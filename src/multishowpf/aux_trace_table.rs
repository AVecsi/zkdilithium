use winter_utils::{uninit_vector};
use winterfell::{
    math::{FieldElement, StarkField}, matrix::ColMatrix, EvaluationFrame, Trace, TraceInfo
};
use crate::multishowpf::{C_TRIT_IND, HASH_CYCLE_LEN, QW_IND, W_IND, Z_IND};

use super::{AUX_WIDTH, PIT_START, PIT_END};

pub const CAUX: usize = 0;
pub const ZAUX: usize = CAUX + 1;
pub const WAUX: usize = ZAUX + 4;
pub const QWAUX: usize = WAUX + 4;
pub const GAMMA: usize = QWAUX + 4;
pub const POLYMULTASSERT: usize = GAMMA + 1;

#[derive(Debug)]
pub struct RapTraceTable<B: StarkField> {
    info: TraceInfo,
    trace: ColMatrix<B>
}

impl<B: StarkField> RapTraceTable<B> {
    pub fn new(width: usize, length: usize) -> Self {
        Self::with_meta(width, length, vec![])
    }

    pub fn with_meta(width: usize, length: usize, meta: Vec<u8>) -> Self {
        assert!(
            width > 0,
            "execution trace must consist of at least one column"
        );
        assert!(
            width <= TraceInfo::MAX_TRACE_WIDTH,
            "execution trace width cannot be greater than {}, but was {}",
            TraceInfo::MAX_TRACE_WIDTH,
            width
        );
        assert!(
            length >= TraceInfo::MIN_TRACE_LENGTH,
            "execution trace must be at least {} steps long, but was {}",
            TraceInfo::MIN_TRACE_LENGTH,
            length
        );
        assert!(
            length.is_power_of_two(),
            "execution trace length must be a power of 2"
        );
        assert!(
            length.ilog2() as u32 <= B::TWO_ADICITY,
            "execution trace length cannot exceed 2^{} steps, but was 2^{}",
            B::TWO_ADICITY,
            length.ilog2()
        );
        assert!(
            meta.len() <= TraceInfo::MAX_META_LENGTH,
            "number of metadata bytes cannot be greater than {}, but was {}",
            TraceInfo::MAX_META_LENGTH,
            meta.len()
        );

        let columns = unsafe { (0..width).map(|_| uninit_vector(length)).collect() };
        Self {
            info: TraceInfo::new_multi_segment(width, AUX_WIDTH, 1, length, meta),
            trace: ColMatrix::new(columns),
        }
    }

    // DATA MUTATORS
    // --------------------------------------------------------------------------------------------
    pub fn fill<I, U>(&mut self, init: I, update: U)
    where
        I: Fn(&mut [B]),
        U: Fn(usize, &mut [B]),
    {
        let mut state = vec![B::ZERO; self.main_trace_width()];
        init(&mut state);
        self.update_row(0, &state);

        for i in 0..self.length() - 1 {
            update(i, &mut state);
            self.update_row(i + 1, &state);
        }
    }

    /// Updates a single row in the execution trace with provided data.
    pub fn update_row(&mut self, step: usize, state: &[B]) {
        self.trace.update_row(step, state);
    }

    // PUBLIC ACCESSORS
    // --------------------------------------------------------------------------------------------

    /// Returns the number of columns in this execution trace.
    pub fn width(&self) -> usize {
        self.main_trace_width()
    }

    /// Returns value of the cell in the specified column at the specified row of this trace.
    #[allow(unused)]
    pub fn get(&self, column: usize, step: usize) -> B {
        self.trace.get(column, step)
    }

    /// Reads a single row from this execution trace into the provided target.
    pub fn read_row_into(&self, step: usize, target: &mut [B]) {
        self.trace.read_row_into(step, target);
    }
}

// TRACE TRAIT IMPLEMENTATION
// ================================================================================================

impl<B: StarkField> Trace for RapTraceTable<B> {
    type BaseField = B;

    fn info(&self) -> &TraceInfo {
        &self.info
    }

    fn length(&self) -> usize {
        self.trace.num_rows()
    }

    fn read_main_frame(&self, row_idx: usize, frame: &mut EvaluationFrame<Self::BaseField>) {
        let next_row_idx = (row_idx + 1) % self.length();
        self.trace.read_row_into(row_idx, frame.current_mut());
        self.trace.read_row_into(next_row_idx, frame.next_mut());
    }

    fn main_segment(&self) -> &ColMatrix<B> {
        &self.trace
    }
}
