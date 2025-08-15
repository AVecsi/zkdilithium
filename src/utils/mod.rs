use winterfell::{
    math::{FieldElement},
};

pub mod poseidon_23_spec;

// CONSTRAINT EVALUATION HELPERS
// ================================================================================================

/// Returns zero only when a == b.
pub fn are_equal<E: FieldElement>(a: E, b: E) -> E {
    a - b
}

/// Returns zero only when a = zero || a == one.
pub fn is_binary<E: FieldElement>(a: E) -> E {
    a * a - a
}

/// Returns zero iff `a` is 0, 1, or -1. Nonzero otherwise.
pub fn is_ternary_challenge<E: FieldElement>(a: E) -> E {
    a * (a - E::ONE) * (a + E::ONE)
}

// Returns zero iff `a` is 0, 1, or 2. Nonzero otherwise.
pub fn is_ternary<E: FieldElement>(a: E) -> E {
    a * (a - E::ONE) * (a - E::from(2 as u32))
}

// TRAIT TO SIMPLIFY CONSTRAINT AGGREGATION
// ================================================================================================

pub trait EvaluationResult<E> {
    fn agg_constraint(&mut self, index: usize, flag: E, value: E);
}

impl<E: FieldElement> EvaluationResult<E> for [E] {
    fn agg_constraint(&mut self, index: usize, flag: E, value: E) {
        self[index] += flag * value;
    }
}

impl<E: FieldElement> EvaluationResult<E> for Vec<E> {
    fn agg_constraint(&mut self, index: usize, flag: E, value: E) {
        self[index] += flag * value;
    }
}