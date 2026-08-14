use crate::field::BaseElement;
use crate::utils::poseidon_constants::{ARK, INV_MDS, MDS};
use crate::utils::{are_equal, EvaluationResult};
use winter_utils::{ByteReader, ByteWriter, Deserializable, DeserializationError, Serializable};
use winterfell::{
    crypto::{Digest, Hasher},
    math::FieldElement,
};

pub const STATE_WIDTH: usize = 35;
pub const RATE_WIDTH: usize = 24;
// pub const CAPACITY_WIDTH: usize = STATE_WIDTH-RATE_WIDTH;

/// 12 elements (can be serialized into 32-bytes) are returned as digest.
pub const DIGEST_SIZE: usize = 12;

/// Number of full rounds we use is actually 21 with 3 permutations applied per row of the trace table
pub const NUM_ROUNDS: usize = 7;

pub const CYCLE_LENGTH: usize = 8;

// TYPES AND INTERFACES
// ================================================================================================

pub struct Poseidon23 {
    state: [BaseElement; STATE_WIDTH],
    idx: usize,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Default)]
pub struct Hash([BaseElement; DIGEST_SIZE]);

// Poseidon23 IMPLEMENTATION
// ================================================================================================

impl Poseidon23 {
    /// Returns a new hasher with the state initialized to all zeros.
    #[allow(clippy::new_without_default)]
    #[allow(dead_code)]
    pub fn new() -> Self {
        Poseidon23 {
            state: [BaseElement::ZERO; STATE_WIDTH],
            idx: 0,
        }
    }

    /// Absorbs data into the hasher state.
    #[allow(dead_code)]
    pub fn update(&mut self, data: &[BaseElement]) {
        for &element in data {
            self.state[self.idx] += element;
            self.idx += 1;
            if self.idx % RATE_WIDTH == 0 {
                apply_permutation(&mut self.state);
                self.idx = 0;
            }
        }
    }

    /// Returns hash of the data absorbed into the hasher.
    #[allow(dead_code)]
    pub fn finalize(mut self) -> Hash {
        if self.idx > 0 {
            apply_permutation(&mut self.state);
        }
        let mut out: [BaseElement; DIGEST_SIZE] = [BaseElement::ZERO; DIGEST_SIZE];
        for i in 0..DIGEST_SIZE{
            out[i] = self.state[i];
        }
        Hash(out)
    }

    /// Returns hash of the provided data.
    pub fn digest(data: &[BaseElement]) -> Hash {
        // initialize state to all zeros
        let mut state = [BaseElement::ZERO; STATE_WIDTH];

        let mut i = 0;
        for &element in data.iter() {
            state[i] += element;
            i += 1;
            if i % RATE_WIDTH == 0 {
                apply_permutation(&mut state);
                i = 0;
            }
        }

        if i > 0 {
            apply_permutation(&mut state);
        }

        let mut out: [BaseElement; DIGEST_SIZE] = [BaseElement::ZERO; DIGEST_SIZE];
        for i in 0..DIGEST_SIZE{
            out[i] = state[i];
        }
        
        Hash(out)
    }
}

// HASHER IMPLEMENTATION
// ================================================================================================

impl Hasher for Poseidon23 {
    type Digest = Hash;

    const COLLISION_RESISTANCE: u32 = 128;

    fn hash(_bytes: &[u8]) -> Self::Digest {
        unimplemented!("not implemented")
    }

    fn merge(values: &[Self::Digest; 2]) -> Self::Digest {
        Self::digest(Hash::hashes_as_elements(values))
    }

    fn merge_many(_values: &[Self::Digest]) -> Self::Digest {
        unimplemented!("not implemented")
    }

    fn merge_with_int(_seed: Self::Digest, _value: u64) -> Self::Digest {
        unimplemented!("not implemented")
    }
}

// HASH IMPLEMENTATION
// ================================================================================================

impl Hash {
    #[allow(dead_code)]
    pub fn new(v: [BaseElement; DIGEST_SIZE]) -> Self {
        Hash(v)
    }

    #[allow(dead_code)]
    #[allow(clippy::wrong_self_convention)]
    pub fn to_bytes(&self) -> [u8; 32] {
        unimplemented!()
    }

    #[allow(dead_code)]
    #[allow(clippy::wrong_self_convention)]
    pub fn to_elements(&self) -> [BaseElement; DIGEST_SIZE] {
        unimplemented!()
    }

    pub fn hashes_as_elements(_hashes: &[Hash]) -> &[BaseElement] {
        unimplemented!()
    }
}

impl Digest for Hash {
    fn as_bytes(&self) -> [u8; 32] {
        let bytes = BaseElement::elements_as_bytes(&self.0);
        let mut result = [0; 32];
        result[..bytes.len()].copy_from_slice(bytes);
        result
    }
}

impl Serializable for Hash {
    fn write_into<W: ByteWriter>(&self, target: &mut W) {
        for i in 0..DIGEST_SIZE{
             target.write(self.0[i]);
        }
    }
}

impl Deserializable for Hash {
    fn read_from<R: ByteReader>(source: &mut R) -> Result<Self, DeserializationError> {
        let mut v: [BaseElement; DIGEST_SIZE] = [BaseElement::ZERO; DIGEST_SIZE];
        for i in 0..DIGEST_SIZE{
            v[i] = BaseElement::read_from(source)?;
        }

        Ok(Self(v))
    }
}

// Poseidon PERMUTATION
// ================================================================================================

pub fn apply_permutation(state: &mut [BaseElement; STATE_WIDTH]) {
    for i in 0..NUM_ROUNDS {
        apply_round(state, i);
    }
}

#[inline(always)]
pub fn apply_round(state: &mut [BaseElement], step: usize) {
    // determine which round constants to use
    let ark = ARK[step % CYCLE_LENGTH];

    for i in 0..STATE_WIDTH {
        state[2*STATE_WIDTH+i] = state[i] + ark[i];
    }
    apply_sbox(&mut state[2*STATE_WIDTH..3*STATE_WIDTH]);
    apply_mds(&mut state[2*STATE_WIDTH..3*STATE_WIDTH]);

    for i in 0..STATE_WIDTH {
        state[STATE_WIDTH+i] = state[2*STATE_WIDTH+i] + ark[STATE_WIDTH+i];
    }
    apply_sbox(&mut state[STATE_WIDTH..2*STATE_WIDTH]);
    apply_mds(&mut state[STATE_WIDTH..2*STATE_WIDTH]);

    for i in 0..STATE_WIDTH {
        state[i] = state[STATE_WIDTH+i] + ark[2*STATE_WIDTH+i];
    }
    apply_sbox(&mut state[0..STATE_WIDTH]);
    apply_mds(&mut state[0..STATE_WIDTH]);
}

// CONSTRAINTS
// ================================================================================================

/// when flag = 1, enforces constraints for a single round of Poseidon
pub fn enforce_round<E: FieldElement + From<BaseElement>>(
    result: &mut [E],
    current: &[E],
    next: &[E],
    ark: &[E],
    flag: E,
) {
    // compute the state that should result from applying Poseidon permutation upto the sbox
    let mut step1 = [E::ZERO; STATE_WIDTH];
    for i in 0..STATE_WIDTH {
        step1[i] = current[i] + ark[i];
    }
    
    // compute the state that should result from applying the inverse for Poseidon permutation upto the sbox
    let mut step2 = [E::ZERO; STATE_WIDTH];
    step2.copy_from_slice(next);
    apply_inv_mds(&mut step2);

    // make sure that the results inverses of each other
    for i in 0..STATE_WIDTH {
        result.agg_constraint(i, flag, 
            are_equal(step1[i]*(step2[i]*step1[i] - E::ONE), E::ZERO));
        result.agg_constraint(i+STATE_WIDTH, flag, 
            are_equal(step2[i]*(step2[i]*step1[i] - E::ONE), E::ZERO));
    }
}

// ROUND CONSTANTS
// ================================================================================================

/// Returns Poseidon round constants arranged in column-major form.
pub fn get_round_constants() -> Vec<Vec<BaseElement>> {
    let mut constants = Vec::new();
    for _ in 0..(STATE_WIDTH * 3) {
        constants.push(vec![BaseElement::ZERO; CYCLE_LENGTH]);
    }

    #[allow(clippy::needless_range_loop)]
    for i in 0..CYCLE_LENGTH-1 {
        for j in 0..STATE_WIDTH*3 {
            constants[j][i] = ARK[i][j];
        }
    }

    constants
}

// 
// TESTING
// ================================================================================================

#[allow(unused)]
fn print_field_slice(v: &[BaseElement]){
    print!("[");
    for i in 0..STATE_WIDTH{
        print!("{}, ", v[i]);
    }
    println!("]");
}

// HELPER FUNCTIONS
// ================================================================================================

#[inline(always)]
#[allow(clippy::needless_range_loop)]
fn apply_sbox<E: FieldElement>(state: &mut [E]) {
    for i in 0..STATE_WIDTH {
        state[i] = state[i].inv();
    }
}

#[inline(always)]
#[allow(clippy::needless_range_loop)]
fn apply_mds<E: FieldElement + From<BaseElement>>(state: &mut [E]) {
    let mut result = [E::ZERO; STATE_WIDTH];
    let mut temp;
    
    for i in 0..STATE_WIDTH {
        temp = E::ZERO;
        for j in 0..STATE_WIDTH {
            temp = temp+E::from(MDS[i * STATE_WIDTH + j]) * state[j];
        }
        result[i] = temp;
    }
    state.copy_from_slice(&result);
}

#[inline(always)]
#[allow(clippy::needless_range_loop)]
fn apply_inv_mds<E: FieldElement + From<BaseElement>>(state: &mut [E]) {
    let mut result = [E::ZERO; STATE_WIDTH];
    let mut temp;
    
    for i in 0..STATE_WIDTH {
        temp = E::ZERO;
        for j in 0..STATE_WIDTH {
            temp = temp+E::from(INV_MDS[i * STATE_WIDTH + j]) * state[j];
        }
        result[i] = temp;
    }
    state.copy_from_slice(&result);
}
