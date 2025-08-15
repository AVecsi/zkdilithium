// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use std::os::macos::raw::stat;

use winter_utils::uninit_vector;
use winterfell::{
    crypto::{hashers::Blake3_256, DefaultRandomCoin, MerkleTree}, matrix::ColMatrix, AuxRandElements, CompositionPoly, CompositionPolyTrace, ConstraintCompositionCoefficients, DefaultConstraintCommitment, DefaultConstraintEvaluator, DefaultTraceLde, PartitionOptions, StarkDomain, Trace, TraceInfo, TracePolyTable, TraceTable
};

use crate::{multishowpf::{aux_trace_table::{RapTraceTable, CAUX, GAMMA, QWAUX, WAUX, ZAUX}, AUX_WIDTH, BETA, COM_END, COM_START, CTILDE_IND, C_IND, C_SIZE, C_TRIT_IND, FE_TRIT_SIZE, GAMMA2, HASH_IND, HTR, K, M, M_IND, N, PADDED_TRACE_LENGTH, PIT_END, PIT_LEN, PIT_START, QW_IND, Q_IND, Q_RANGE, Q_RANGE_IND, R_IND, R_RANGE, R_RANGE_IND, SIGN_IND, SWAP_C_TRIT, SWAP_DEC_FE_IND, SWAP_DEC_TRIT_IND, SWAP_FE_EQUAL_IND, S_BALL_END, S_BALL_START, TAU, W_BIND, W_HIGH_IND, W_HIGH_RANGE, W_HIGH_RANGE_IND, W_HIGH_SHIFT, W_IND, W_LOW_IND, W_LOW_LIMIT, W_LOW_RANGE, W_LOW_RANGE_IND, Z_IND, Z_LIMIT, Z_RANGE, Z_RANGE_IND, _TRACE_LENGTH}, utils::poseidon_23_spec};

use super::{
    BaseElement, ThinDilMulShowAir, FieldElement, ProofOptions, Prover, TRACE_WIDTH, air::PublicInputs,
    HASH_CYCLE_LEN, HASH_STATE_WIDTH, HASH_RATE_WIDTH, NUM_HASH_ROUNDS, HASH_DIGEST_WIDTH};

// MULTI-SHOW zkDILITHIUM PROVER
// ================================================================================================

pub struct ThinDilMulShowProver {
    options: ProofOptions,
    z: [[BaseElement; N]; K],
    w: [[BaseElement; N]; K],
    qw: [[BaseElement; N]; K],
    ctilde: [BaseElement; HASH_DIGEST_WIDTH],
    m: [BaseElement; 12],
    comm: [BaseElement; HASH_RATE_WIDTH],
    com_r: [BaseElement; 12],
    nonce: [BaseElement; 12]
}

impl ThinDilMulShowProver {
    pub fn new(options: ProofOptions, z: [[BaseElement; N]; K], w: [[BaseElement; N]; K],  qw: [[BaseElement; N]; K], ctilde: [BaseElement; HASH_DIGEST_WIDTH], m: [BaseElement; 12], comm: [BaseElement; HASH_RATE_WIDTH], com_r: [BaseElement; 12], nonce: [BaseElement; 12]) -> Self {
        Self {options, z, w, qw, ctilde, m, comm, com_r, nonce}
    }

    /// Builds an execution trace for computing a Fibonacci sequence of the specified length such
    /// that each row advances the sequence by 2 terms.
    pub fn build_trace(&self) -> RapTraceTable<BaseElement> {

        let mut trace = RapTraceTable::new(TRACE_WIDTH, PADDED_TRACE_LENGTH);
        trace.fill(
            |state| {

                // ctilde
                for i in 0..HASH_DIGEST_WIDTH {
                    state[CTILDE_IND+i] = self.ctilde[i];
                }

                // message
                for i in 0..self.m.len() {
                    state[M_IND + i] = self.m[i];
                }

                // message nonce
                for i in 0..HASH_DIGEST_WIDTH{
                    state[HASH_IND + i] =  state[M_IND + i];
                    state[HASH_IND + HASH_DIGEST_WIDTH + i] = self.nonce[i];
                }
            },
            |step, state| {
                let cycle_pos = step % HASH_CYCLE_LEN;
                let _cycle_num = step / HASH_CYCLE_LEN;

                let base: u32 = (N-TAU + step-(HASH_CYCLE_LEN)-S_BALL_START) as u32;
                
                // apply poseidon round in all but the last round of HASH_CYCLE
                if cycle_pos < NUM_HASH_ROUNDS {
                    poseidon_23_spec::apply_round(&mut state[HASH_IND..(HASH_IND + 3*HASH_STATE_WIDTH)], step);
                }

                //Set up the trace for sample in ball
                if step == S_BALL_START - 1 {
                    state[HASH_IND] = BaseElement::from(2u32);
                    for i in 0..HASH_DIGEST_WIDTH{
                        state[HASH_IND + i + 1] = state[CTILDE_IND + i];
                    }

                    for i in HASH_DIGEST_WIDTH+1..(3*HASH_STATE_WIDTH) {
                        state[HASH_IND + i] = BaseElement::ZERO;
                    }
                }

                // Ballsample section
                if step < (HASH_CYCLE_LEN)*(S_BALL_END)-1 && step > S_BALL_START - 1{
                    // Hashing to compute randomness used in BallSample
                    if cycle_pos == NUM_HASH_ROUNDS {
                        // Computing random value % basei where basei runs from N-TAU..N and storing in RIND, QIND
                        for i in 0..HASH_CYCLE_LEN{
                            let x = state[HASH_IND+i].to_string().parse::<u32>().unwrap();
                            
                            let basei = base + (i+1) as u32;
                            
                            state[Q_IND+i] = BaseElement::new(x/basei);
                            state[R_IND+i] = BaseElement::new(x%basei);    
                        }

                        // Extracting bits for sign flips
                        bitdec(
                            state[HASH_IND+HASH_CYCLE_LEN].to_string().parse::<u64>().unwrap() % 2u64.pow(HASH_CYCLE_LEN as u32),
                            &mut state[SIGN_IND..SIGN_IND + HASH_CYCLE_LEN] 
                        );

                        // Below is needed because rotate_left happens at every step and we don't want to do it whenever hashing is complete
                        state[Q_IND..Q_IND+HASH_CYCLE_LEN].rotate_right(1);
                        state[R_IND..R_IND+HASH_CYCLE_LEN].rotate_right(1);
                        state[SIGN_IND..SIGN_IND+HASH_CYCLE_LEN].rotate_right(1);
                    }

                    // Starts at the end of first round of hashing above. Then we start swapping and negation
                    if step >= S_BALL_START + HASH_CYCLE_LEN-1 {
                        // The base goes from 216 to 255
                        state[Q_IND..Q_IND+HASH_CYCLE_LEN].rotate_left(1);
                        state[R_IND..R_IND+HASH_CYCLE_LEN].rotate_left(1);
                        state[SIGN_IND..SIGN_IND+HASH_CYCLE_LEN].rotate_left(1);

                        bitdec(state[Q_IND].to_string().parse::<u64>().unwrap(), &mut state[Q_RANGE_IND..(Q_RANGE_IND+Q_RANGE)]);
                        bitdec(state[R_IND].to_string().parse::<u64>().unwrap(), &mut state[R_RANGE_IND..(R_RANGE_IND+R_RANGE)]);
    
                        bitdec((M/(base+1)) as u64, &mut state[Q_RANGE_IND+Q_RANGE..(Q_RANGE_IND+2*Q_RANGE)]);
                        bitdec(256 - (base+1) as u64, &mut state[R_RANGE_IND+R_RANGE..(R_RANGE_IND+2*R_RANGE)]);

                        let sel = state[R_IND];

                        //i
                        let base_fe_q = base / 11;
                        let base_fe_r = (base % 11);

                        //j
                        let sel_fe_q = sel.to_string().parse::<usize>().unwrap() / 11;
                        let sel_fe_r = (sel.to_string().parse::<usize>().unwrap() % 11);

                        //Set up the swapped challenge field element decomposed to trits
                        trit_dec(state[C_IND + sel_fe_q].to_string().parse::<u64>().unwrap(), &mut state[SWAP_C_TRIT..(SWAP_C_TRIT + FE_TRIT_SIZE)]);

                        // Hashing ctilde to ball
                        // Swapping and negating entries of c as described in Dilithium.v3

                        state[C_IND + base_fe_q as usize] += BaseElement::from(4u64.pow(base_fe_r))*state[SWAP_C_TRIT + sel_fe_r];

                        state[C_IND + sel_fe_q] -= BaseElement::from(4u64.pow(sel_fe_r as u32))*state[SWAP_C_TRIT + sel_fe_r];
                        state[C_IND + sel_fe_q] += BaseElement::from(4u64.pow(sel_fe_r as u32)*(state[SIGN_IND].to_string().parse::<u64>().unwrap() + 1));

                        // Resetting the SWAPDEC registers to 0
                        for i in 0..C_SIZE{
                            state[SWAP_DEC_FE_IND+i] = BaseElement::ZERO;
                        }
                        state[SWAP_DEC_FE_IND + sel_fe_q] = BaseElement::ONE;

                        for i in 0..FE_TRIT_SIZE{
                            state[SWAP_DEC_TRIT_IND+i] = BaseElement::ZERO;
                        }
                        state[SWAP_DEC_TRIT_IND + sel_fe_r] = BaseElement::ONE;

                        // Setting the equality element for the FE of i and j
                        if sel_fe_q as u32 == base_fe_q {
                            state[SWAP_FE_EQUAL_IND] = BaseElement::ONE;
                        } else {
                            state[SWAP_FE_EQUAL_IND] = BaseElement::ZERO;
                        }
                    }
                }

                // Opening a hash-based commitment -- signature on com = H(m||com_r)
                // the constraints will be enforced as follows
                // assert that the last HASH_STATE_WIDTH-HASH_RATE_WIDTH registers match H(rho||t)
                // assert that the first 12 registers are H(rho||t) + m
                // the next 12 registers dont need any constraints as the prover is allowed to choose any com_r
                if step == COM_START - 1 {
                    // insert m and com_r
                    // m and com_r are each 12 field elements perfectly filling up HASH_RATE_WIDTH
                    for j in 0..HASH_STATE_WIDTH {
                        state[HASH_IND + j] = BaseElement::from(HTR[j]);
                    }

                    for j in 0..12 {
                        state[HASH_IND + j] += self.m[j];
                        state[HASH_IND + 12 + j] += self.com_r[j];
                    }
                }

                if step == COM_END - 1 {
                    // Reset HASH_STATE-HAS_RATE to 0 and leave mu=H(HTR||com(m;com_r)) in HASH_RATE
                    for j in HASH_RATE_WIDTH..HASH_STATE_WIDTH{
                        state[HASH_IND + j] = BaseElement::ZERO;
                    }
                }

                // PIT section                
                let zlimitf = BaseElement::from(Z_LIMIT);
                let wlowlimitf = BaseElement::from(W_LOW_LIMIT);
                let whighshiftf = BaseElement::from(W_HIGH_SHIFT);
                let betaf = BaseElement::from(BETA);
                if step == PIT_START - 1 {
                    // Reset HASH_STATE to 0
                    for j in HASH_STATE_WIDTH..3*HASH_STATE_WIDTH{
                        state[HASH_IND + j] = BaseElement::ZERO;
                    }

                    //decompose the first challenge FE
                    challenge_trit_dec(state[C_IND].to_string().parse::<u64>().unwrap(), &mut state[C_TRIT_IND..C_TRIT_IND + FE_TRIT_SIZE]);
                }

                if step >= PIT_START-1 {
                    // Helper variables
                    let poly_cycle = (step + 1 - PIT_START) / HASH_CYCLE_LEN;
                    let polycycle_pos = (step + 1 - PIT_START) % HASH_CYCLE_LEN;

                    // Inserting Z, W and QW polynomials in the first 6 rows of each HASH_CYCLE
                    // edge_case: Note that each HASH_CYCLE consumes 24 coefficients but N*K % 24 = 16
                    // hence in the last HASH_CYCLE we need to pad with 8 zero elements
                    if step < PIT_START - 1 + PIT_LEN - 4 {
                        if polycycle_pos < HASH_CYCLE_LEN - 2{
                            let poly_ind = poly_cycle*(HASH_CYCLE_LEN - 2) + polycycle_pos;
                            for j in 0..K{
                                state[Z_IND+j] = self.z[j][poly_ind];
                                state[QW_IND+j] = self.qw[j][poly_ind];
                                state[W_IND+j] = self.w[j][poly_ind];
                            }
                        }

                        // Populating WHIGH with HASH_RATE_WIDTH entries at the end of every cycle
                        // these will be rotated to ensure the same values are used in decomposition check are hashed
                        if polycycle_pos == 0 {
                            // Check if it's the last cycle
                            let jj_end: usize = if poly_cycle == N/(HASH_CYCLE_LEN-2) {HASH_RATE_WIDTH/K-2} else {HASH_RATE_WIDTH/K};

                            for jj in 0..jj_end {
                                for j in 0..K {
                                    let (_,w1) = wdec(self.w[j][poly_cycle*(HASH_CYCLE_LEN-2) + jj].to_string().parse::<i64>().unwrap());
                                    state[W_HIGH_IND+jj*K+j] = BaseElement::from((w1.rem_euclid((M).into())) as u64);
                                }
                            }

                            // make last 12 entries of WHIGH 0
                            for jj in jj_end..HASH_RATE_WIDTH/K {
                                for j in 0..K {
                                    state[W_HIGH_IND+jj*K+j] = BaseElement::ZERO;
                                }
                            }

                            // Absorb values into sponge
                            for j in 0..HASH_RATE_WIDTH{
                                state[HASH_IND+j] += state[W_HIGH_IND+j];
                            }
                        }
                    }

                    /////////////////////////////////////////////////////////////////////
                    // Post processing after insertion --- bitdec, wdec, rotations, poseidon round
                    
                    // Rotate W and C by 4 and 1 positions to the left respectively at first HASH_CYCLE_LEN-2 rows in each cycle
                    if step >= PIT_START{
                        let hashcycle_pos = (step - PIT_START) % HASH_CYCLE_LEN;

                        if hashcycle_pos < HASH_CYCLE_LEN - 2{                        
                            state[W_HIGH_IND..(W_HIGH_IND+HASH_RATE_WIDTH)].rotate_left(4);

                            //number of rotates done
                            let rotates_done = ((step - PIT_START) / HASH_CYCLE_LEN) * (HASH_CYCLE_LEN - 2) + hashcycle_pos + 1;

                            if rotates_done % FE_TRIT_SIZE == 0 && step > PIT_START {
                                //Rotate the challenge FEs
                                state[C_IND..C_IND + C_SIZE].rotate_left(1);

                                //Decompose the current challenge FE
                                challenge_trit_dec(state[C_IND].to_string().parse::<u64>().unwrap(), &mut state[C_TRIT_IND..C_TRIT_IND + FE_TRIT_SIZE]);
                            } else {
                                //Rotate the challenge trits
                                state[C_TRIT_IND..C_TRIT_IND+11].rotate_left(1);
                            }
                        }
                    } 

                    // Bit decomposition of the FOUR elements in ZIND..ZIND+K
                    for j in 0..K{
                        bitdec(
                            (state[Z_IND+j]+zlimitf).to_string().parse::<u64>().unwrap(),
                            &mut state[Z_RANGE_IND+(2*j)*Z_RANGE..(Z_RANGE_IND+(2*j+1)*Z_RANGE)]
                        );
                        bitdec(
                            (state[Z_IND+j]+zlimitf+betaf).to_string().parse::<u64>().unwrap(),
                            &mut state[Z_RANGE_IND+(2*j+1)*Z_RANGE..(Z_RANGE_IND+(2*j+2)*Z_RANGE)]
                        );
                    }

                    // decompse w into low bits
                    for j in 0..K{
                        let windj = state[W_IND+j].to_string().parse::<i64>().unwrap();
                        let (w0,w1) = wdec(windj);
                        let w2 = if windj== (M as i64-GAMMA2 as i64) {1} else {0};
                        state[W_BIND+j] = BaseElement::from(w2 as u8); // w2 is always a bit
                        state[W_LOW_IND+j] = BaseElement::from((w0.rem_euclid(M.into())) as u64);
                        if w2==1 {
                            println!("{},{},{}", w0,w1,w2);
                        }
                    }
                    
                    // WLOW rangeproof
                    // Since the ranges line up with powers of two we only have one range proof
                    for j in 0..K{
                        bitdec(
                            (state[W_LOW_IND+j]+wlowlimitf).to_string().parse::<u64>().unwrap(),
                            &mut state[W_LOW_RANGE_IND+(j)*W_LOW_RANGE..(W_LOW_RANGE_IND+(j+1)*W_LOW_RANGE)]
                        );
                    } 

                    // WHIGH rangeproof
                    for j in 0..K{
                        bitdec(
                            (state[W_HIGH_IND+j]).to_string().parse::<u64>().unwrap(),
                            &mut state[W_HIGH_RANGE_IND+(2*j)*W_HIGH_RANGE..(W_HIGH_RANGE_IND+(2*j+1)*W_HIGH_RANGE)]
                        );
                        bitdec(
                            (state[W_HIGH_IND+j]+whighshiftf).to_string().parse::<u64>().unwrap(),
                            &mut state[W_HIGH_RANGE_IND+(2*j+1)*W_HIGH_RANGE..(W_HIGH_RANGE_IND+(2*j+2)*W_HIGH_RANGE)]
                        );
                    }
                    /////////////////////////////////////////////////////////////////////////////////   
                }

                // Artifact of winterfell. Used to prevent constant polynomial when interpolating
                if step==PADDED_TRACE_LENGTH-2 {
                    for i in 0..TRACE_WIDTH{
                        state[i] = BaseElement::new(123 as u32);
                    }
                }
            },
        );

        trace
    }
}

impl Prover for ThinDilMulShowProver {
    type BaseField = BaseElement;
    type Air = ThinDilMulShowAir;
    type Trace = RapTraceTable<BaseElement>;

   fn get_pub_inputs(&self, _trace: &Self::Trace) -> PublicInputs {
       PublicInputs{comm: self.comm, nonce: self.nonce}
    }
    fn options(&self) -> &ProofOptions {
        &self.options
    }
    
    type HashFn = Blake3_256<BaseElement>;
    
    type VC = MerkleTree<Blake3_256<BaseElement>>;
    
    type RandomCoin = DefaultRandomCoin<Self::HashFn>;

    type TraceLde<E: FieldElement<BaseField = Self::BaseField>> =
        DefaultTraceLde<E, Self::HashFn, Self::VC>;

    type ConstraintEvaluator<'a, E: FieldElement<BaseField = Self::BaseField>> =
        DefaultConstraintEvaluator<'a, Self::Air, E>;
    
    type ConstraintCommitment<E: FieldElement<BaseField = Self::BaseField>> =
        DefaultConstraintCommitment<E, Blake3_256<BaseElement>, Self::VC>;
    
    fn new_trace_lde<E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        trace_info: &TraceInfo,
        main_trace: &ColMatrix<Self::BaseField>,
        domain: &StarkDomain<Self::BaseField>,
        partition_option: PartitionOptions,
    ) -> (Self::TraceLde<E>, TracePolyTable<E>) {
        DefaultTraceLde::new(trace_info, main_trace, domain, partition_option)
    }
    
    fn new_evaluator<'a, E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        air: &'a Self::Air,
        aux_rand_elements: Option<AuxRandElements<E>>,
        composition_coefficients: ConstraintCompositionCoefficients<E>,
    ) -> Self::ConstraintEvaluator<'a, E> {
        DefaultConstraintEvaluator::new(air, aux_rand_elements, composition_coefficients)
    }

    fn build_constraint_commitment<E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        composition_poly_trace: CompositionPolyTrace<E>,
        num_constraint_composition_columns: usize,
        domain: &StarkDomain<Self::BaseField>,
        partition_options: PartitionOptions,
    ) -> (Self::ConstraintCommitment<E>, CompositionPoly<E>) {
        DefaultConstraintCommitment::new(
            composition_poly_trace,
            num_constraint_composition_columns,
            domain,
            partition_options,
        )
    }

    fn build_aux_trace<E>(
        &self,
        trace: &Self::Trace,
        aux_rand_elements: &AuxRandElements<E>,
    ) -> ColMatrix<E>
    where
        E: FieldElement<BaseField = Self::BaseField>,
    {
        let main_trace = trace.main_segment();
        let rand_elements = aux_rand_elements.rand_elements();

        let mut current_row = unsafe { uninit_vector(main_trace.num_cols()) };
        // let mut next_row = unsafe { uninit_vector(self.width()) };
        main_trace.read_row_into(0, &mut current_row);
        let mut aux_columns = vec![vec![E::ZERO; main_trace.num_rows()]; trace.aux_trace_width()];
        
        for i in 0..AUX_WIDTH{
            aux_columns[i][PIT_START] = E::ZERO;
        }
        aux_columns[GAMMA][PIT_START] = E::ONE;
        
        let mut gamma1 = E::ONE;

        for step in PIT_START..PIT_END {
            let matmul_step = step-PIT_START;
            let matmul_pos = (matmul_step) % HASH_CYCLE_LEN;

            main_trace.read_row_into(step, &mut current_row);
            
            if matmul_pos < HASH_CYCLE_LEN - 2{
                // C eval
                aux_columns[CAUX][step+1] = aux_columns[CAUX][step] + gamma1*current_row[C_TRIT_IND].into();
                
                // Z eval
                for i in 0..4{
                    aux_columns[ZAUX+i][step+1] = aux_columns[ZAUX+i][step] + gamma1*current_row[Z_IND+i].into();
                }

                // W eval
                for i in 0..4{
                    aux_columns[WAUX+i][step+1] = aux_columns[WAUX+i][step] + gamma1*current_row[W_IND+i].into();
                }

                // QW eval
                for i in 0..4{
                    aux_columns[QWAUX+i][step+1] = aux_columns[QWAUX+i][step] + gamma1*current_row[QW_IND+i].into();
                }

                // Maintain a column of powers of gamma1
                gamma1 *= rand_elements[0];
                aux_columns[GAMMA][step+1] = gamma1;
            } else {
                // Do nothing and simply copy values
                for i in 0..AUX_WIDTH {
                    aux_columns[i][step+1] = aux_columns[i][step];
                }
            }
            
        }

        ColMatrix::new(aux_columns)
    }
}

fn bitdec(mut x: u64, bits: &mut [BaseElement]) {
    let mut b;
    
    // Assertion checking that length of bits is large enough to decompose x
    debug_assert!((x as f32).log2() <= bits.len() as f32, "Value: {} did not fit in {} bits", x, bits.len());
    
    // Placing the bits of x into the bits array in little endian form
    for i in 0..bits.len() {
        b = x % 2;
        bits[i] = BaseElement::new(b as u32);
        x = x/2;
    }
}

fn trit_dec(mut x: u64, trits: &mut [BaseElement]) {
    let mut t;

    // Assertion checking that length of bits is large enough to decompose x
    debug_assert!((x as f32).log2()/2.0 <= trits.len() as f32, "Value: {} did not fit in {} bits", x, trits.len());

    // Placing the bits of x into the bits array in little endian form
    for i in 0..trits.len() {
        t = x % 4;
        trits[i] = BaseElement::new(t as u32);
        x = x/4;
    }
}

// This decomposes to -1 0 1 trits
fn challenge_trit_dec(mut x: u64, trits: &mut [BaseElement]) {
    let mut t;

    // Assertion checking that length of bits is large enough to decompose x
    debug_assert!((x as f32).log2()/2.0 <= trits.len() as f32, "Value: {} did not fit in {} bits", x, trits.len());

    // Placing the bits of x into the bits array in little endian form
    for i in 0..trits.len() {
        t = BaseElement::new((x % 4) as u32);
        trits[i] = (BaseElement::from(5u32) * t - (BaseElement::from(3u32) * t * t)) * BaseElement::from(3670017u32);
        x = x/4;
    }
}

// decomposes elements into high and low bits
fn wdec(x: i64) -> (i64, i64) {
    let gamma2: i64 = GAMMA2 as i64;
    let mut x0: i64 = x % (2*gamma2);
    
    if x0 > gamma2 {
        x0 -= 2*gamma2;
    }
    if (x -x0) == ((M-1) as i64){
        return (x0-1,0)
    }

    return (x0, (x as i64-x0)/(2*gamma2))
}