use atomic_refcell::AtomicRefCell;
use winter_utils::SliceReader;
use winterfell::{
    math::ToElements, Air, AirContext, Assertion, EvaluationFrame, TraceInfo, TransitionConstraintDegree
};

use super::{BaseElement, FieldElement, ProofOptions, TRACE_WIDTH, HASH_CYCLE_LEN, aux_trace_table::{GAMMA, CAUX, ZAUX, WAUX, QWAUX, POLYMULTASSERT}};
use crate::{starkpf::{AUX_WIDTH, BETA, COM_END, COM_START, CTILDE_ASSERT, CTILDE_IND, C_IND, C_SIZE, C_TRIT_ASSERT, C_TRIT_IND, FE_TRIT_SIZE, GAMMA2, HASH_IND, HTR, K, M, N, PADDED_TRACE_LENGTH, PIT_END, PIT_LEN, PIT_START, PUBA, PUBT, QR_ASSERT, QW_IND, Q_ASSERT, Q_IND, Q_RANGE, Q_RANGE_IND, R_ASSERT, R_IND, R_RANGE, R_RANGE_IND, SET_ASSERT, SIGN_IND, SWAP_ASSERT, SWAP_C_DEC_ASSERT, SWAP_C_TRIT, SWAP_DEC_ASSERT, SWAP_DEC_FE_ASSERT, SWAP_DEC_FE_IND, SWAP_DEC_TRIT_ASSERT, SWAP_DEC_TRIT_IND, SWAP_FE_EQUAL_IND, S_BALL_END, TAU, W_BIND, W_DEC_ASSERT, W_HIGH_ASSERT, W_HIGH_IND, W_HIGH_RANGE, W_HIGH_RANGE_IND, W_HIGH_SHIFT, W_IND, W_LOW_ASSERT, W_LOW_IND, W_LOW_LIMIT, W_LOW_RANGE, W_LOW_RANGE_IND, Z_ASSERT, Z_IND, Z_LIMIT, Z_RANGE, Z_RANGE_IND}, utils::{are_equal, is_binary, is_ternary, is_ternary_challenge, poseidon_23_spec::{self, DIGEST_SIZE as HASH_DIGEST_WIDTH, RATE_WIDTH as HASH_RATE_WIDTH, STATE_WIDTH as HASH_STATE_WIDTH}, EvaluationResult}};

// DILITHIUM AIR
// ================================================================================================

const HASH_CYCLE_MASK: [BaseElement; HASH_CYCLE_LEN] = [
    BaseElement::ONE,
    BaseElement::ONE,
    BaseElement::ONE,
    BaseElement::ONE,
    BaseElement::ONE,
    BaseElement::ONE,
    BaseElement::ONE,
    BaseElement::ZERO,
];

pub struct PublicInputs {
    pub m: [BaseElement; HASH_DIGEST_WIDTH]
}

impl ToElements<BaseElement> for PublicInputs {
    fn to_elements(&self) -> Vec<BaseElement> {
        self.m.to_vec()
    }
}

pub struct ThinDilAir {
    context: AirContext<BaseElement>,
    cache: AtomicRefCell<Vec<u8>>,
    m: [BaseElement; HASH_DIGEST_WIDTH]
}

impl Air for ThinDilAir {
    type BaseField = BaseElement;
    type PublicInputs = PublicInputs;

    // CONSTRUCTOR
    // --------------------------------------------------------------------------------------------
    fn new(trace_info: TraceInfo, pub_inputs: Self::PublicInputs, options: ProofOptions) -> Self {
        let mut main_degrees = Vec::new();
        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(2, vec![PADDED_TRACE_LENGTH]); (N-TAU-1)/FE_TRIT_SIZE]); // c
        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(3, vec![PADDED_TRACE_LENGTH]); C_SIZE-(N-TAU-1)/FE_TRIT_SIZE]); // c

        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(1, vec![PADDED_TRACE_LENGTH]); HASH_CYCLE_LEN]); //Q_IND, Z_IND, Z_RANGE_IND 
        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(1, vec![PADDED_TRACE_LENGTH]); HASH_CYCLE_LEN]); //R_IND, Z_RANGE_IND
        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(1, vec![PADDED_TRACE_LENGTH]); HASH_CYCLE_LEN]); //SIGN_IND, Z_RANGE_IND

        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(2, vec![PADDED_TRACE_LENGTH]); 2*Q_RANGE]); // q_rangeproof, Z_RANGE_IND
        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(2, vec![PADDED_TRACE_LENGTH]); 2*R_RANGE]); // r_rangeproof, Z_RANGE_IND

        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(2, vec![PADDED_TRACE_LENGTH]); C_SIZE]); // fe ind, ranges
        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(2, vec![PADDED_TRACE_LENGTH]); FE_TRIT_SIZE]); // trit ind, ranges

        //TODO hide the magic number
        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(2, vec![PADDED_TRACE_LENGTH]); 197]); // ranges

        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(3, vec![PADDED_TRACE_LENGTH]); FE_TRIT_SIZE]); //before swap/set trits C_TRIT

        main_degrees.append(&mut vec![TransitionConstraintDegree::new(1); HASH_DIGEST_WIDTH]); // ctilde

        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(3, vec![PADDED_TRACE_LENGTH]); 6*HASH_STATE_WIDTH]); //hash_space

        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(4, vec![PADDED_TRACE_LENGTH]); 1]); //SWAP_ASSERT
        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(4, vec![PADDED_TRACE_LENGTH]); 1]); //SET_ASSERT
        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(2, vec![PADDED_TRACE_LENGTH]); 1]); //C_TRIT_ASSERT
        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(2, vec![PADDED_TRACE_LENGTH]); 2*4]); //W_DEC_ASSERT
        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(1, vec![PADDED_TRACE_LENGTH]); 4]); //W_LOW_ASSERT
        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(1, vec![PADDED_TRACE_LENGTH]); 2*4]); //W_HIGH_ASSERT
        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(1, vec![PADDED_TRACE_LENGTH]); HASH_DIGEST_WIDTH]); //CTILDE_ASSERT
        main_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(1, vec![PADDED_TRACE_LENGTH]); 8]); //Z_ASSERT

        debug_assert_eq!(TRACE_WIDTH+AUX_WIDTH, trace_info.width());

        let mut aux_degrees = Vec::new();
        aux_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(2, vec![PADDED_TRACE_LENGTH]); AUX_WIDTH-1]);
        aux_degrees.push(TransitionConstraintDegree::with_cycles(1, vec![PADDED_TRACE_LENGTH]));
        aux_degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(1, vec![PADDED_TRACE_LENGTH]); 4]);

        ThinDilAir {
            context: AirContext::new_multi_segment(
                trace_info, 
                main_degrees,
                aux_degrees,
                84,
                14, 
                options
            ).set_num_transition_exemptions(2),
            m: pub_inputs.m,
            cache: AtomicRefCell::new(vec![]),
        }
    }

    fn context(&self) -> &AirContext<Self::BaseField> {
        &self.context
    }

    fn evaluate_transition<E: FieldElement + From<Self::BaseField>>(
        &self,
        frame: &EvaluationFrame<E>,
        _periodic_values: &[E],
        result: &mut [E],
    ) {
        let current = frame.current();
        let next = frame.next();
        
        debug_assert_eq!(TRACE_WIDTH, current.len());
        debug_assert_eq!(TRACE_WIDTH, next.len());

        let qr_flag = _periodic_values[0];
        let notqr_flag = _periodic_values[1];
        let qrdec_flag = _periodic_values[2];
        let hashmask_flag = _periodic_values[3];
        let r_mod = _periodic_values[4];
        let q_mod = _periodic_values[5];
        let qr_base = _periodic_values[6];

        let cinserthashmask_flag = _periodic_values[7];
        let winserthashmask_flag = _periodic_values[8];

        let ctilde_flag = _periodic_values[9];
        let matmul_flag = _periodic_values[10];

        let ccopy_flag = _periodic_values[11];
        let crotate_flag = _periodic_values[12];

        let ctrit_dec_flag = _periodic_values[13];
        let ctrit_rotate_flag = _periodic_values[14];

        let s_fe = &_periodic_values[17..(17 + C_SIZE)];
        let s_trit = &_periodic_values[(17 + C_SIZE)..(17 + C_SIZE) + FE_TRIT_SIZE];
        let ark = &_periodic_values[((17 + C_SIZE) + FE_TRIT_SIZE)..];

        let powers_of_2 = vec![
            E::ONE,
            E::from(2u32),
            E::from(4u32),
            E::from(8u32),
            E::from(16u32),
            E::from(32u32),
            E::from(64u32),
            E::from(128u32),
            E::from(256u32),
            E::from(512u32),
            E::from(1024u32),
            E::from(2048u32),
            E::from(4096u32),
            E::from(8192u32),
            E::from(16384u32),
            E::from(32768u32),
            E::from(65536u32),
            E::from(131072u32),
            E::from(262144u32),
            E::from(524288u32),
            E::from(1048576u32),
            E::from(2097152u32),
        ];

        // Assert the poseidon round was computed correctly whenever a permutation needs to be applied
        assert_hash(&mut result[HASH_IND..(HASH_IND + 6*HASH_STATE_WIDTH)],
            &current[HASH_IND..(HASH_IND + 3*HASH_STATE_WIDTH)],
            &next[HASH_IND..(HASH_IND + 3*HASH_STATE_WIDTH)],
            &ark,
            hashmask_flag
        );

        // Copy ctilde
        for i in 0..HASH_DIGEST_WIDTH {
            result[CTILDE_IND + i] += next[CTILDE_IND + i] - current[CTILDE_IND + i];
        }

        //////////////////////////////////////////////////////////////////////////////////////////////////////
        //Sample In Ball
        let (mut lhs, mut rhs) = (E::ZERO, E::ZERO);
        
        //The FE index elements must be 0 or 1
        for i in 0..C_SIZE {
            lhs += E::from((i * FE_TRIT_SIZE) as u32) * current[SWAP_DEC_FE_IND + i];
            result.agg_constraint(SWAP_DEC_FE_IND + i, qrdec_flag, is_binary(current[SWAP_DEC_FE_IND + i]));
        }

        //The trit index elements must be 0 or 1
        for i in 0..FE_TRIT_SIZE {
            lhs += E::from((i) as u32) * current[SWAP_DEC_TRIT_IND + i];
            result.agg_constraint(SWAP_DEC_TRIT_IND + i, qrdec_flag, is_binary(current[SWAP_DEC_TRIT_IND + i]));
        }

        //The correct FE and trit indexes must be 1
        result.agg_constraint(SWAP_DEC_ASSERT, qrdec_flag, lhs - current[R_IND]);

        //Exactly one FE index must be 1
        lhs = E::ZERO;
        for i in 0..C_SIZE {
            lhs += current[SWAP_DEC_FE_IND + i];
        }
        result.agg_constraint(SWAP_DEC_FE_ASSERT, qrdec_flag, lhs - E::ONE);

        //Exactly one trit index must be 1
        lhs = E::ZERO;
        for i in 0..FE_TRIT_SIZE {
            lhs += current[SWAP_DEC_TRIT_IND + i];
        }
        result.agg_constraint(SWAP_DEC_TRIT_ASSERT, qrdec_flag, lhs - E::ONE);

        //The elements of the swap trit decomposition must be trinary
        //The swap trit decomposition must compose into the correct FE
        let (head, tail) = result.split_at_mut(SWAP_C_DEC_ASSERT + 1);
        let mut value = E::ZERO;
        for i in 0..C_SIZE {
            value += next[SWAP_DEC_FE_IND + i] * current[C_IND + i];
        }
            
        assert_trit_dec(
            &mut tail[SWAP_C_TRIT - (SWAP_C_DEC_ASSERT + 1)..SWAP_C_TRIT - (SWAP_C_DEC_ASSERT + 1) + FE_TRIT_SIZE],
            &next[SWAP_C_TRIT..SWAP_C_TRIT + FE_TRIT_SIZE], 
            value, 
            qrdec_flag,
            &mut head[SWAP_C_DEC_ASSERT],
            &powers_of_2
        );

        //The unmodified challenge elements must be copied correctly
        for i in 0..C_SIZE {
            result.agg_constraint(
                C_IND+i, 
                qrdec_flag, 
                (E::ONE - next[SWAP_DEC_FE_IND+i])*(E::ONE - s_fe[i])*(next[C_IND+i] - current[C_IND+i])
            );
        }

        //The trit must be swapped correctly (edge case, if the two indices of the FE are equal FE_i == FE_j)
        lhs = E::ZERO;
        rhs = E::ZERO;

        let mut mul = E::ZERO;
        let mut addition = E::ZERO; 
        let mut sub = E::ZERO; 
        for i in 0..FE_TRIT_SIZE {
            mul += s_trit[i] * powers_of_2[i * 2]; //Should be modified with this amount because of swap
            lhs += next[SWAP_DEC_TRIT_IND + i] * next[SWAP_C_TRIT + i]; //The value of the trit that needs to be swapped

            addition += next[SWAP_DEC_TRIT_IND + i] * powers_of_2[i*2] * (next[SIGN_IND] + E::ONE); //The value that should be added during set
            sub += next[SWAP_C_TRIT + i] * (next[SWAP_DEC_TRIT_IND + i]) * powers_of_2[i*2]; //The swapped trits represented value
        }

        lhs = lhs * mul;
        let swap_value = lhs;
        
        let mut set_change = E::ZERO;
        for i in 0..C_SIZE{
            rhs += s_fe[i]*(next[C_IND + i] - current[C_IND + i]); //Was modified with this amount
            set_change += (next[SWAP_DEC_FE_IND + i] * s_fe[i]) * (addition - sub); //If the j-th FE and i-th FE is the same the set with sign changed the FE by this amount
        }

        rhs = rhs - set_change;

        result.agg_constraint(SWAP_ASSERT, qrdec_flag, lhs - rhs);

        //The new trit must be set correctly
        lhs = E::ZERO;
        rhs = E::ZERO;

        let mut swap_change = E::ZERO;
        for i in 0..C_SIZE{
            lhs += next[SWAP_DEC_FE_IND + i] * next[C_IND + i]; //The new value of the modified FE
        }
        swap_change = next[SWAP_FE_EQUAL_IND] * swap_value;

        for i in 0..FE_TRIT_SIZE {
            rhs += next[SWAP_C_TRIT + i] * (E::ONE - next[SWAP_DEC_TRIT_IND + i]) * powers_of_2[i*2]; //The old value minus the swapped trit
        }

        result.agg_constraint(SET_ASSERT, qrdec_flag, lhs-rhs-addition-swap_change);

        // Q BIT DECOMPOSITION
        let (head, tail) = result.split_at_mut(Q_ASSERT);
        for i in 0..2 {
            let mut value = current[Q_IND];
            if i%2 == 1 {
                value = q_mod;
            }
            assert_bitdec(
                &mut head[Q_RANGE_IND+i*Q_RANGE..Q_RANGE_IND+(i+1)*Q_RANGE], 
                &current[Q_RANGE_IND+i*Q_RANGE..Q_RANGE_IND+(i+1)*Q_RANGE], 
                value, 
                qrdec_flag,
                &mut tail[i],
                &powers_of_2
            );
        }
        
        // Assert rotation of Q by 1 to the left
        result.agg_constraint(Q_IND+HASH_CYCLE_LEN-1, qr_flag, next[Q_IND+HASH_CYCLE_LEN-1] - current[Q_IND]);
        for i in 0..(HASH_CYCLE_LEN-1) {
            result.agg_constraint(Q_IND+i, qr_flag, next[Q_IND+i] - current[Q_IND+i+1]);
        }
        
        //  R BIT DECOMPOSITION
        let (head, tail) = result.split_at_mut(R_ASSERT);
        for i in 0..2 {
            let mut value = current[R_IND];
            if i%2 == 1 {
                value = r_mod;
            }
            assert_bitdec(
                &mut head[R_RANGE_IND+i*R_RANGE..R_RANGE_IND+(i+1)*R_RANGE],
                &current[R_RANGE_IND+i*R_RANGE..R_RANGE_IND+(i+1)*R_RANGE], 
                value, 
                qrdec_flag,
                &mut tail[i],
                &powers_of_2
            );
        }

        // Assert rotation of R by 1 to the left
        result.agg_constraint(R_IND+HASH_CYCLE_LEN-1, qr_flag, next[R_IND+HASH_CYCLE_LEN-1] - current[R_IND]);
        for i in 0..(HASH_CYCLE_LEN-1) {
            result.agg_constraint(R_IND+i, qr_flag, next[R_IND+i] - current[R_IND+i+1]);
        }
        
        // Assert q.base + r = x
        for i in 0..HASH_CYCLE_LEN{
            result[QR_ASSERT+i] = (notqr_flag)*(next[HASH_IND+i] - next[R_IND+i] - (qr_base+E::from(i as u32))*next[Q_IND+i]);
        }



        //////////////////////////////////////////////////////////////////////////////////////////////////////
        // PIT

        // Assert copy of C when ccopy_flag = 1
        for i in 0..C_SIZE{
            result.agg_constraint(C_IND+i, ccopy_flag, next[C_IND+i] - current[C_IND+i]);
        }

        // Assert rotation of C by 1 to the left when crotate_flag = 1
        result.agg_constraint(C_IND+C_SIZE-1, crotate_flag, next[C_IND+C_SIZE-1] - current[C_IND]);
        for i in 0..(C_SIZE-1) {
            result.agg_constraint(C_IND+i, crotate_flag, next[C_IND+i] - current[C_IND+i+1]);
        }

        //Assert that the trit form of the challenge equals to the field form after rotate
        let (head, tail) = result.split_at_mut(C_TRIT_ASSERT);
        let value = next[C_IND];
            
        assert_challenge_trit_dec(
            &mut head[C_TRIT_IND..C_TRIT_IND+11],
            &next[C_TRIT_IND..C_TRIT_IND+11], 
            value, 
            ctrit_dec_flag,
            &mut tail[0],
            &powers_of_2
        );

        //Assert rotation of the challenge trit by 1 when ccopy_flag = 1 during PIT phase
        result.agg_constraint(C_TRIT_IND+FE_TRIT_SIZE-1, ctrit_rotate_flag, next[C_TRIT_IND+FE_TRIT_SIZE-1] - current[C_TRIT_IND]);
        for i in 0..(FE_TRIT_SIZE-1) {
            result.agg_constraint(C_TRIT_IND+i, ctrit_rotate_flag, next[C_TRIT_IND+i] - current[C_TRIT_IND+i+1]);
        }

        // Copy claimed WHIGH into hash_space at beginning of every cycle or ensure hash rate space is copied correctly
        for i in 0..HASH_RATE_WIDTH {
            result.agg_constraint(HASH_IND+i, winserthashmask_flag, next[HASH_IND+i] - current[HASH_IND+i] - next[W_HIGH_IND+i]);
            result.agg_constraint(HASH_IND+i, cinserthashmask_flag, next[HASH_IND+i] - current[HASH_IND+i]);
        }

        // Assert that the hash_capacity was copied correctly at the end of each round
        assert_hash_copy(&mut result[HASH_IND..(HASH_IND+6*HASH_STATE_WIDTH)],
            &current[HASH_IND..(HASH_IND+3*HASH_STATE_WIDTH)],
            &next[HASH_IND..(HASH_IND+3*HASH_STATE_WIDTH)],
            &ark[0..3*HASH_STATE_WIDTH],
            cinserthashmask_flag+winserthashmask_flag
        );

        //////////////////////////////////////////////////////////////////////////////////////////////////

        // Assert rotation of WHIGH by 4 to the left
        result.agg_constraint(W_HIGH_IND+HASH_RATE_WIDTH-1, matmul_flag, next[W_HIGH_IND+HASH_RATE_WIDTH-1] - current[W_HIGH_IND+3]);
        result.agg_constraint(W_HIGH_IND+HASH_RATE_WIDTH-2, matmul_flag, next[W_HIGH_IND+HASH_RATE_WIDTH-2] - current[W_HIGH_IND+2]);
        result.agg_constraint(W_HIGH_IND+HASH_RATE_WIDTH-3, matmul_flag, next[W_HIGH_IND+HASH_RATE_WIDTH-3] - current[W_HIGH_IND+1]);
        result.agg_constraint(W_HIGH_IND+HASH_RATE_WIDTH-4, matmul_flag, next[W_HIGH_IND+HASH_RATE_WIDTH-4] - current[W_HIGH_IND]);
        for i in 0..(HASH_RATE_WIDTH-4) {
            result.agg_constraint(W_HIGH_IND+i, matmul_flag, next[W_HIGH_IND+i] - current[W_HIGH_IND+i+4]);
        }

        // Assert decomposition of W
        let twof = E::from(2u32);
        let gamma2 = E::from(GAMMA2);
        
        for i in 0..4 {
            result.agg_constraint(
                W_IND+i, 
                matmul_flag, 
                current[W_IND+i] - current[W_LOW_IND+i]-current[W_HIGH_IND+i]*twof*gamma2+current[W_BIND]*gamma2
            );
            result.agg_constraint(W_BIND+i, matmul_flag, is_binary(current[W_BIND+i])); //w2.(1-w2)=0
            result.agg_constraint(W_DEC_ASSERT+2*i, matmul_flag, current[W_HIGH_IND+i]*current[W_BIND+i]); //w1.w2=0
            result.agg_constraint(W_DEC_ASSERT+2*i+1, matmul_flag, current[W_LOW_IND+i]*current[W_BIND+i]); //w0.w2=0
        }

        let wlowlimitf = E::from(W_LOW_LIMIT);
        let (head, tail) = result.split_at_mut(W_LOW_ASSERT);
        for i in 0..4{
            let value = current[W_LOW_IND + i] + wlowlimitf;
            
            assert_bitdec(
                &mut head[W_LOW_RANGE_IND+i*W_LOW_RANGE..W_LOW_RANGE_IND+(i+1)*W_LOW_RANGE], 
                &current[W_LOW_RANGE_IND+i*W_LOW_RANGE..W_LOW_RANGE_IND+(i+1)*W_LOW_RANGE], 
                value, 
                matmul_flag,
                &mut tail[i],
                &powers_of_2
            );
        }

        let whighshiftf = E::from(W_HIGH_SHIFT);
        let (head, tail) = result.split_at_mut(W_HIGH_ASSERT);
        for i in 0..8{
            let mut value = current[W_HIGH_IND + i/2];
            if i%2 == 1 {
                value += whighshiftf;
            }
            
            assert_bitdec(
                &mut head[W_HIGH_RANGE_IND+i*W_HIGH_RANGE..W_HIGH_RANGE_IND+(i+1)*W_HIGH_RANGE], 
                &current[W_HIGH_RANGE_IND+i*W_HIGH_RANGE..W_HIGH_RANGE_IND+(i+1)*W_HIGH_RANGE], 
                value, 
                matmul_flag,
                &mut tail[i],
                &powers_of_2
            );
        }

        // Z BIT DECOMPOSITION
        let zlimitf = E::from(Z_LIMIT);
        let betaf = E::from(BETA);
        
        let (head, tail) = result.split_at_mut(Z_ASSERT);
        for i in 0..8{
            let mut value = current[Z_IND + i/2] + zlimitf;
            if i%2 == 1 {
                value += betaf;
            }
            
            assert_bitdec(
                &mut head[Z_RANGE_IND+i*Z_RANGE..Z_RANGE_IND+(i+1)*Z_RANGE], 
                &current[Z_RANGE_IND+i*Z_RANGE..Z_RANGE_IND+(i+1)*Z_RANGE], 
                value, 
                matmul_flag,
                &mut tail[i],
                &powers_of_2
            );
        }

        //////////////////////////////////////////////////////////////////////////////////////////////////////
        // ctilde check

        // Assert that ctilde is equal to h(mu||w) -- hashstate at step PIT_END-1
        for i in 0..HASH_DIGEST_WIDTH {
            result.agg_constraint(
                CTILDE_ASSERT + i, 
                ctilde_flag.into(), 
                are_equal(current[CTILDE_IND+i],current[HASH_IND+i])
            );
        }
    }
    
    fn evaluate_aux_transition<F, E>(
            &self,
            main_frame: &EvaluationFrame<F>,
            aux_frame: &EvaluationFrame<E>,
            periodic_values: &[F],
            aux_rand_elements: &winterfell::AuxRandElements<E>,
            result: &mut [E],
        ) where
            F: FieldElement<BaseField = Self::BaseField>,
            E: FieldElement<BaseField = Self::BaseField> + winterfell::math::ExtensionOf<F>, {
                let polycopy_flag = periodic_values[15];
                let polymult_flag = periodic_values[16];
                let matmul_flag = periodic_values[10];

                
                let main_current = main_frame.current();
                let _main_next = main_frame.next();

                let aux_current = aux_frame.current();
                let aux_next = aux_frame.next();

                let random_elements = aux_rand_elements.rand_elements();

                // Carrying out the following PIT
                // Q(GAMMA).(GAMMA^256 + 1) + W(GAMMA) = A(GAMMA).z(GAMMA) - t(GAMMA).c(GAMMA)
                // Q, W, z, t are 4x1 vectors of degree 255 polynomials
                // A is a 4x4 matric of degree 255 polynomials
                // c is a degree 255 polynomial
                
                // Evaluate T and A at point random_elements[0]
                // We need a hacky solution with caching because of restrictions in winterfell and rust
                let mut t_eval = [E::ZERO; 4];
                let mut a_eval = [[E::ZERO; 4]; 4];

                let mut cache = self.cache.borrow_mut();
                if cache.len() > 0 {
                    let mut reader = SliceReader::new(&cache);
                    for j in 0..4 {
                    if let Ok(v) = E::read_from(&mut reader) {
                        t_eval[j] = v;
                    } else {
                        panic!("recover from cache failed");
                    }
                }

                    for j in 0..4 {
                        for i in 0..4 {
                            if let Ok(v) = E::read_from(&mut reader) {
                                a_eval[i][j] = v;
                            } else {
                                panic!("recover from cache failed");
                            }
                        }
                    }
                } else {
                    let mut pubt: [[E; N]; 4] = [[E::ZERO; N]; 4];
                    for j in 0..4 {
                        pubt[j] = PUBT[j].map(E::from);
                        t_eval[j] = poly_eval(&pubt[j], random_elements[0]);
                        t_eval[j].write_into(&mut *cache);
                    }
                    let mut puba: [[[E; N]; 4]; 4] = [[[E::ZERO; N]; 4]; 4];
                    for j in 0..4 {
                        for i in 0..4 {
                            puba[i][j] = PUBA[i][j].map(E::from);
                            a_eval[i][j] = poly_eval(&puba[i][j], random_elements[0]);
                            a_eval[i][j].write_into(&mut *cache);
                        }
                    }
                }

                let c_eval = aux_current[CAUX];
                let w_eval = &aux_current[WAUX..WAUX+4];
                let qw_eval = &aux_current[QWAUX..QWAUX+4];
                let z_eval = &aux_current[ZAUX..ZAUX+4];

                let mut lhs:E;
                let mut rhs:E;
                for ii in 0..4{
                    lhs = qw_eval[ii]*(random_elements[0].exp(E::PositiveInteger::from(256 as u32)) + E::ONE) + w_eval[ii];
                    rhs = E::ZERO;
                    
                    for i in 0..4{
                        rhs += a_eval[ii][i]*z_eval[i]; 
                    }

                    rhs -= c_eval*t_eval[ii];

                    //print!("{} {}\n", lhs, rhs);

                    result.agg_constraint(
                        POLYMULTASSERT + ii, 
                        polymult_flag.into(), 
                        are_equal(lhs,rhs)
                    );
                }
                
                // evaluation aggregation check
                // todo: can move this to mod.rs constants and save some work
                let mut ec_tuples: Vec<(usize,usize)> = Vec::new();
                ec_tuples.push((CAUX, C_TRIT_IND));
                for i in 0..4 {
                    ec_tuples.push((ZAUX+i, Z_IND+i));
                    ec_tuples.push((WAUX+i, W_IND+i));
                    ec_tuples.push((QWAUX+i, QW_IND+i));
                }

                result.agg_constraint(
                    GAMMA, 
                    matmul_flag.into(), 
                    are_equal(aux_next[GAMMA],aux_current[GAMMA]*random_elements[0],)
                );
                result.agg_constraint(
                    GAMMA, 
                    polycopy_flag.into(), 
                    are_equal(aux_next[GAMMA],aux_current[GAMMA],)
                );

                ec_tuples.iter().for_each(
                    |ec| 
                    poly_eval_assert(
                        ec.0,
                        matmul_flag.into(),
                        polycopy_flag.into(),
                        ec.1,
                        result,
                        &aux_next,
                        &aux_current,
                        main_current
                    )
                );
    }

    fn get_assertions(&self) -> Vec<Assertion<Self::BaseField>> {
        let mut main_assertions = Vec::new();

        // Assert HASH_STATE is zero in all registers except the first HASH_DIGEST_WIDTH+1
        for i in HASH_DIGEST_WIDTH+1..HASH_STATE_WIDTH{
            main_assertions.push(Assertion::single(HASH_IND+i, 0, BaseElement::ZERO));
        } 
        
        // Assert HASH_STATE is zero in all registers except the first HASH_RATE_WIDTH
        for i in HASH_RATE_WIDTH..HASH_STATE_WIDTH{
            main_assertions.push(Assertion::single(HASH_IND+i, COM_END, BaseElement::ZERO));
        }

        // Assert HASH_RATE..HASH_STATE is HTR on step COM_START
        for i in HASH_RATE_WIDTH..HASH_STATE_WIDTH{
            main_assertions.push(Assertion::single(HASH_IND+i, COM_START, BaseElement::from(HTR[i])));
        }

        // Assert 0..HASH_DIGEST is HTR+m on step COM_START
        for i in 0..HASH_DIGEST_WIDTH{
            main_assertions.push(Assertion::single(HASH_IND+i, COM_START, BaseElement::from(HTR[i])+self.m[i]));
        }

        // Assert C_IND is initialized to zero at the beginning (HASH_CYCLE_LEN-1)
        for i in 0..C_SIZE{
            main_assertions.push(Assertion::single(C_IND+i,  HASH_CYCLE_LEN-1, BaseElement::ZERO));
        }

        // Assert highest coefficienct of qw is 0
        for i in 0..K{
            main_assertions.push(Assertion::single(QW_IND+i, PIT_START-1 + PIT_LEN-4, BaseElement::ZERO));
        }
        main_assertions
    }

    fn get_aux_assertions<E: FieldElement<BaseField = Self::BaseField>>(
            &self,
            aux_rand_elements: &winterfell::AuxRandElements<E>,
        ) -> Vec<Assertion<E>> {
        
        let mut aux_assertions = Vec::new();
        
        let random_elements = aux_rand_elements.rand_elements();
        
        aux_assertions.push(Assertion::single(GAMMA, PIT_START+1, random_elements[0]));
        
        aux_assertions.push(Assertion::single(CAUX, PIT_START, E::ZERO));
        for i in 0..K {
            aux_assertions.push(Assertion::single(ZAUX+i, PIT_START, E::ZERO));
            aux_assertions.push(Assertion::single(WAUX+i, PIT_START, E::ZERO));
            aux_assertions.push(Assertion::single(QWAUX+i, PIT_START, E::ZERO));
        }
        
        aux_assertions
    }

    fn get_periodic_column_values(&self) -> Vec<Vec<Self::BaseField>> {
        let mut result = Vec::new();
        result.push(get_qr_mask());
        result.push(get_notqr_mask());
        result.push(get_qrdec_mask());
        result.push(get_hashmask_constants());
        result.push(get_r_mod());
        result.push(get_q_mod());
        result.push(get_qr_base_constants());
        result.push(get_copyhashmask_constants());
        result.push(get_inserthashmask_constants());
        result.push(get_ctilde_flag());
        result.push(get_matmul_mask());
        result.push(get_ccopy_mask());
        result.push(get_crotate_mask());
        result.push(get_ctrit_dec_mask());
        result.push(get_ctrit_rotate_mask());
        result.push(get_polycopy_mask());
        result.push(get_polymult_mask());
        result.append(&mut get_swap_fe_constants());
        result.append(&mut get_swap_trit_constants());
        result.append(&mut poseidon_23_spec::get_round_constants());

        result
    }
}

fn assert_hash<E: FieldElement + From<BaseElement>>(
    result: &mut [E],
    current: &[E],
    next: &[E],
    ark: &[E],
    flag: E
) {
    poseidon_23_spec::enforce_round(
        &mut result[0..(2*HASH_STATE_WIDTH)],
        &current[0..(HASH_STATE_WIDTH)],
        &next[(2*HASH_STATE_WIDTH)..(3*HASH_STATE_WIDTH)],
        &ark[0..HASH_STATE_WIDTH],
        flag,
    );
    poseidon_23_spec::enforce_round(
        &mut result[(4*HASH_STATE_WIDTH)..(6*HASH_STATE_WIDTH)],
        &next[(2*HASH_STATE_WIDTH)..(3*HASH_STATE_WIDTH)],
        &next[(HASH_STATE_WIDTH)..(2*HASH_STATE_WIDTH)],
        &ark[HASH_STATE_WIDTH..2*HASH_STATE_WIDTH],
        flag,
    );
    poseidon_23_spec::enforce_round(
        &mut result[(2*HASH_STATE_WIDTH)..(4*HASH_STATE_WIDTH)],
        &next[(HASH_STATE_WIDTH)..(2*HASH_STATE_WIDTH)],
        &next[0..(HASH_STATE_WIDTH)],
        &ark[2*HASH_STATE_WIDTH..3*HASH_STATE_WIDTH],
        flag,
    );
}

fn assert_hash_copy<E: FieldElement + From<BaseElement>>(
    result: &mut [E],
    current: &[E],
    next: &[E],
    _ark: &[E],
    flag: E
) {
    // Asserting copy of HASH_CAPACITY
    for i in 0..3{
        for j in HASH_RATE_WIDTH..HASH_STATE_WIDTH{
            result[HASH_STATE_WIDTH*i + j] += flag*(current[HASH_STATE_WIDTH*i + j] - next[HASH_STATE_WIDTH*i + j]);
        }
    }
}

fn assert_trit_dec<E: FieldElement + From<BaseElement>>(
    result: &mut[E], 
    trits: &[E],
    value: E, 
    flag: E,
    final_check: &mut E,
    powers_of_2: &[E]
) {
    let mut should_be_value = E::ZERO;
    for i in 0..trits.len() {
        let current_trit = trits[i];
        result[i] += flag*is_ternary(current_trit);
        
        should_be_value += current_trit*powers_of_2[i*2];
    }

    *final_check+=flag*(value - should_be_value);
}

fn assert_challenge_trit_dec<E: FieldElement + From<BaseElement>>(
    result: &mut[E], 
    trits: &[E],
    value: E, 
    flag: E,
    final_check: &mut E,
    powers_of_2: &[E]
) {
    let mut should_be_value = E::ZERO;
    for i in 0..trits.len() {
        let current_trit = trits[i];
        result[i] += flag*is_ternary_challenge(current_trit);
        
        let converted_trit = (E::from(3u32)*current_trit*current_trit - current_trit)/E::from(2u32);
        should_be_value += converted_trit*powers_of_2[i*2];
    }

    *final_check+=flag*(value - should_be_value);
}

fn assert_bitdec<E: FieldElement + From<BaseElement>>(
    result: &mut[E], 
    bits: &[E],
    value: E, 
    flag: E,
    final_check: &mut E,
    powers_of_2: &[E]
) {
    let mut should_be_value = E::ZERO;
    for i in 0..bits.len() {
        result[i] += flag*is_binary(bits[i]);
        should_be_value += bits[i]*powers_of_2[i];
    }

    *final_check+=flag*(value - should_be_value);
}

fn get_qr_mask() -> Vec<BaseElement> {
    let mut qr_mask = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];

    for i in HASH_CYCLE_LEN-1..(HASH_CYCLE_LEN)*(S_BALL_END){
        qr_mask[i] = HASH_CYCLE_MASK[i%HASH_CYCLE_LEN];
    }

    qr_mask
}

fn get_notqr_mask() -> Vec<BaseElement> {
    let mut notqr_mask = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];

    // Check that (HASH_CYCLE_LEN)*(SBALLEND)-1 is correct
    for i in (HASH_CYCLE_LEN-1)..(HASH_CYCLE_LEN)*(S_BALL_END)-1{
        notqr_mask[i] = BaseElement::ONE - HASH_CYCLE_MASK[i%HASH_CYCLE_LEN];
    }

    notqr_mask
}

fn get_qrdec_mask() -> Vec<BaseElement> {
    let mut qrdec_mask = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];

    for i in HASH_CYCLE_LEN..(HASH_CYCLE_LEN)*(S_BALL_END)-1 {
        qrdec_mask[i] = BaseElement::ONE;
    }

    qrdec_mask
}

//The i index of the sample in ball to FE index
fn get_swap_fe_constants() -> Vec<Vec<BaseElement>> {
    let mut swap_fe_const = Vec::new();
    for _ in 0..C_SIZE {
        swap_fe_const.push(vec![BaseElement::ZERO; PADDED_TRACE_LENGTH]);
    }
    for i in HASH_CYCLE_LEN-1..(S_BALL_END)*HASH_CYCLE_LEN{
        //N - TAU + i - HASH_CYCLE_LEN is the trit index
        swap_fe_const[(N - TAU + i - HASH_CYCLE_LEN) / FE_TRIT_SIZE][i] = BaseElement::ONE;
    }

    swap_fe_const
}

//The i index of the sample in ball to trit index
fn get_swap_trit_constants() -> Vec<Vec<BaseElement>> {
    let mut swap_trit_const = Vec::new();
    for _ in 0..FE_TRIT_SIZE {
        swap_trit_const.push(vec![BaseElement::ZERO; PADDED_TRACE_LENGTH]);
    }
    for i in HASH_CYCLE_LEN-1..(S_BALL_END)*HASH_CYCLE_LEN{
        swap_trit_const[(N - TAU + i - HASH_CYCLE_LEN) % FE_TRIT_SIZE][i] = BaseElement::ONE;
    }

    swap_trit_const
}

fn get_qr_base_constants() -> Vec<BaseElement> {
    let mut qr_base = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];

    for i in HASH_CYCLE_LEN-1..(S_BALL_END)*HASH_CYCLE_LEN{
        qr_base[i] = BaseElement::new((N-TAU+i-HASH_CYCLE_LEN+1) as u32);
    }

    qr_base
}

fn get_hashmask_constants() -> Vec<BaseElement> {
    let mut hashmask_const = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];
    for i in 0..HASH_CYCLE_LEN{
        hashmask_const[i] = HASH_CYCLE_MASK[i%HASH_CYCLE_LEN];
    }

    for i in 0..(HASH_CYCLE_LEN)*(S_BALL_END){
        hashmask_const[i] = HASH_CYCLE_MASK[i%HASH_CYCLE_LEN];
    }

    for i in PIT_START..PIT_END{
        hashmask_const[i] = HASH_CYCLE_MASK[i%HASH_CYCLE_LEN];
    }

    hashmask_const
}

fn get_r_mod() -> Vec<BaseElement> {
    let mut r_mod = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];

    for i in 0..TAU+1{
        // println!("r_mod: {}", 256 - (N-1-TAU+i) as u32);
        r_mod[HASH_CYCLE_LEN+i] = BaseElement::new(256 - (N-TAU+i) as u32);
    }

    r_mod
}

fn get_q_mod() -> Vec<BaseElement> {
    let mut q_mod = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];

    for i in 0..TAU+1{
        q_mod[HASH_CYCLE_LEN+i] = BaseElement::new(M/(N-TAU+i) as u32);
    }

    q_mod
}

fn get_inserthashmask_constants() -> Vec<BaseElement> {
    let mut inserthashmask_const = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];
    for i in PIT_START..PIT_END-1{
        inserthashmask_const[i] = BaseElement::ONE - HASH_CYCLE_MASK[i%HASH_CYCLE_LEN];
    }

    inserthashmask_const
}

fn get_copyhashmask_constants() -> Vec<BaseElement> {
    let mut copyhashmask_const = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];
    for i in 0..(HASH_CYCLE_LEN)*(S_BALL_END){
        copyhashmask_const[i] = BaseElement::ONE - HASH_CYCLE_MASK[i%HASH_CYCLE_LEN];
    }

    copyhashmask_const
}

fn get_ctilde_flag() -> Vec<BaseElement> {
    // Flag to check A(gamma).z(gamma) - c(gamma).t(gamma) = w(gamma) + (gamma^256 + 1).q(gamma)
    let mut ctilde_flag = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];
    ctilde_flag[PIT_END-1] = BaseElement::ONE;

    ctilde_flag
}

fn get_matmul_mask() -> Vec<BaseElement> {
    let mut matmul_mask = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];
    for i in PIT_START..PIT_END-4{
        if i%HASH_CYCLE_LEN < HASH_CYCLE_LEN-2 {
            matmul_mask[i] = BaseElement::ONE;
        }
    }

    matmul_mask
}

//Copy when between PIT and S_BALL, also during PIT when not rotated
fn get_ccopy_mask() -> Vec<BaseElement> {
    let mut ccopy_mask = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];

    //PIT_START+1 so the edge case for the if in the next for is included (first 0 is not rotate)
    for i in (HASH_CYCLE_LEN)*(S_BALL_END)..PIT_START+1{
        ccopy_mask[i] = BaseElement::ONE;
    }

    for i in PIT_START+1..PIT_END{
        let hashcycle_pos = (i - PIT_START) % HASH_CYCLE_LEN;
        if hashcycle_pos < HASH_CYCLE_LEN - 2{
            if (((i - PIT_START) / HASH_CYCLE_LEN) * (HASH_CYCLE_LEN - 2) + hashcycle_pos + 1) % FE_TRIT_SIZE != 0 {
                ccopy_mask[i] = BaseElement::ONE;
            }
        } else {
            ccopy_mask[i] = BaseElement::ONE;
        }
    }

    ccopy_mask
}

fn get_crotate_mask() -> Vec<BaseElement> {
    let mut crotate_mask = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];

    for i in PIT_START+1..PIT_END{
        let hashcycle_pos = (i - PIT_START) % HASH_CYCLE_LEN;
        if hashcycle_pos < HASH_CYCLE_LEN - 2{
            if (((i - PIT_START) / HASH_CYCLE_LEN) * (HASH_CYCLE_LEN - 2) + hashcycle_pos + 1) % FE_TRIT_SIZE == 0 {
                crotate_mask[i] = BaseElement::ONE;
            }
        }   
    }

    crotate_mask
}

fn get_ctrit_dec_mask() -> Vec<BaseElement> {
    let mut ctrit_dec_mask = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];

    for i in PIT_START..PIT_END{
        let hashcycle_pos = (i - PIT_START) % HASH_CYCLE_LEN;
        if hashcycle_pos < HASH_CYCLE_LEN - 2{
            if (((i - PIT_START) / HASH_CYCLE_LEN) * (HASH_CYCLE_LEN - 2) + hashcycle_pos + 1) % FE_TRIT_SIZE == 0 {
                ctrit_dec_mask[i] = BaseElement::ONE;
            }
        }   
    }

    ctrit_dec_mask
}

//Copy when between PIT and S_BALL, also during PIT when not rotated
fn get_ctrit_rotate_mask() -> Vec<BaseElement> {
    let mut ctrit_rotate_mask = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];

    for i in PIT_START+1..PIT_END{
        let hashcycle_pos = (i - PIT_START) % HASH_CYCLE_LEN;
        if hashcycle_pos < HASH_CYCLE_LEN - 2{
            if (((i - PIT_START) / HASH_CYCLE_LEN) * (HASH_CYCLE_LEN - 2) + hashcycle_pos + 1) % FE_TRIT_SIZE != 0 {
                ctrit_rotate_mask[i] = BaseElement::ONE;
            }
        }
    }

    ctrit_rotate_mask
}

fn poly_eval<E:FieldElement + From<BaseElement>>(
    coeffs: &[E],
    x: E,
) -> E {
    let mut eval = E::ZERO;
    let mut gamma_acc = E::ONE;
    for i in 0..N{
        eval += coeffs[i]*gamma_acc;
        gamma_acc = gamma_acc*x;
    }

    eval
}

fn poly_eval_assert<F: FieldElement, E:FieldElement + From<F>>(
    eval_index: usize,
    flag1: E,
    flag2: E,
    coeff_index: usize,
    result: &mut [E],
    aux_next: &[E],
    aux_current: &[E],
    main_current: &[F]
) {
    result.agg_constraint(
        eval_index, 
        flag1, 
        are_equal(aux_next[eval_index],aux_current[eval_index] + aux_current[GAMMA]*main_current[coeff_index].into(),)
    );

    result.agg_constraint(
        eval_index, 
        flag2, 
        are_equal(aux_next[eval_index],aux_current[eval_index],)
    ); 
}

fn get_polycopy_mask() -> Vec<BaseElement> {
    let mut polycopy_mask = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];
    for i in PIT_START..PIT_END{
        if i%HASH_CYCLE_LEN >= HASH_CYCLE_LEN-2 {
            polycopy_mask[i] = BaseElement::ONE;
        }
    }

    polycopy_mask
}

fn get_polymult_mask() -> Vec<BaseElement> {
    // Flag to check A(gamma).z(gamma) - c(gamma).t(gamma) = w(gamma) + (gamma^256 + 1).q(gamma)
    let mut polymult_mask = vec![BaseElement::ZERO; PADDED_TRACE_LENGTH];
    polymult_mask[PIT_END-4] = BaseElement::ONE;

    polymult_mask
}