use std::vec;

use rand_chacha::ChaCha20Rng;
use winterfell::{
    crypto::{hashers::Blake3_256, DefaultRandomCoin, MerkleTree}, matrix::ColMatrix, AuxRandElements, CompositionPoly, CompositionPolyTrace, ConstraintCompositionCoefficients, DefaultConstraintCommitment, DefaultConstraintEvaluator, DefaultTraceLde, PartitionOptions, StarkDomain, TraceInfo, TracePolyTable, TraceTable, ZkParameters
};

use super::{
    BaseElement, DisclosureAir, FieldElement, ProofOptions, air::PublicInputs,
    Prover, HASH_CYCLE_LEN, HASH_DIGEST_WIDTH, HASH_RATE_WIDTH, HASH_STATE_WIDTH
};

use crate::{disclosurepf2::{Credential, DisclosureInputs, FIRST_ATTR_IND, HASH_IND, HASHING_PHASE_START, STORAGE_IND, TRACE_WIDTH}, utils::poseidon_23_spec::{self}};

//attr0 secret attr, same for every cred
//attr1 nonce attr, fresh when cred issued, never disclosed for RP

pub struct DisclosureProver {
    options: ProofOptions,
    credentials: Vec<Credential>
}

impl DisclosureProver {
    pub fn new(options: ProofOptions, credentials: Vec<Credential>) -> Self {
        Self { options, credentials }
    }

    pub fn build_trace(&self) -> TraceTable<BaseElement> {
        let mut hash_trace_lengths = Vec::new();
        let mut hash_trace_lengths_sum = 0;

        //H(H(hidden_attrs)||H(issuer_attrs))
        //all_attributes = hidden_attrs U issuer_attrs
        for credential in &self.credentials {
            //Add padding attribute if needed
            // if self.attributes[i].len() % 2 == 1 {
            //     self.attributes[i].push([BaseElement::ZERO; HASH_DIGEST_WIDTH]);
            // }

            let cred_trace_length = credential.attributes.len() / 2 * HASH_CYCLE_LEN;

            hash_trace_lengths.push(cred_trace_length);
            hash_trace_lengths_sum += cred_trace_length;
        }

        let final_hash_length_sum = self.credentials.len()*HASH_CYCLE_LEN;
        
        let randomize_cred_trace_length_sum = self.credentials.len()*HASH_CYCLE_LEN;

        let trace_length = hash_trace_lengths_sum + final_hash_length_sum + randomize_cred_trace_length_sum;

        //trace length must be power of 2
        let mut i = 16; 
        //Added 2 because of the winterfell artifact at the end of trace
        while i < trace_length + 2 {
            i *= 2;
        }
        let trace_padded_length = i;

        let mut trace = TraceTable::new(TRACE_WIDTH, trace_padded_length);
        trace.fill(
            |state| {
                for i in 0..HASH_DIGEST_WIDTH {
                    state[FIRST_ATTR_IND + i] = self.credentials[0].attributes[0][i];

                    state[HASH_IND + i] = self.credentials[0].attributes[0][i];
                    state[HASH_IND + i + HASH_DIGEST_WIDTH] = self.credentials[0].attributes[1][i];
                }
            },
            |step, state| {
                if step < trace_length {

                    if step % HASH_CYCLE_LEN > 0 {
                        poseidon_23_spec::apply_round(&mut state[HASH_IND..HASH_IND + (3*HASH_STATE_WIDTH)], step - 1);
                    } else{

                        let mut step_in_cred = step - HASHING_PHASE_START;
                        let mut cred_index = 0;
                        for i in 0..hash_trace_lengths.len() {
                            if step_in_cred >= hash_trace_lengths[i] + 2*HASH_CYCLE_LEN /*addition for final hash and credential hash*/{
                                cred_index += 1;
                                step_in_cred = step_in_cred - hash_trace_lengths[i] - 2*HASH_CYCLE_LEN;
                            }
                        }

                        let _cycle_num = step_in_cred / HASH_CYCLE_LEN;
                        
                        if step_in_cred == 0 {
                            //Init
                            for i in 0..HASH_DIGEST_WIDTH {
                                state[HASH_IND + i] = self.credentials[cred_index].attributes[0][i];
                                state[HASH_IND + HASH_DIGEST_WIDTH + i] = self.credentials[cred_index].attributes[1][i];
                            }

                            //clear hash state
                            for i in HASH_RATE_WIDTH..HASH_STATE_WIDTH {
                                state[HASH_IND + i] = BaseElement::ZERO;
                            }
                        } else if step_in_cred < hash_trace_lengths[cred_index] {

                            if step_in_cred == self.credentials[cred_index].num_of_user_attributes / 2 * HASH_CYCLE_LEN {
                                //Finished user hash

                                //Save result of hidden attributes to storage
                                for i in 0..HASH_DIGEST_WIDTH {
                                    state[STORAGE_IND + i] = state[HASH_IND + i];
                                }
                                
                                //Clear hash state for non-blind attributes
                                for i in 0..HASH_STATE_WIDTH {
                                    state[HASH_IND + i] = BaseElement::ZERO;
                            }
                            }
                            //load attributes
                            for i in 0..HASH_DIGEST_WIDTH {

                                state[HASH_IND + i] += self.credentials[cred_index].attributes[2 * _cycle_num][i];
                                state[HASH_IND + HASH_DIGEST_WIDTH + i] += self.credentials[cred_index].attributes[2 * _cycle_num + 1][i];
                            }
                        } else if step_in_cred == hash_trace_lengths[cred_index] {
                            //Final hash for the attributes

                            //Load issuer hash result to 2nd slot
                            for i in 0..HASH_DIGEST_WIDTH {
                                state[HASH_IND + HASH_DIGEST_WIDTH + i] = state[HASH_IND + i];
                            }

                            //Load user hash result to 1st slot
                            for i in 0..HASH_DIGEST_WIDTH {
                                state[HASH_IND + i] = state[STORAGE_IND + i];
                            }

                            //Clear capacity
                            for i in HASH_RATE_WIDTH..HASH_STATE_WIDTH {
                                state[HASH_IND + i] = BaseElement::ZERO;
                            }

                        } else {
                            //Load nonce for hash result
                            for i in HASH_DIGEST_WIDTH..HASH_RATE_WIDTH {
                                state[HASH_IND + i] = self.credentials[cred_index].salt[i - HASH_DIGEST_WIDTH];
                            }

                            //Clear capacity
                            for i in HASH_RATE_WIDTH..HASH_STATE_WIDTH {
                                state[HASH_IND + i] = BaseElement::ZERO;
                            }
                            
                        }
                    }

                    // print!("{}: ", step);
                    // for i in 0..state.len() {
                    //     print!("{} ", state[i]);
                    // }
                    // println!();
                }

                // Artifact of winterfell. Used to prevent constant polynomial when interpolating
                if step==trace_padded_length-2 {
                    for i in 0..TRACE_WIDTH{
                        state[i] = BaseElement::new(123 as u32);
                    }
                }
            },
        );

        trace
    }
}

impl Prover for DisclosureProver {
    type BaseField = BaseElement;
    type Air = DisclosureAir;
    type Trace = TraceTable<BaseElement>;
    type ZkPrng = ChaCha20Rng;

    fn get_pub_inputs(&self, _trace: &Self::Trace) -> PublicInputs {

        let mut disclosures: Vec<DisclosureInputs> = vec![];

        for credential in &self.credentials {
            let mut disclosed_attributes: Vec<[BaseElement; HASH_DIGEST_WIDTH]> = vec![];

            for index in &credential.disclosed_indices {
                disclosed_attributes.push(credential.attributes[*index]);
            }
            disclosures.push(DisclosureInputs { disclosed_attributes: disclosed_attributes, indices: credential.disclosed_indices.clone(), num_of_attributes: credential.attributes.len(), num_of_user_attributes: credential.num_of_user_attributes, salted_hash: credential.salted_hash});
        }

        PublicInputs{disclosures}
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
        DefaultConstraintCommitment<E, Blake3_256<BaseElement>, Self::ZkPrng, Self::VC>;
    
    fn new_trace_lde<E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        trace_info: &TraceInfo,
        main_trace: &ColMatrix<Self::BaseField>,
        domain: &StarkDomain<Self::BaseField>,
        partition_option: PartitionOptions,
        zk_parameters: Option<ZkParameters>,
        prng: &mut Option<Self::ZkPrng>,
    ) -> (Self::TraceLde<E>, TracePolyTable<E>) {
        DefaultTraceLde::new(trace_info, main_trace, domain, partition_option, zk_parameters, prng)
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
        zk_parameters: Option<ZkParameters>,
        prng: &mut Option<Self::ZkPrng>,
    ) -> (Self::ConstraintCommitment<E>, CompositionPoly<E>) {
        DefaultConstraintCommitment::new(
            composition_poly_trace,
            num_constraint_composition_columns,
            domain,
            partition_options,
            zk_parameters,
            prng
        )
    }
}