use std::os::macos::raw::stat;

use rand_chacha::ChaCha20Rng;
use winterfell::{
    crypto::{hashers::Blake3_256, DefaultRandomCoin, MerkleTree}, matrix::ColMatrix, AuxRandElements, CompositionPoly, CompositionPolyTrace, ConstraintCompositionCoefficients, DefaultConstraintCommitment, DefaultConstraintEvaluator, DefaultTraceLde, MockPrng, PartitionOptions, StarkDomain, Trace, TraceInfo, TracePolyTable, TraceTable, ZkParameters
};

use super::{
    BaseElement, DisclosureAir, FieldElement, ProofOptions, air::PublicInputs,
    Prover, HASH_CYCLE_LEN, HASH_DIGEST_WIDTH, HASH_RATE_WIDTH, HASH_STATE_WIDTH, NUM_HASH_ROUNDS
};

use crate::{disclosurepf2::{FIRST_ATTR_IND, HASHING_PHASE_START, HASH_IND, STORAGE_IND, TRACE_WIDTH}, utils::poseidon_23_spec::{self}};

//attr0 secret attr, same for every cred
//attr1 nonce attr, fresh when cred issued, never disclosed for RP

pub struct DisclosureProver {
    options: ProofOptions,

    attributes: Vec<Vec<[BaseElement; HASH_DIGEST_WIDTH]>>,
    num_of_user_attributes: Vec<usize>,
    disclosed_indices: Vec<Vec<usize>>,
    comm: Vec<[BaseElement; HASH_DIGEST_WIDTH]>,
    cred_nonce: Vec<[BaseElement; 12]>
}

impl DisclosureProver {
    pub fn new(options: ProofOptions, attributes: Vec<Vec<[BaseElement; HASH_DIGEST_WIDTH]>>, num_of_user_attributes: Vec<usize>, disclosed_indices: Vec<Vec<usize>>, comm: Vec<[BaseElement; HASH_DIGEST_WIDTH]>, cred_nonce: Vec<[BaseElement; 12]>) -> Self {
        Self { options, attributes, num_of_user_attributes, disclosed_indices, comm, cred_nonce }
    }

    pub fn build_trace(&self) -> TraceTable<BaseElement> {
        let mut hash_trace_lengths = Vec::new();
        let mut hash_trace_lengths_sum = 0;

        //H(H(hidden_attrs)||H(issuer_attrs))
        //all_attributes = hidden_attrs U issuer_attrs
        for i in 0..self.attributes.len() {
            //Add padding attribute if needed
            // if self.attributes[i].len() % 2 == 1 {
            //     self.attributes[i].push([BaseElement::ZERO; HASH_DIGEST_WIDTH]);
            // }

            hash_trace_lengths.push(self.attributes[i].len() / 2 * HASH_CYCLE_LEN);
            hash_trace_lengths_sum += hash_trace_lengths[i];
        }

        let final_hash_length_sum = self.attributes.len()*HASH_CYCLE_LEN;
        
        let randomize_cred_trace_length_sum = self.attributes.len()*HASH_CYCLE_LEN;

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
                    state[FIRST_ATTR_IND + i] = self.attributes[0][0][i];

                    state[HASH_IND + i] = self.attributes[0][0][i];
                    state[HASH_IND + i + HASH_DIGEST_WIDTH] = self.attributes[0][1][i];
                }
            },
            |step, state| {
                if step <= trace_length {

                    if step % HASH_CYCLE_LEN > 0 {
                        poseidon_23_spec::apply_round(&mut state[HASH_IND..HASH_IND + (3*HASH_STATE_WIDTH)], step - 1);
                    } else{

                        let mut step_in_cert = step - HASHING_PHASE_START;
                        let mut cert_index = 0;
                        for i in 0..hash_trace_lengths.len() {
                            if step_in_cert >= hash_trace_lengths[i] + 2*HASH_CYCLE_LEN /*addition for final hash and credential hash*/{
                                cert_index += 1;
                                step_in_cert = step_in_cert - hash_trace_lengths[i] - 2*HASH_CYCLE_LEN;
                            }
                        }

                        let _cycle_num = step_in_cert / HASH_CYCLE_LEN;
                        
                        if step_in_cert == 0 {
                            //clear hash capacity
                            for i in HASH_RATE_WIDTH..HASH_STATE_WIDTH {
                                state[HASH_IND + i] = BaseElement::ZERO;
                            }
                        } else if step_in_cert < hash_trace_lengths[cert_index] {

                            if step_in_cert == self.num_of_user_attributes[cert_index] / 2 * HASH_CYCLE_LEN {
                                //Finished user hash

                                //Save result to storage
                                for i in 0..HASH_DIGEST_WIDTH {
                                    state[STORAGE_IND + i] = state[HASH_IND + i];
                                }
                                
                                //Clear capacity
                                for i in HASH_RATE_WIDTH..HASH_STATE_WIDTH {
                                    state[HASH_IND + i] = BaseElement::ZERO;
                                }
                            }
                            //load attributes
                            for i in 0..HASH_DIGEST_WIDTH {

                                state[HASH_IND + i] = self.attributes[cert_index][2 * _cycle_num][i];
                                state[HASH_IND + HASH_DIGEST_WIDTH + i] = self.attributes[cert_index][2 * _cycle_num + 1][i];
                            }
                        } else if step_in_cert == hash_trace_lengths[cert_index] {
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
                                state[HASH_IND + i] = self.cred_nonce[cert_index][i - HASH_DIGEST_WIDTH];
                            }

                            //Clear capacity
                            for i in HASH_RATE_WIDTH..HASH_STATE_WIDTH {
                                state[HASH_IND + i] = BaseElement::ZERO;
                            }
                            
                        }
                    }

                    // Artifact of winterfell. Used to prevent constant polynomial when interpolating
                    if step==trace_padded_length-2 {
                        for i in 0..TRACE_WIDTH{
                            state[i] = BaseElement::new(123 as u32);
                        }
                    }
                }
                

                // print!("{}: ", step);
                // for i in 0..state.len() {
                //     print!("{} ", state[i]);
                // }
                // println!();
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
        let mut disclosed_attributes: Vec<Vec<[BaseElement; HASH_DIGEST_WIDTH]>> = vec![];
        for i in 0..self.disclosed_indices.len() {
            disclosed_attributes.push(Vec::new());
            for j in 0..self.disclosed_indices[i].len() {
                disclosed_attributes[i].push(self.attributes[i][self.disclosed_indices[i][j]]);
            }
        }
        let mut num_of_attributes = Vec::new();
        for i in 0.. self.attributes.len() {
            num_of_attributes.push(self.attributes[i].len());
        }
        PublicInputs{disclosed_attributes: disclosed_attributes, indices: self.disclosed_indices.clone(), num_of_attributes: num_of_attributes, num_of_user_attributes: self.num_of_user_attributes.clone(), comm: self.comm.clone(), cred_nonce: self.cred_nonce.clone()}
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