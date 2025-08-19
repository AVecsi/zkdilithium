use winterfell::{
    crypto::{hashers::Blake3_256, DefaultRandomCoin, MerkleTree}, matrix::ColMatrix, AuxRandElements, CompositionPoly, CompositionPolyTrace, ConstraintCompositionCoefficients, DefaultConstraintCommitment, DefaultConstraintEvaluator, DefaultTraceLde, PartitionOptions, StarkDomain, Trace, TraceInfo, TracePolyTable, TraceTable
};

use super::{
    BaseElement, DisclosureAir, FieldElement, ProofOptions, air::PublicInputs,
    Prover, HASH_CYCLE_LEN, HASH_DIGEST_WIDTH, HASH_RATE_WIDTH, HASH_STATE_WIDTH, STORAGE_START, NUM_HASH_ROUNDS
};

use crate::utils::poseidon_23_spec::{self};

pub struct DisclosureProver {
    options: ProofOptions,
    attributes: Vec<Vec<[BaseElement; HASH_DIGEST_WIDTH]>>,
    disclosed_indices: Vec<Vec<usize>>,
    merkle_comm: Vec<[BaseElement; HASH_RATE_WIDTH]>,
    secret_comm: [BaseElement; HASH_RATE_WIDTH],
    nonce: Vec<[BaseElement; 12]>,
    secret_nonce: [BaseElement; 12]
}

impl DisclosureProver {
    pub fn new(options: ProofOptions, attributes: Vec<Vec<[BaseElement; HASH_DIGEST_WIDTH]>>, disclosed_indices: Vec<Vec<usize>>, merkle_comm: Vec<[BaseElement; HASH_RATE_WIDTH]>, secret_comm: [BaseElement; HASH_RATE_WIDTH], nonce: Vec<[BaseElement; 12]>, secret_nonce: [BaseElement; 12]) -> Self {
        Self { options, attributes, disclosed_indices, merkle_comm, secret_comm, nonce, secret_nonce }
    }

    pub fn build_trace(&self) -> TraceTable<BaseElement> {
        //number of attributes must be power of 2

        let mut max_num_of_attributes = 0;
        for i in 0..self.attributes.len() {
            if self.attributes[i].len() > max_num_of_attributes {
                max_num_of_attributes = self.attributes[i].len();
            }
        }
        let trace_width = HASH_STATE_WIDTH*3 + (max_num_of_attributes.trailing_zeros() as usize)*HASH_DIGEST_WIDTH + HASH_DIGEST_WIDTH;

        let secret_commitment_length = HASH_CYCLE_LEN;
        let mut merkle_trace_lengths = Vec::new();
        let mut merkle_trace_lengths_sum = 0;

        for i in 0..self.attributes.len() {
            merkle_trace_lengths.push((self.attributes[i].len() as usize - 1) * HASH_CYCLE_LEN);
            merkle_trace_lengths_sum += merkle_trace_lengths[i];
        }
        
        let commitment_trace_length_sum = self.attributes.len()*HASH_CYCLE_LEN;

        //trace length must be power of 2
        let mut i = 32;
        //Added 2 because of the winterfell artifact at the end of trace
        while i < secret_commitment_length + merkle_trace_lengths_sum + commitment_trace_length_sum + 2 {
            i *= 2;
        }
        let trace_padded_length = i;

        let load_attribute_steps: Vec<usize> = leaf_steps_in_postorder(max_num_of_attributes - 1);

        let mut trace = TraceTable::new(trace_width, trace_padded_length);
        trace.fill(
            |state| {
                for i in 0..HASH_DIGEST_WIDTH {
                    state[i] = self.attributes[0][0][i];
                    state[i + HASH_DIGEST_WIDTH] = self.secret_nonce[i];
                    //TODO If the execution trace is changed it will break, unless it stays at the end
                    state[trace_width - HASH_DIGEST_WIDTH + i] = self.attributes[0][0][i];
                }
            },
            |step, state| {
                if step < secret_commitment_length {
                    if step % HASH_CYCLE_LEN > 0 {
                        poseidon_23_spec::apply_round(&mut state[0..(3*HASH_STATE_WIDTH)], step - 1);
                    }
                } else if step < secret_commitment_length + merkle_trace_lengths_sum + commitment_trace_length_sum {
                    let mut step_in_cert = step - secret_commitment_length;
                    let mut cert_index = 0;
                    for i in 0..merkle_trace_lengths.len()-1 {
                        if step_in_cert >= merkle_trace_lengths[i] + HASH_CYCLE_LEN {
                            cert_index += 1;
                            step_in_cert = step_in_cert - merkle_trace_lengths[i] - HASH_CYCLE_LEN;
                        }
                    }
                    let cycle_pos = step % HASH_CYCLE_LEN;

                    if step_in_cert == 0 {
                        //Init
                        for i in 0..HASH_DIGEST_WIDTH {
                            state[i] = self.attributes[cert_index][0][i];
                            state[HASH_DIGEST_WIDTH + i] = self.attributes[cert_index][1][i];
                        }
                        // Clean up the hash state
                        for i in HASH_RATE_WIDTH..HASH_STATE_WIDTH {
                            state[i] = BaseElement::ZERO;
                        }
                    } else if cycle_pos > 0 {
                        // apply poseidon round in all round of HASH_CYCLE, leave the init rounds in the trace
                        poseidon_23_spec::apply_round(&mut state[0..(3*HASH_STATE_WIDTH)], step-1);
                    } else if merkle_trace_lengths[cert_index] == step_in_cert {
                        // Init commitment
                        for i in 0..HASH_DIGEST_WIDTH {
                            state[i + HASH_DIGEST_WIDTH] = self.nonce[cert_index][i];
                        }

                        // Clean up the hash state
                        for i in HASH_RATE_WIDTH..HASH_STATE_WIDTH {
                            state[i] = BaseElement::ZERO;
                        }
                    } else {
                        let _cycle_num = (step_in_cert + 1) / HASH_CYCLE_LEN;
                        //After the hashing steps, it's time to move some data

                        //Shift storage (shifting and load to beginning makes our job easier with the transition constraints).
                        for i in (STORAGE_START..trace_width-2*HASH_DIGEST_WIDTH).rev() {
                            state[i+HASH_DIGEST_WIDTH] = state[i];
                        }

                        //Move hash result to the beginning of storage.
                        for i in 0..HASH_DIGEST_WIDTH {
                            state[STORAGE_START + i] = state[i];
                        }

                        //Determine if we need to load attributes
                        let mut index = 0;
                        for i in 0..load_attribute_steps.len() {
                            if load_attribute_steps[i] == _cycle_num {
                                index = i;
                                break;
                            }
                        }
                        //self.load_attribute_steps.contains(&_cycle_num)
                        if index != 0 {
                            //Load two attributes to hash space
                            for i in 0..HASH_DIGEST_WIDTH {
                                state[i] = self.attributes[cert_index][index * 2][i];
                                state[HASH_DIGEST_WIDTH + i] = self.attributes[cert_index][index * 2 + 1][i];
                            }
                        } else {
                            //Move two elements from storage to hash space
                            for i in 0..HASH_DIGEST_WIDTH {
                                state[i] = state[STORAGE_START + HASH_DIGEST_WIDTH + i];
                                state[HASH_DIGEST_WIDTH + i] = state[STORAGE_START + i];
                            }

                            //Shift the storage data
                            for i in STORAGE_START..trace_width-3*HASH_DIGEST_WIDTH {
                                state[i] = state[i + 2*HASH_DIGEST_WIDTH];
                            }

                            // Clean up the end of storage
                            //for i in 0..2*HASH_DIGEST_WIDTH {
                            //    state[trace_width - 1 - i] = BaseElement::ZERO;
                            //}
                        }
                        // Clean up the hash state
                        for i in HASH_RATE_WIDTH..HASH_STATE_WIDTH {
                            state[i] = BaseElement::ZERO;
                        }
                    }
                }

                // Artifact of winterfell. Used to prevent constant polynomial when interpolating
                if step==trace_padded_length-2 {
                    for i in 0..trace_width{
                        state[i] = BaseElement::new(123 as u32);
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
        PublicInputs{disclosed_attributes: disclosed_attributes, indices: self.disclosed_indices.clone(), num_of_attributes: num_of_attributes, merkle_comm: self.merkle_comm.clone(), secret_comm: self.secret_comm.clone(), nonce: self.nonce.clone(), secret_nonce: self.secret_nonce}
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
}


fn postorder_traversal(n: usize, nodes: &[usize]) -> Vec<usize> {
    // Simulates postorder traversal of a tree with nodes.
    if n > nodes.len() {
        // Base case: If the node doesn't exist, return empty
        return vec![];
    }
    // Recursive calls for left and right children
    let left = postorder_traversal(2 * n, nodes);
    let right = postorder_traversal(2 * n + 1, nodes);

    // Current node last (postorder)
    [left, right, vec![nodes[n - 1]]].concat()
}

fn leaf_steps_in_postorder(num_nodes: usize) -> Vec<usize> {
    // Step 1: Generate node indices for a fully balanced binary tree
    let nodes: Vec<usize> = (1..=num_nodes).collect();

    // Step 2: Simulate postorder traversal
    let postorder = postorder_traversal(1, &nodes);

    // Step 3: Identify leaves (indices from 2^(h-1) to 2^h - 1)
    let leaf_start = (num_nodes + 1) / 2;
    let leaf_end = num_nodes + 1;
    let leaf_nodes: Vec<usize> = (leaf_start..leaf_end).collect();

    // Step 4: Find steps where leaf nodes appear in the postorder sequence
    postorder
        .iter()
        .enumerate()
        .filter_map(|(i, &node)| if leaf_nodes.contains(&node) { Some(i) } else { None })
        .collect()
}
