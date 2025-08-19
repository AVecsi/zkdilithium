// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use winter_utils::Serializable;
use winterfell::{
    math::ToElements, Air, AirContext, Assertion, ByteWriter, EvaluationFrame, TraceInfo, TransitionConstraintDegree
};

use super::{BaseElement, FieldElement, ProofOptions, HASH_CYCLE_LEN, HASH_DIGEST_WIDTH, HASH_RATE_WIDTH, HASH_STATE_WIDTH, STORAGE_START};
use crate::utils::{EvaluationResult, is_binary, poseidon_23_spec, are_equal};

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
    pub disclosed_attributes: Vec<Vec<[BaseElement; HASH_DIGEST_WIDTH]>>,
    pub indices: Vec<Vec<usize>>,
    pub num_of_attributes: Vec<usize>,
    pub merkle_comm: Vec<[BaseElement; HASH_RATE_WIDTH]>,
    pub secret_comm: [BaseElement; HASH_RATE_WIDTH],
    pub nonce: Vec<[BaseElement; 12]>,
    pub secret_nonce: [BaseElement; 12]
}

impl ToElements<BaseElement> for PublicInputs {
    fn to_elements(&self) -> Vec<BaseElement> {
        let mut elements = Vec::new();

        // Flatten disclosed_attributes: Vec<Vec<[BaseElement; HASH_DIGEST_WIDTH]>>
        for attr_list in &self.disclosed_attributes {
            for hash in attr_list {
                elements.extend_from_slice(hash);
            }
        }

        // Convert indices: Vec<Vec<usize>> to BaseElements
        for group in &self.indices {
            for &index in group {
                elements.push(BaseElement::from(index as u64));
            }
        }

        // Convert num_of_attributes: Vec<usize>
        for &num in &self.num_of_attributes {
            elements.push(BaseElement::from(num as u64));
        }

        // Flatten merkle_comm: Vec<[BaseElement; HASH_RATE_WIDTH]>
        for comm in &self.merkle_comm {
            elements.extend_from_slice(comm);
        }

        // Flatten secret_comm: [BaseElement; HASH_RATE_WIDTH]
        elements.extend_from_slice(&self.secret_comm);

        // Flatten nonce: Vec<[BaseElement; 12]>
        for nonce in &self.nonce {
            elements.extend_from_slice(nonce);
        }

        // Flatten secret_nonce: [BaseElement; 12]
        elements.extend_from_slice(&self.secret_nonce);

        elements
    }
}


impl Serializable for PublicInputs {
    fn write_into<W: ByteWriter>(&self, _target: &mut W) {
        // target.write(&self.ctilde[..]);
        for i in 0..self.nonce.len() {
            for j in 0..self.nonce[i].len() {
                _target.write(self.nonce[i][j]);
            }
        }
        for i in 0..self.secret_nonce.len() {
            _target.write(self.secret_nonce[i]);
        }
    }
}

pub struct DisclosureAir {
    context: AirContext<BaseElement>,
    disclosed_attributes: Vec<Vec<[BaseElement; HASH_DIGEST_WIDTH]>>,
    disclosed_indices: Vec<Vec<usize>>,
    num_of_attributes: Vec<usize>,
    merkle_comm: Vec<[BaseElement; HASH_RATE_WIDTH]>,
    secret_comm: [BaseElement; HASH_RATE_WIDTH],
    nonce: Vec<[BaseElement; 12]>,
    secret_nonce: [BaseElement; 12]
}

impl Air for DisclosureAir {
    type BaseField = BaseElement;
    type PublicInputs = PublicInputs;

    // CONSTRUCTOR
    // --------------------------------------------------------------------------------------------
    fn new(trace_info: TraceInfo, pub_inputs: Self::PublicInputs, options: ProofOptions) -> Self {
 
        let mut degrees = Vec::new();
        degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(3, vec![trace_info.length()]); 6*HASH_STATE_WIDTH]); //hash_space
        degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(1, vec![trace_info.length()]); trace_info.width()-HASH_DIGEST_WIDTH - STORAGE_START]); //storage

        let mut num_assertions = HASH_DIGEST_WIDTH + HASH_RATE_WIDTH;
        for i in 0..pub_inputs.disclosed_attributes.len() {
            num_assertions += pub_inputs.disclosed_attributes[i].len() * HASH_DIGEST_WIDTH;
            num_assertions += HASH_DIGEST_WIDTH + HASH_RATE_WIDTH;
        }
        for i in 0..pub_inputs.num_of_attributes.len() {
            num_assertions += (pub_inputs.num_of_attributes[i]) * (HASH_STATE_WIDTH-HASH_RATE_WIDTH)
        }
        DisclosureAir {
            context: AirContext::new(
                trace_info, 
                degrees, 
                num_assertions,
                 options
            ).set_num_transition_exemptions(2),
            disclosed_attributes: pub_inputs.disclosed_attributes,
            disclosed_indices: pub_inputs.indices,
            num_of_attributes: pub_inputs.num_of_attributes,
            merkle_comm: pub_inputs.merkle_comm,
            secret_comm: pub_inputs.secret_comm,
            nonce: pub_inputs.nonce,
            secret_nonce: pub_inputs.secret_nonce
        }
    }

    fn context(&self) -> &AirContext<Self::BaseField> {
        &self.context
    }

    fn evaluate_transition<E: FieldElement + From<Self::BaseField>>(
        &self,
        frame: &EvaluationFrame<E>,
        periodic_values: &[E],
        result: &mut [E],
    ) {
        let current = frame.current();
        let next = frame.next();

        debug_assert_eq!(self.trace_info().width(), current.len());
        debug_assert_eq!(self.trace_info().width(), next.len());

        let hashmask_flag = periodic_values[0];
        let move_to_storage_flag = periodic_values[1];
        let move_from_storage_flag = periodic_values[2];
        let merkle_root_copy_flag = periodic_values[3];
        let first_attribute_flag= periodic_values[4];
        let ark = &periodic_values[5..];
        
        // Assert the poseidon round was computed correctly was computed correctly whenever a permutation needs to be applied
        assert_hash(&mut result[0..6*HASH_STATE_WIDTH],
            &current[0..3*HASH_STATE_WIDTH],
            &next[0..3*HASH_STATE_WIDTH],
            &ark,
            hashmask_flag
        );

        //Assert the storage is copied correctly in every hashing steps
        for i in STORAGE_START..self.trace_info().width()-HASH_DIGEST_WIDTH {
            result.agg_constraint(6*HASH_STATE_WIDTH + i - STORAGE_START, hashmask_flag, next[i] - current[i]);
        }

        //Assert the new hash was stored correctly on every attribute load steps
        for i in STORAGE_START..STORAGE_START+HASH_DIGEST_WIDTH {
            result.agg_constraint(6*HASH_STATE_WIDTH + i - STORAGE_START, move_to_storage_flag, next[i] - current[i - STORAGE_START]);
        }

        //Assert the storage was shifted correctly on every attribute load steps
        for i in STORAGE_START+HASH_DIGEST_WIDTH..self.trace_info().width()-HASH_DIGEST_WIDTH {
            result.agg_constraint(6*HASH_STATE_WIDTH + i - STORAGE_START, move_to_storage_flag, next[i] - current[i - HASH_DIGEST_WIDTH]);
        }

        //Assert on the load from storage steps, the correct data is loaded from storage
        for i in STORAGE_START..STORAGE_START+HASH_DIGEST_WIDTH {
            result.agg_constraint(6*HASH_STATE_WIDTH + i - STORAGE_START, move_from_storage_flag, next[i - STORAGE_START] - current[i]);
        }

        //Assert on load from storage steps, the last hash result was copied correctly
        for i in 0..HASH_DIGEST_WIDTH {
            result.agg_constraint(i, move_from_storage_flag, next[i+HASH_DIGEST_WIDTH] - current[i]);
        }

        //Assert the storage was shifted correctly on every load from storage steps
        for i in STORAGE_START..self.trace_info().width() - 3*HASH_DIGEST_WIDTH {
            result.agg_constraint(6*HASH_STATE_WIDTH + i - STORAGE_START, move_from_storage_flag, next[i] - current[i + HASH_DIGEST_WIDTH]);
        }

        //Assert the merkle root was copied correctly
        for i in 0..HASH_DIGEST_WIDTH {
            result.agg_constraint(i, merkle_root_copy_flag, next[i] - current[i]);
        }

        //Assert that the attribute stored at the end is copied correctly
        for i in self.trace_info().width()-HASH_DIGEST_WIDTH..self.trace_info().width() {
            result[i] += next[i] - current[i];
        }

        //Assert that the first attribute of each cert is the same the one stored at the end of the trace
        for i in 0..HASH_DIGEST_WIDTH {
            result.agg_constraint(i, first_attribute_flag, current[i] - current[self.trace_info().width()-HASH_DIGEST_WIDTH+i]);
        }

    }

    fn get_assertions(&self) -> Vec<Assertion<Self::BaseField>> {
        let mut main_assertions = Vec::new();

        //Assert that the secret_nonce in the commitment is correct
        for i in 0..HASH_DIGEST_WIDTH {
            main_assertions.push(Assertion::single(i + HASH_DIGEST_WIDTH, 1, self.secret_nonce[i]));
        }

        //Assert that the secret_comm was computed correctly
        for i in 0..HASH_RATE_WIDTH {
            main_assertions.push(Assertion::single(i, HASH_CYCLE_LEN, self.secret_comm[i]));
        }

        let mut steps_done = HASH_CYCLE_LEN;
        for cert_index in 0..self.disclosed_attributes.len() {
            //Assert that the disclosed attributes were loaded to the hash space on the correct step
            let highest_disclosed_index = self.disclosed_indices[cert_index][self.disclosed_indices[cert_index].len() - 1];
            let mut i = 1;
            while i <= highest_disclosed_index {
                i *= 2;
            }
            let load_attribute_steps = leaf_steps_in_postorder(i - 1);
            
            let mut j = 0;
            for (i, step) in load_attribute_steps.iter().enumerate() {
                //i*2th and i*2+1th attributes are loaded in step
                if self.disclosed_indices[cert_index].contains(&(i*2)) {
                    for k in 0..HASH_DIGEST_WIDTH{
                        main_assertions.push(Assertion::single(k, steps_done+step*HASH_CYCLE_LEN + 1, self.disclosed_attributes[cert_index][j][k]));
                    }
                    j += 1;
                }

                if self.disclosed_indices[cert_index].contains(&(i*2 + 1)) {
                    for k in HASH_DIGEST_WIDTH..2*HASH_DIGEST_WIDTH{
                        main_assertions.push(Assertion::single(k, steps_done+step*HASH_CYCLE_LEN + 1, self.disclosed_attributes[cert_index][j][k - HASH_DIGEST_WIDTH]));
                    }
                    j += 1;
                }
            }

            //Assert that the nonce in the commitment is correct
            for i in 0..HASH_DIGEST_WIDTH {
                main_assertions.push(Assertion::single(i + HASH_DIGEST_WIDTH, steps_done+(self.num_of_attributes[cert_index] - 1) * HASH_CYCLE_LEN + 1, self.nonce[cert_index][i]));
            }

            //Assert the final result is the given commitment
            for i in 0..HASH_RATE_WIDTH {
                main_assertions.push(Assertion::single(i, steps_done+(self.num_of_attributes[cert_index]) * HASH_CYCLE_LEN, self.merkle_comm[cert_index][i]));
            }

            //Assert that the hash rate was cleaned up correctly
            for i in 0..self.num_of_attributes[cert_index] {
                for k in HASH_RATE_WIDTH..HASH_STATE_WIDTH {
                    main_assertions.push(Assertion::single(k, steps_done+i as usize * HASH_CYCLE_LEN + 1, BaseElement::ZERO));
                }
            }

            steps_done += (self.num_of_attributes[cert_index] as usize) * HASH_CYCLE_LEN;
        }

        main_assertions
    }

    fn get_periodic_column_values(&self) -> Vec<Vec<Self::BaseField>> {
        let mut result = Vec::new();
        let padded_trace_length = self.trace_length();
        result.push(get_hashmask_constants(padded_trace_length, self.num_of_attributes.clone()));
        result.push(get_move_to_storage_constants(padded_trace_length, self.num_of_attributes.clone()));
        result.push(get_move_from_storage_constants(padded_trace_length, self.num_of_attributes.clone()));
        result.push(get_merkle_root_copy_constants(padded_trace_length, self.num_of_attributes.clone()));
        result.push(get_first_attribute_copy_constants(padded_trace_length, self.num_of_attributes.clone()));

        let singleark = poseidon_23_spec::get_round_constants();
        let mut ark: Vec<Vec<BaseElement>> = vec![vec![BaseElement::ZERO; padded_trace_length]; 3*HASH_STATE_WIDTH];;
        
        for i in (1..padded_trace_length) {
            for j in 0..3*HASH_STATE_WIDTH {
                ark[j][i] = singleark[j][(i-1)%HASH_CYCLE_LEN]
            }
        }
        result.append(&mut ark);

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

fn get_hashmask_constants(padded_trace_length: usize, num_of_attributes: Vec<usize>) -> Vec<BaseElement> {
    let mut hashmask_const = vec![BaseElement::ZERO; padded_trace_length];
    
    let mut trace_length = 0;
    for i in 0..num_of_attributes.len() {
        trace_length += (num_of_attributes[i] as usize) * HASH_CYCLE_LEN;
    }

    for i in 1..HASH_CYCLE_LEN + trace_length{
        hashmask_const[i] = HASH_CYCLE_MASK[(i - 1)%HASH_CYCLE_LEN];
    }

    hashmask_const
}

fn get_move_to_storage_constants(padded_trace_length: usize, num_of_attributes: Vec<usize>) -> Vec<BaseElement> {
    let mut move_to_storage_const = vec![BaseElement::ZERO; padded_trace_length];

    let mut steps_done = HASH_CYCLE_LEN;
    for i in 0..num_of_attributes.len() {

        let mut load_steps = leaf_steps_in_postorder(num_of_attributes[i] - 1);

        for j in 1..load_steps.len() {
            load_steps[j] = load_steps[j]*HASH_CYCLE_LEN;
        }

        let merkle_trace_length = (num_of_attributes[i] as usize - 1) * HASH_CYCLE_LEN;
        for j in (HASH_CYCLE_LEN..merkle_trace_length).step_by(HASH_CYCLE_LEN){
            if load_steps.contains(&j) {
                move_to_storage_const[steps_done+j] = BaseElement::ONE;
            }
        }
        //The extra addition is to skip the commitment steps
        steps_done += merkle_trace_length + HASH_CYCLE_LEN;
    }

    move_to_storage_const
}

fn get_move_from_storage_constants(padded_trace_length: usize, num_of_attributes: Vec<usize>) -> Vec<BaseElement> {
    let mut move_from_storage_const = vec![BaseElement::ZERO; padded_trace_length];
    
    let mut steps_done = HASH_CYCLE_LEN;
    for i in 0..num_of_attributes.len() {

        let mut load_steps = leaf_steps_in_postorder(num_of_attributes[i] - 1);

        for j in 1..load_steps.len() {
            load_steps[j] = load_steps[j]*HASH_CYCLE_LEN;
        }

        let merkle_trace_length = (num_of_attributes[i] as usize - 1) * HASH_CYCLE_LEN;
        for j in (HASH_CYCLE_LEN..merkle_trace_length).step_by(HASH_CYCLE_LEN){
            if !load_steps.contains(&j) {
                move_from_storage_const[steps_done+j] = BaseElement::ONE;
            }
        }
        //The extra addition is to skip the commitment steps
        steps_done += merkle_trace_length + HASH_CYCLE_LEN;
    }

    move_from_storage_const
}

fn get_merkle_root_copy_constants(padded_trace_length: usize, num_of_attributes: Vec<usize>) -> Vec<BaseElement> {
    let mut merkle_root_copy_const = vec![BaseElement::ZERO; padded_trace_length];
    
    let mut merkle_trace_end = HASH_CYCLE_LEN;
    for i in 0..num_of_attributes.len() {
        merkle_trace_end += (num_of_attributes[i] as usize - 1) * HASH_CYCLE_LEN;
        merkle_root_copy_const[merkle_trace_end] = BaseElement::ONE;

        //Set the counter to the beginning of the next cert
        merkle_trace_end += HASH_CYCLE_LEN;
    }

    merkle_root_copy_const
}

fn get_first_attribute_copy_constants(padded_trace_length: usize, num_of_attributes: Vec<usize>) -> Vec<BaseElement> {
    let mut first_attribute_copy_const = vec![BaseElement::ZERO; padded_trace_length];
    
    first_attribute_copy_const[0] = BaseElement::ONE;
    first_attribute_copy_const[HASH_CYCLE_LEN + 1] = BaseElement::ONE;
    let mut merkle_trace_begin = HASH_CYCLE_LEN + 1;
    for i in 0..num_of_attributes.len() - 1{
        //Set the counter to the beginning of the next cert
        merkle_trace_begin += (num_of_attributes[i] as usize) * HASH_CYCLE_LEN;
        first_attribute_copy_const[merkle_trace_begin] = BaseElement::ONE;
    }

    first_attribute_copy_const
}