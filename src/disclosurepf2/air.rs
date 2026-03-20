use winter_utils::Serializable;
use winterfell::{
    math::ToElements, Air, AirContext, Assertion, ByteWriter, EvaluationFrame, TraceInfo, TransitionConstraintDegree
};

use super::{BaseElement, FieldElement, ProofOptions, HASH_CYCLE_LEN, HASH_DIGEST_WIDTH, HASH_RATE_WIDTH, HASH_STATE_WIDTH};
use crate::{disclosurepf2::{DisclosureInputs, FIRST_ATTR_IND, HASH_IND, STORAGE_IND}, utils::{EvaluationResult, poseidon_23_spec}};

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
    pub disclosures: Vec<DisclosureInputs>
}

impl ToElements<BaseElement> for PublicInputs {
    fn to_elements(&self) -> Vec<BaseElement> {
        let mut elements = Vec::new();

        for disclosure in &self.disclosures {
            for hash in &disclosure.disclosed_attributes {
                elements.extend_from_slice(hash);
            }

            for index in &disclosure.indices {
                elements.push(BaseElement::from(*index as u64));
            }

            elements.push(BaseElement::from(disclosure.num_of_attributes as u64));

            elements.push(BaseElement::from(disclosure.num_of_user_attributes as u64));

            elements.extend_from_slice(&disclosure.salted_hash);
        }

        elements
    }
}


impl Serializable for PublicInputs {
    fn write_into<W: ByteWriter>(&self, _target: &mut W) {
        
    }
}

pub struct DisclosureAir {
    context: AirContext<BaseElement>,
    disclosures: Vec<DisclosureInputs>
}

impl Air for DisclosureAir {
    type BaseField = BaseElement;
    type PublicInputs = PublicInputs;

    // CONSTRUCTOR
    // --------------------------------------------------------------------------------------------
    fn new(trace_info: TraceInfo, pub_inputs: Self::PublicInputs, options: ProofOptions) -> Self {
 
        let mut degrees = Vec::new();

        //degrees.append(&mut vec![TransitionConstraintDegree::new(1); HASH_DIGEST_WIDTH]); //secret attr
        degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(1, vec![trace_info.length()]); HASH_DIGEST_WIDTH]); //secret attr
        degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(1, vec![trace_info.length()]); HASH_DIGEST_WIDTH]); //storage
        degrees.append(&mut vec![TransitionConstraintDegree::with_cycles(3, vec![trace_info.length()]); 6*HASH_STATE_WIDTH]); //hash_space

        let trace_length = trace_info.length();

        //68 assertions on each disclosed credentials
        let num_assertions = pub_inputs.disclosures.len() * 56;
        DisclosureAir {
            context: AirContext::new(
                trace_info, 
                degrees, 
                num_assertions,
                 options
            ).set_num_transition_exemptions(trace_length / 2),
            disclosures: pub_inputs.disclosures
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
        let hashcopy_flag = periodic_values[1];
        let cred_hash_copy_flag = periodic_values[2];
        let first_attribute_flag= periodic_values[3];
        let storage_flag = periodic_values[4];
        let final_attr_hash_flag = periodic_values[5];

        let even_attr_load_flag = periodic_values[6];
        let even_attr_load_value = &periodic_values[7..7+HASH_DIGEST_WIDTH];
        let odd_attr_load_flag = periodic_values[7+HASH_DIGEST_WIDTH];
        let odd_attr_load_value = &periodic_values[8+HASH_DIGEST_WIDTH..8+2*HASH_DIGEST_WIDTH];

        let even_attr_load_first_flag = periodic_values[8+2*HASH_DIGEST_WIDTH];
        let odd_attr_load_first_flag = periodic_values[9+2*HASH_DIGEST_WIDTH];

        let ark = &periodic_values[10+2*HASH_DIGEST_WIDTH..];
        
        // Assert the poseidon round was computed correctly was computed correctly whenever a permutation needs to be applied
        assert_hash(&mut result[HASH_IND..HASH_IND + 6*HASH_STATE_WIDTH],
            &current[HASH_IND..HASH_IND + 3*HASH_STATE_WIDTH],
            &next[HASH_IND..HASH_IND + 3*HASH_STATE_WIDTH],
            &ark,
            hashmask_flag
        );

        // Assert that the hash_capacity was copied correctly at the end of each round
        assert_hash_copy(&mut result[HASH_IND..(HASH_IND+6*HASH_STATE_WIDTH)],
            &current[HASH_IND..(HASH_IND+3*HASH_STATE_WIDTH)],
            &next[HASH_IND..(HASH_IND+3*HASH_STATE_WIDTH)],
            &ark[0..3*HASH_STATE_WIDTH],
            hashcopy_flag
        );

        //Assert the user hash was stored correctly
        for i in 0..HASH_DIGEST_WIDTH {
            result.agg_constraint(STORAGE_IND + i, storage_flag, next[STORAGE_IND + i] - current[HASH_IND + i]);
        }

        //Assert the storage is copied correctly
        for i in 0..HASH_DIGEST_WIDTH {
            result.agg_constraint(STORAGE_IND + i, E::ONE - storage_flag, next[STORAGE_IND + i] - current[STORAGE_IND + i]);
        }

        //Assert the issuer hash is moved correctly
        for i in 0..HASH_DIGEST_WIDTH {
            result.agg_constraint(HASH_IND + HASH_DIGEST_WIDTH + i, final_attr_hash_flag, next[HASH_IND + HASH_DIGEST_WIDTH + i] - current[HASH_IND + i]);
        }

        //Assert the stored user hash is moved correctly
        for i in 0..HASH_DIGEST_WIDTH {
            result.agg_constraint(HASH_IND + i, final_attr_hash_flag, next[HASH_IND + i] - current[STORAGE_IND + i]);
        }

        //Assert the cred hash was copied correctly
        for i in 0..HASH_DIGEST_WIDTH {
            result.agg_constraint(HASH_IND + i, cred_hash_copy_flag, next[HASH_IND + i] - current[HASH_IND + i]);
        }

        //Assert that the first attribute of each cert is the same with the one stored
        for i in 0..HASH_DIGEST_WIDTH {
            result.agg_constraint(FIRST_ATTR_IND + i, first_attribute_flag, current[HASH_IND + i] - current[FIRST_ATTR_IND+i]);
        }

        //Assert that the attribute stored is copied correctly
        for i in FIRST_ATTR_IND..FIRST_ATTR_IND+HASH_DIGEST_WIDTH {
            result[i] += next[i] - current[i];
        }

        //Assert that the disclosed attributes were loaded to the hash space on the correct step, correctly
        //First attribute logic
        for i in 0..HASH_DIGEST_WIDTH{
            result.agg_constraint(HASH_IND + i, even_attr_load_first_flag, next[HASH_IND + i] - even_attr_load_value[i]);
        }

        for i in 0..HASH_DIGEST_WIDTH{
            result.agg_constraint(HASH_IND + HASH_DIGEST_WIDTH + i, odd_attr_load_first_flag, next[HASH_IND + HASH_DIGEST_WIDTH + i] - odd_attr_load_value[i]);
        }

        //Following attribute logic
        for i in 0..HASH_DIGEST_WIDTH{
            result.agg_constraint(HASH_IND + i, even_attr_load_flag, next[HASH_IND + i] - (current[HASH_IND + i] + even_attr_load_value[i]));
        }

        for i in 0..HASH_DIGEST_WIDTH{
            result.agg_constraint(HASH_IND + HASH_DIGEST_WIDTH + i, odd_attr_load_flag, next[HASH_IND + HASH_DIGEST_WIDTH + i] - (current[HASH_IND + HASH_DIGEST_WIDTH + i] + odd_attr_load_value[i]));
        }


    }

    fn get_assertions(&self) -> Vec<Assertion<Self::BaseField>> {
        let mut main_assertions = Vec::new();

        let mut steps_done = 1;
        for cert_index in 0..self.disclosures.len() {
            //Assert that the capacity is clean at the start of the user hashing 0-11
            for i in HASH_RATE_WIDTH..HASH_STATE_WIDTH {
                main_assertions.push(Assertion::single(HASH_IND + i, steps_done, BaseElement::ZERO));
            }

            //Assert that the capacity is cleaned at the start of issuer hashing 11-22
            //TODO is it the right step?
            for i in HASH_RATE_WIDTH..HASH_STATE_WIDTH {
                main_assertions.push(Assertion::single(HASH_IND + i, steps_done + (self.disclosures[cert_index].num_of_user_attributes / 2 * HASH_CYCLE_LEN), BaseElement::ZERO));
            }

            //Assert that the capacity was cleaned up before final hash 22-33
            for i in HASH_RATE_WIDTH..HASH_STATE_WIDTH {
                main_assertions.push(Assertion::single(HASH_IND + i, steps_done + (self.disclosures[cert_index].num_of_attributes / 2 * HASH_CYCLE_LEN), BaseElement::ZERO));
            }

            //Assert that the capacity was cleaned up correctly before salted hash 33-44
            for i in HASH_RATE_WIDTH..HASH_STATE_WIDTH {
                main_assertions.push(Assertion::single(HASH_IND + i, steps_done + (self.disclosures[cert_index].num_of_attributes / 2 * HASH_CYCLE_LEN) + HASH_CYCLE_LEN, BaseElement::ZERO));
            }

            //Assert the final result is the given hash 44-56
            for i in 0..HASH_DIGEST_WIDTH {
                main_assertions.push(Assertion::single(HASH_IND + i, steps_done + (self.disclosures[cert_index].num_of_attributes / 2 * HASH_CYCLE_LEN) + 2*HASH_CYCLE_LEN - 1, self.disclosures[cert_index].salted_hash[i]));
            }

            steps_done += (self.disclosures[cert_index].num_of_attributes / 2 * HASH_CYCLE_LEN) + HASH_CYCLE_LEN + HASH_CYCLE_LEN;
        }

        main_assertions
    }

    fn get_periodic_column_values(&self) -> Vec<Vec<Self::BaseField>> {
        let mut result = Vec::new();
        let padded_trace_length = self.trace_length();
        result.push(get_hashmask_constants(padded_trace_length, &self.disclosures));
        result.push(get_hashcopy_constants(padded_trace_length, &self.disclosures));
        result.push(cred_hash_copy_flag_constants(padded_trace_length, &self.disclosures));
        result.push(get_first_attribute_constants(padded_trace_length, &self.disclosures));
        result.push(get_storage_constants(padded_trace_length, &self.disclosures));
        result.push(get_final_attr_hash_constants(padded_trace_length, &self.disclosures));
        result.append(&mut get_even_attr_load_constants(padded_trace_length, &self.disclosures));
        result.append(&mut get_odd_attr_load_constants(padded_trace_length, &self.disclosures));
        result.push(get_even_attr_load_first_constant(padded_trace_length, &self.disclosures));
        result.push(get_odd_attr_load_first_constant(padded_trace_length, &self.disclosures));

        let singleark = poseidon_23_spec::get_round_constants();
        let mut ark: Vec<Vec<BaseElement>> = vec![vec![BaseElement::ZERO; padded_trace_length]; 3*HASH_STATE_WIDTH];
        
        for i in 1..padded_trace_length {
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

fn get_hashmask_constants(padded_trace_length: usize, disclosures: &Vec<DisclosureInputs>) -> Vec<BaseElement> {
    let mut hashmask_const = vec![BaseElement::ZERO; padded_trace_length];
    
    let mut trace_length = 0;
    for disclosure in disclosures {
        trace_length += disclosure.num_of_attributes / 2 * HASH_CYCLE_LEN + 2*HASH_CYCLE_LEN;
    }

    //TODO to trace_length is fine?
    for i in 1..trace_length{
        hashmask_const[i] = HASH_CYCLE_MASK[(i - 1)%HASH_CYCLE_LEN];
    }

    hashmask_const
}

//When to copy the capacity
fn get_hashcopy_constants(padded_trace_length: usize, disclosures: &Vec<DisclosureInputs>) -> Vec<BaseElement> {
    let mut hashcopy_const = vec![BaseElement::ZERO; padded_trace_length];

    let mut trace_position = 0;
    for disclosure in disclosures {

        for j in 1..disclosure.num_of_user_attributes / 2 * HASH_CYCLE_LEN {
            hashcopy_const[trace_position + j] = BaseElement::ONE - HASH_CYCLE_MASK[(j - 1)%HASH_CYCLE_LEN];
        }

        for j in 1 + disclosure.num_of_user_attributes / 2 * HASH_CYCLE_LEN..disclosure.num_of_attributes / 2 * HASH_CYCLE_LEN {
            hashcopy_const[trace_position + j] = BaseElement::ONE - HASH_CYCLE_MASK[(j - 1)%HASH_CYCLE_LEN];
        }

        trace_position += disclosure.num_of_attributes / 2 * HASH_CYCLE_LEN;
        trace_position += 2*HASH_CYCLE_LEN;
    }

    hashcopy_const
}

//When to copy the the result of the hash to be randomized
fn cred_hash_copy_flag_constants(padded_trace_length: usize, disclosures: &Vec<DisclosureInputs>) -> Vec<BaseElement> {
    let mut cred_hash_copy_const = vec![BaseElement::ZERO; padded_trace_length];
    
    let mut trace_position = 0;
    for disclosure in disclosures {
        trace_position += (disclosure.num_of_attributes / 2 * HASH_CYCLE_LEN) + HASH_CYCLE_LEN;
        cred_hash_copy_const[trace_position] = BaseElement::ONE;

        //Set the counter to the beginning of the next cert
        trace_position += HASH_CYCLE_LEN;
    }

    cred_hash_copy_const
}

//When is the first attribute of a credential is loaded
fn get_first_attribute_constants(padded_trace_length: usize, disclosures: &Vec<DisclosureInputs>) -> Vec<BaseElement> {
    let mut first_attribute_copy_const = vec![BaseElement::ZERO; padded_trace_length];
    
    let mut trace_position = 1;
    for disclosure in disclosures {
        first_attribute_copy_const[trace_position] = BaseElement::ONE;

        trace_position += (disclosure.num_of_attributes / 2 * HASH_CYCLE_LEN) + 2*HASH_CYCLE_LEN;
    }

    first_attribute_copy_const
}

//When to move the result of user attrs hash to storage
fn get_storage_constants(padded_trace_length: usize, disclosures: &Vec<DisclosureInputs>) -> Vec<BaseElement> {
    let mut storage_const = vec![BaseElement::ZERO; padded_trace_length];
    
    let mut trace_position = 0;
    for disclosure in disclosures {

        storage_const[trace_position + (disclosure.num_of_user_attributes / 2 * HASH_CYCLE_LEN)] = BaseElement::ONE;

        trace_position += (disclosure.num_of_attributes / 2 * HASH_CYCLE_LEN) + 2*HASH_CYCLE_LEN;
    }

    storage_const
}

//When to hash the two intermediate results
fn get_final_attr_hash_constants(padded_trace_length: usize, disclosures: &Vec<DisclosureInputs>) -> Vec<BaseElement> {
    let mut final_attr_hash_const = vec![BaseElement::ZERO; padded_trace_length];
    
    let mut trace_position = 0;
    for disclosure in disclosures {

        trace_position += disclosure.num_of_attributes / 2 * HASH_CYCLE_LEN;

        final_attr_hash_const[trace_position] = BaseElement::ONE;

        trace_position += 2*HASH_CYCLE_LEN;
    }

    final_attr_hash_const
}

fn get_even_attr_load_constants(padded_trace_length: usize, disclosures: &Vec<DisclosureInputs>) -> Vec<Vec<BaseElement>> {
    let mut even_attr_load_const = Vec::new();

    for _ in 0..HASH_DIGEST_WIDTH + 1 {
        even_attr_load_const.push(vec![BaseElement::ZERO; padded_trace_length]);
    }

    let mut trace_position = 0;
    for disclosure in disclosures {

        for j in 0..disclosure.indices.len(){
            if disclosure.indices[j] % 2 == 0 {
                if disclosure.indices[j] != disclosure.num_of_user_attributes {
                
                    even_attr_load_const[0][trace_position + (disclosure.indices[j] / 2) * HASH_CYCLE_LEN] = BaseElement::ONE
                }

                //Loading all the disclosed attributes the first too.
                for k in 0..HASH_DIGEST_WIDTH {
                    even_attr_load_const[k+1][trace_position + (disclosure.indices[j] / 2) * HASH_CYCLE_LEN] = disclosure.disclosed_attributes[j][k]
                }
            }
        }

        trace_position += disclosure.num_of_attributes / 2 * HASH_CYCLE_LEN + 2*HASH_CYCLE_LEN;
    }

    return even_attr_load_const
}

fn get_odd_attr_load_constants(padded_trace_length: usize, disclosures: &Vec<DisclosureInputs>) -> Vec<Vec<BaseElement>> {
    let mut odd_attr_load_const = Vec::new();

    for _ in 0..HASH_DIGEST_WIDTH + 1 {
        odd_attr_load_const.push(vec![BaseElement::ZERO; padded_trace_length]);
    }

    let mut trace_position = 0;
    for disclosure in disclosures {

        for j in 0..disclosure.indices.len(){
             if disclosure.indices[j] % 2 == 1 {
                if disclosure.indices[j] != disclosure.num_of_user_attributes + 1 {
                
                    odd_attr_load_const[0][trace_position + (disclosure.indices[j] / 2) * HASH_CYCLE_LEN] = BaseElement::ONE
                }

                //Loading all the disclosed attributes the first too.
                for k in 0..HASH_DIGEST_WIDTH {
                    odd_attr_load_const[k+1][trace_position + (disclosure.indices[j] / 2) * HASH_CYCLE_LEN] = disclosure.disclosed_attributes[j][k]
                }
            }
        }

        trace_position += disclosure.num_of_attributes / 2 * HASH_CYCLE_LEN + 2*HASH_CYCLE_LEN;
    }

    return odd_attr_load_const
}

fn get_even_attr_load_first_constant(padded_trace_length: usize, disclosures: &Vec<DisclosureInputs>) -> Vec<BaseElement> {
    let mut even_attr_load_first_const = vec![BaseElement::ZERO; padded_trace_length];

    let mut trace_position = 0;
   for disclosure in disclosures {

        for j in 0..disclosure.indices.len(){
            if disclosure.indices[j] == disclosure.num_of_user_attributes {
                if disclosure.indices[j] % 2 == 0 {
                    even_attr_load_first_const[trace_position + (disclosure.indices[j] / 2) * HASH_CYCLE_LEN] = BaseElement::ONE
                }
            }
        }

        trace_position += disclosure.num_of_attributes / 2 * HASH_CYCLE_LEN + 2*HASH_CYCLE_LEN;
    }

    return even_attr_load_first_const
}

fn get_odd_attr_load_first_constant(padded_trace_length: usize, disclosures: &Vec<DisclosureInputs>) -> Vec<BaseElement> {
    let mut odd_attr_load_first_const = vec![BaseElement::ZERO; padded_trace_length];

    let mut trace_position = 0;
    for disclosure in disclosures {

        for j in 0..disclosure.indices.len(){
            if disclosure.indices[j] == disclosure.num_of_user_attributes + 1 {
                if disclosure.indices[j] % 2 == 1 {
                    odd_attr_load_first_const[trace_position + (disclosure.indices[j] / 2) * HASH_CYCLE_LEN] = BaseElement::ONE
                }
            }
        }

        trace_position += disclosure.num_of_attributes / 2 * HASH_CYCLE_LEN + 2*HASH_CYCLE_LEN;
    }

    return odd_attr_load_first_const
}