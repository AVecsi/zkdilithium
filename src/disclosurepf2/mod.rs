// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use log::debug;
use rand_chacha::{rand_core::SeedableRng, ChaCha20Rng};
use std::{time::Instant};
use winterfell::{
    crypto::{DefaultRandomCoin, MerkleTree}, math::{fields::f23201::BaseElement, FieldElement, StarkField}, FieldExtension, MockPrng, Proof, ProofOptions, Prover, Trace, VerifierError
};

use crate::utils::poseidon_23_spec::{
    CYCLE_LENGTH as HASH_CYCLE_LEN, NUM_ROUNDS as NUM_HASH_ROUNDS,
    STATE_WIDTH as HASH_STATE_WIDTH, RATE_WIDTH as HASH_RATE_WIDTH,
    DIGEST_SIZE as HASH_DIGEST_WIDTH
};

mod air;
use air::DisclosureAir;

mod prover;
use prover::DisclosureProver;

use self::air::PublicInputs;

// CONSTANTS
// ================================================================================================

pub const FIRST_ATTR_IND: usize = 0;
pub const STORAGE_IND: usize = HASH_DIGEST_WIDTH;
//In future for bigger storage, extend here
pub const HASH_IND: usize = STORAGE_IND + HASH_DIGEST_WIDTH;

pub const HASHING_PHASE_START: usize = 0;

pub const TRACE_WIDTH: usize = HASH_IND + HASH_STATE_WIDTH*3;

pub type Blake3_256 = winterfell::crypto::hashers::Blake3_256<BaseElement>;

pub(crate) fn prove(
    mut attributes: Vec<Vec<[BaseElement; HASH_DIGEST_WIDTH]>>,
    num_of_user_attributes: Vec<usize>,
    disclosed_indices: Vec<Vec<usize>>,
    comm: Vec<[BaseElement; HASH_DIGEST_WIDTH]>,
    cred_nonce: Vec<[BaseElement; 12]>
) -> Proof {
        let options = ProofOptions::new(
            48, // number of queries
            4,  // blowup factor
            20,  // grinding factor
            FieldExtension::Sextic,
            8,   // FRI folding factor
            127, // FRI max remainder length
            winterfell::BatchingMethod::Linear, //TODO
            winterfell::BatchingMethod::Linear, //TODO
            false
        );
        debug!(
            "Generating proof for correctness of Disclosure tree"
        );

        for i in 0..attributes.len() {
            //Add padding attribute if needed
            if attributes[i].len() % 2 == 1 {
                attributes[i].push([BaseElement::ZERO; HASH_DIGEST_WIDTH]);
            }
        }

        // create a prover
        let now = Instant::now();
        //TODO assuming now that non of the attributes number are odd (padding already included if needed)
        let prover = DisclosureProver::new(options.clone(), attributes, num_of_user_attributes, disclosed_indices, comm, cred_nonce);

        // generate execution trace
        let trace = prover.build_trace();

        let trace_width = trace.width();
        let trace_length = trace.length();
        debug!(
            "Generated execution trace of {} registers and 2^{} steps in {} ms \n",
            trace_width,
            trace_length.ilog2(),
            now.elapsed().as_millis()
        );

        //let seed = ChaCha20Rng::from_entropy().get_seed();

        let seed = [0; 32].into();
        // generate the proof
        prover.prove(trace, Some(seed)).unwrap()
    }

pub(crate) fn verify(proof: Proof, disclosed_attributes: Vec<Vec<[BaseElement; HASH_DIGEST_WIDTH]>>, indices: Vec<Vec<usize>>, num_of_attributes: Vec<usize>, num_of_user_attributes: Vec<usize>, comm: Vec<[BaseElement; HASH_DIGEST_WIDTH]>, nonce: Vec<[BaseElement; 12]>) -> Result<(), VerifierError> {
    let pub_inputs = PublicInputs{disclosed_attributes, indices, num_of_attributes, num_of_user_attributes, comm, cred_nonce: nonce};
    let acceptable_options =
            winterfell::AcceptableOptions::OptionSet(vec![proof.options().clone()]);

    winterfell::verify::<DisclosureAir, Blake3_256, DefaultRandomCoin<Blake3_256>, MerkleTree<Blake3_256>>(
            proof,
            pub_inputs,
            &acceptable_options,
        )
}

pub(crate) fn verify_with_wrong_inputs(proof: Proof, disclosed_attributes: Vec<Vec<[BaseElement; HASH_DIGEST_WIDTH]>>, indices: Vec<Vec<usize>>, num_of_attributes: Vec<usize>, num_of_user_attributes: Vec<usize>, comm: Vec<[BaseElement; HASH_DIGEST_WIDTH]>, nonce: Vec<[BaseElement; 12]>) -> Result<(), VerifierError> {
    let pub_inputs = PublicInputs{disclosed_attributes, indices, num_of_attributes, num_of_user_attributes, comm, cred_nonce: nonce};
    let acceptable_options =
            winterfell::AcceptableOptions::OptionSet(vec![proof.options().clone()]);

    winterfell::verify::<DisclosureAir, Blake3_256, DefaultRandomCoin<Blake3_256>, MerkleTree<Blake3_256>>(
            proof,
            pub_inputs,
            &acceptable_options,
        )
}
