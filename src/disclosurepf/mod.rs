// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use log::debug;
use std::{time::Instant};
use winterfell::{
    crypto::{DefaultRandomCoin, MerkleTree}, math::{fields::f23201::BaseElement, FieldElement, StarkField}, FieldExtension, Proof, ProofOptions, Prover, Trace, VerifierError
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

pub const STORAGE_START: usize = HASH_STATE_WIDTH*3;

pub type Blake3_256 = winterfell::crypto::hashers::Blake3_256<BaseElement>;

pub(crate) fn prove(
    attributes: Vec<Vec<[BaseElement; HASH_DIGEST_WIDTH]>>,
    disclosed_indices: Vec<Vec<usize>>,
    merkle_comm: Vec<[BaseElement; HASH_RATE_WIDTH]>,
    secret_comm: [BaseElement; HASH_RATE_WIDTH],
    nonce: Vec<[BaseElement; 12]>,
    secret_nonce: [BaseElement; 12]
) -> Proof {
        let options = ProofOptions::new(
            48, // number of queries
            4,  // blowup factor
            20,  // grinding factor
            FieldExtension::Sextic,
            8,   // FRI folding factor
            127, // FRI max remainder length
            winterfell::BatchingMethod::Linear, //TODO
            winterfell::BatchingMethod::Linear //TODO
        );
        debug!(
            "Generating proof for correctness of Disclosure tree"
        );

        // create a prover
        let now = Instant::now();
        let prover = DisclosureProver::new(options.clone(), attributes, disclosed_indices, merkle_comm, secret_comm, nonce, secret_nonce);

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

        // generate the proof
        prover.prove(trace).unwrap()
    }

pub(crate) fn verify(proof: Proof, disclosed_attributes: Vec<Vec<[BaseElement; HASH_DIGEST_WIDTH]>>, indices: Vec<Vec<usize>>, num_of_attributes: Vec<usize>, merkle_comm: Vec<[BaseElement; HASH_RATE_WIDTH]>, secret_comm: [BaseElement; HASH_RATE_WIDTH], nonce: Vec<[BaseElement; 12]>,  secret_nonce: [BaseElement; 12]) -> Result<(), VerifierError> {
    let pub_inputs = PublicInputs{disclosed_attributes, indices, num_of_attributes, merkle_comm, secret_comm, nonce, secret_nonce};
    let acceptable_options =
            winterfell::AcceptableOptions::OptionSet(vec![proof.options().clone()]);

    winterfell::verify::<DisclosureAir, Blake3_256, DefaultRandomCoin<Blake3_256>, MerkleTree<Blake3_256>>(
            proof,
            pub_inputs,
            &acceptable_options,
        )
}

pub(crate) fn verify_with_wrong_inputs(proof: Proof, disclosed_attributes: Vec<Vec<[BaseElement; HASH_DIGEST_WIDTH]>>, indices: Vec<Vec<usize>>, num_of_attributes: Vec<usize>, merkle_comm: Vec<[BaseElement; HASH_RATE_WIDTH]>, secret_comm: [BaseElement; HASH_RATE_WIDTH], nonce: Vec<[BaseElement; 12]>, secret_nonce: [BaseElement; 12]) -> Result<(), VerifierError> {
    let pub_inputs = PublicInputs{disclosed_attributes, indices, num_of_attributes, merkle_comm, secret_comm, nonce, secret_nonce};
    let acceptable_options =
            winterfell::AcceptableOptions::OptionSet(vec![proof.options().clone()]);

    winterfell::verify::<DisclosureAir, Blake3_256, DefaultRandomCoin<Blake3_256>, MerkleTree<Blake3_256>>(
            proof,
            pub_inputs,
            &acceptable_options,
        )
}
