use log::debug;
use std::{time::Instant};
use winterfell::{
    crypto::{hashers::Blake3_256, DefaultRandomCoin, MerkleTree}, math::{fields::f23201::BaseElement, FieldElement}, FieldExtension, Proof, ProofOptions, Prover, Trace, VerifierError
};

use crate::{utils::poseidon_23_spec::{
    CYCLE_LENGTH as HASH_CYCLE_LEN, DIGEST_SIZE as HASH_DIGEST_WIDTH, RATE_WIDTH as HASH_RATE_WIDTH, STATE_WIDTH as HASH_STATE_WIDTH
}};

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

#[derive(Clone)]
pub struct Credential {
    pub attributes: Vec<[BaseElement; HASH_DIGEST_WIDTH]>,
    pub num_of_user_attributes: usize,
    pub disclosed_indices: Vec<usize>,
    pub salted_hash: [BaseElement; HASH_DIGEST_WIDTH],
    pub salt: [BaseElement; 12]
}

#[derive(Clone)]
pub struct DisclosureInputs {
    pub disclosed_attributes: Vec<[BaseElement; HASH_DIGEST_WIDTH]>,
    pub indices: Vec<usize>,
    pub num_of_attributes: usize,
    pub num_of_user_attributes: usize,
    pub salted_hash: [BaseElement; HASH_DIGEST_WIDTH],
}

pub fn prove(
    credentials: Vec<Credential>
) -> Proof {
        let options = ProofOptions::new(
            24, // number of queries
            16,  // blowup factor
            20,  // grinding factor
            FieldExtension::Sextic,
            8,   // FRI folding factor
            127, // FRI max remainder length
            winterfell::BatchingMethod::Linear, //TODO
            winterfell::BatchingMethod::Linear, //TODO
            true
        );
        debug!(
            "Generating proof for correctness of Disclosure tree"
        );

        //TODO Should be done in higher layer?
        // for i in 0..attributes.len() {
        //     //Add padding attribute if needed
        //     if attributes[i].len() % 2 == 1 {
        //         attributes[i].push([BaseElement::ZERO; HASH_DIGEST_WIDTH]);
        //     }
        // }

        // create a prover
        let now = Instant::now();
        //TODO assuming now that non of the attributes number are odd (padding already included if needed)
        let prover = DisclosureProver::new(options.clone(), credentials);

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

pub fn verify(proof: Proof, disclosures: Vec<DisclosureInputs>) -> Result<(), VerifierError> {
    let pub_inputs = PublicInputs{disclosures};
    let acceptable_options =
            winterfell::AcceptableOptions::OptionSet(vec![proof.options().clone()]);

    winterfell::verify::<DisclosureAir, Blake3_256<BaseElement>, DefaultRandomCoin<Blake3_256<BaseElement>>, MerkleTree<Blake3_256<BaseElement>>>(
            proof,
            pub_inputs,
            &acceptable_options,
        )
}

pub(crate) fn verify_with_wrong_inputs(proof: Proof, disclosures: Vec<DisclosureInputs>) -> Result<(), VerifierError> {
    let pub_inputs = PublicInputs{disclosures};
    let acceptable_options =
            winterfell::AcceptableOptions::OptionSet(vec![proof.options().clone()]);

    winterfell::verify::<DisclosureAir, Blake3_256<BaseElement>, DefaultRandomCoin<Blake3_256<BaseElement>>, MerkleTree<Blake3_256<BaseElement>>>(
            proof,
            pub_inputs,
            &acceptable_options,
        )
}
