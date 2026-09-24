// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use log::debug;
use rand_chacha::{ChaCha20Rng, rand_core::SeedableRng};
use std::{time::Instant};
use winterfell::{
    crypto::{hashers::Blake3_256, DefaultRandomCoin, MerkleTree}, math::{fields::f23201::BaseElement, FieldElement}, FieldExtension, Proof, ProofOptions, Prover, Trace, VerifierError
};

use crate::utils::poseidon_23_spec::{
    CYCLE_LENGTH as HASH_CYCLE_LEN, NUM_ROUNDS as NUM_HASH_ROUNDS,
    STATE_WIDTH as HASH_STATE_WIDTH, RATE_WIDTH as HASH_RATE_WIDTH,
    DIGEST_SIZE as HASH_DIGEST_WIDTH
};

mod air;
use air::ThinDilMulShowAir;

mod prover;
use prover::ThinDilMulShowProver;

mod aux_trace_table;

use self::air::PublicInputs;

// CONSTANTS
// ================================================================================================

const M: u32 = 7340033; // 2^23 - 2^20 + 1
pub const N: usize = 256;
pub const K: usize = 4;
const TAU: usize = 39; //The actual number of swaps gets rounded up to 40 which is fine for security
const S_BALL_END: usize = TAU/HASH_CYCLE_LEN + 2 + 2; //Spending 6 HASH_CYCLES on BALLSAMPLE, +2 for the two SBALLSTART hash cycles
const BETA: u32 = 80;
const Z_LIMIT: u32 = 131072 - BETA; // 2^17 - BETA
const W_HIGH_SHIFT: u32 = 8;
const W_LOW_LIMIT: u32 = 65535-1;
const GAMMA2: u32 = 65536;

const C_SIZE: usize = 24;
const FE_TRIT_SIZE: usize = 11;

const Z_RANGE: usize = 18;
const Q_RANGE: usize = 16;
const R_RANGE: usize = 8;
const W_LOW_RANGE: usize = 17;
const W_HIGH_RANGE: usize = 6;

const C_IND: usize = 0;

//Sample In Ball only
const Q_IND: usize = C_IND + C_SIZE;
const R_IND: usize = Q_IND + HASH_CYCLE_LEN;
const SIGN_IND: usize = R_IND + HASH_CYCLE_LEN;

const Q_RANGE_IND: usize = SIGN_IND + HASH_CYCLE_LEN;
const R_RANGE_IND: usize = Q_RANGE_IND + 2*Q_RANGE;

const SWAP_DEC_FE_IND: usize = R_RANGE_IND + 2*R_RANGE;
const SWAP_DEC_TRIT_IND: usize = SWAP_DEC_FE_IND + C_SIZE;
const SWAP_FE_EQUAL_IND: usize =SWAP_DEC_TRIT_IND + FE_TRIT_SIZE; 

//Asserts moved here to use empty transitions during sample in ball
const SWAP_DEC_ASSERT: usize = SWAP_FE_EQUAL_IND + 1;
const SWAP_DEC_FE_ASSERT: usize = SWAP_DEC_ASSERT + 1;
const SWAP_DEC_TRIT_ASSERT: usize = SWAP_DEC_FE_ASSERT + 1;
const SWAP_C_DEC_ASSERT: usize = SWAP_DEC_TRIT_ASSERT + 1;
const M_COM_ASSERT: usize = SWAP_C_DEC_ASSERT + 1;
const M_BALL_ASSERT: usize = M_COM_ASSERT + HASH_DIGEST_WIDTH;
const Q_ASSERT: usize = M_BALL_ASSERT + HASH_DIGEST_WIDTH;
const R_ASSERT: usize = Q_ASSERT + 2;
const QR_ASSERT: usize = R_ASSERT + 2;

const SWAP_C_TRIT: usize = CTILDE_IND - FE_TRIT_SIZE; 

//PIT only
const C_TRIT_IND: usize = SWAP_C_TRIT;
const W_HIGH_IND: usize = Q_IND; // HASH_RATE_WIDTH wlow per row for first 6 rows. Placing everything at once because we permute
const W_IND: usize = W_HIGH_IND + HASH_RATE_WIDTH; // 4 w per row for first 6 rows
const W_BIND: usize = W_IND + 4; // 4 wbit per row for first 6 rows
const W_LOW_IND: usize = W_BIND + 4; // 4 w per row for first 6 rows
const Z_IND: usize = W_LOW_IND + 4;
const QW_IND: usize = Z_IND + 4;

const Z_RANGE_IND: usize = QW_IND + 4;
const W_LOW_RANGE_IND: usize = Z_RANGE_IND + 8*Z_RANGE;
const W_HIGH_RANGE_IND: usize = W_LOW_RANGE_IND + 4*W_LOW_RANGE;

//All the way
const CTILDE_IND: usize = W_HIGH_RANGE_IND + 8*W_HIGH_RANGE + FE_TRIT_SIZE;

const M_IND: usize = CTILDE_IND + HASH_DIGEST_WIDTH;

const HASH_IND: usize = M_IND + HASH_DIGEST_WIDTH;

// Below show up only in result space
const SWAP_ASSERT: usize = HASH_IND + 3*HASH_STATE_WIDTH + 3*HASH_STATE_WIDTH; //3*HASH_STATE_WIDTH for hashing and double for assertions
const SET_ASSERT: usize = SWAP_ASSERT + 1;
const C_TRIT_ASSERT: usize = SET_ASSERT + 1;
const W_DEC_ASSERT: usize = C_TRIT_ASSERT + 1;
const W_LOW_ASSERT: usize = W_DEC_ASSERT + 2*4;
const W_HIGH_ASSERT: usize = W_LOW_ASSERT + 4;
const CTILDE_ASSERT: usize = W_HIGH_ASSERT + 2*4;
const Z_ASSERT: usize = CTILDE_ASSERT + HASH_DIGEST_WIDTH; // 4 w's, each has 3 checks

pub const TRACE_WIDTH: usize = HASH_IND + 3*HASH_STATE_WIDTH;
pub const AUX_WIDTH: usize = 1 + 4 + 4 + 4 + 1; // C + Z + W + QW + GAMMA(random evaluation point)

pub const HASH_PHASE_CYCLES: usize = 2;
pub const NONCE_INSERT: usize = HASH_CYCLE_LEN;
pub const S_BALL_START: usize = HASH_PHASE_CYCLES*HASH_CYCLE_LEN;

pub const COM_START: usize = (HASH_CYCLE_LEN)*(S_BALL_END+1);
pub const COM_END: usize = (HASH_CYCLE_LEN)*(S_BALL_END+2);

pub const PIT_START: usize = (HASH_CYCLE_LEN)*(S_BALL_END+3);
pub const PIT_LEN: usize = (N+2)*HASH_CYCLE_LEN/(HASH_CYCLE_LEN-2);
pub const PIT_END: usize = PIT_START+PIT_LEN;

pub const PADDED_TRACE_LENGTH: usize = 512;
pub const _TRACE_LENGTH: usize = PIT_END;
/// The part of an issuer public key that the multi-show AIR is bound to.
///
/// These used to be the `HTR`, `PUBT` and `PUBA` constants, which pinned the
/// circuit to a single hard-coded issuer. They are now public inputs: the
/// prover supplies them alongside the witness, the verifier supplies the ones
/// belonging to the issuer it actually trusts, and `PublicInputs::to_elements`
/// folds them into the Fiat-Shamir transcript. A proof produced under one
/// issuer key therefore fails to verify under any other.
///
/// All three are derived from `(rho, t)` by the caller; see
/// `zkdil.PublicKey.proofInputs` in pq-gabi.
#[derive(Clone, Copy)]
pub struct IssuerKey {
    /// Poseidon state after absorbing tr = H(rho || t), `HASH_STATE_WIDTH` wide.
    pub htr: [BaseElement; HASH_STATE_WIDTH],
    /// Coefficients of t, indexed `[j][n]`.
    pub t: [[BaseElement; N]; K],
    /// Coefficients of InvNTT(A), indexed `[i][j][n]`.
    pub a: [[[BaseElement; N]; K]; K],
}

pub fn prove(
    z: [[BaseElement; N]; K],
    w: [[BaseElement; N]; K],
    qw: [[BaseElement; N]; K],
    ctilde: [BaseElement; HASH_DIGEST_WIDTH],
    m: [BaseElement; 12],
    comm: [BaseElement; HASH_DIGEST_WIDTH],
    com_r: [BaseElement; 12],
    salt: [BaseElement; 12],
    nonce: [BaseElement; 12],
    issuer: IssuerKey
) -> Proof {
    // 48,4,20
    // 32,8,20
    // 24,16,20
    // 19,32,21
    // 16,64,20
    // 14,128,20
        let options = ProofOptions::new(
            24, // number of queries
            16,  // blowup factor
            20,  // grinding factor
            FieldExtension::Sextic,
            8,   // FRI folding factor
            127, // FRI max remainder length
            winterfell::BatchingMethod::Linear, //TODO
            winterfell::BatchingMethod::Linear, //TODO
            true,
        );
        debug!(
            "Generating proof for correctness of Merkle tree"
        );

        // create a prover
        let now = Instant::now();
        let prover = ThinDilMulShowProver::new(options.clone(), z, w, qw, ctilde, m, comm, com_r, salt, nonce, issuer);

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
        let seed = ChaCha20Rng::from_entropy().get_seed();
        prover.prove(trace, Some(seed)).unwrap()
    }

    pub fn verify(proof: Proof, comm: [BaseElement; HASH_DIGEST_WIDTH], nonce: [BaseElement; 12], issuer: IssuerKey) -> Result<(), VerifierError> {
        let pub_inputs = PublicInputs{comm, nonce, issuer};
        let acceptable_options =
            winterfell::AcceptableOptions::OptionSet(vec![proof.options().clone()]);

        winterfell::verify::<ThinDilMulShowAir, Blake3_256<BaseElement>, DefaultRandomCoin<Blake3_256<BaseElement>>, MerkleTree<Blake3_256<BaseElement>>>(
            proof,
            pub_inputs,
            &acceptable_options,
        )
    }

    pub fn verify_with_wrong_inputs(proof: Proof, comm: [BaseElement; HASH_DIGEST_WIDTH], nonce: [BaseElement; 12], issuer: IssuerKey) -> Result<(), VerifierError> {
        let pub_inputs = PublicInputs{comm, nonce, issuer};
        let acceptable_options =
            winterfell::AcceptableOptions::OptionSet(vec![proof.options().clone()]);

        winterfell::verify::<ThinDilMulShowAir, Blake3_256<BaseElement>, DefaultRandomCoin<Blake3_256<BaseElement>>, MerkleTree<Blake3_256<BaseElement>>>(
            proof,
            pub_inputs,
            &acceptable_options,
        )
    }