//! The base field every part of the proof system works over.
//!
//! Named in exactly one place. The modulus fixes `GAMMA2`, every range-proof width, and the Poseidon
//! MDS matrix and round constants, so two modules disagreeing about it would not be a type error --
//! it would be a silently different hash function and a silently different set of range windows.
//!
//! `f23` is Dilithium2's own modulus, `q = 2^23 - 2^13 + 1 = 8380417`, which is what makes
//! `GAMMA2 = (q-1)/88 = 95232` and the rest of the FIPS 204 parameter set native.
//!
//! Two consequences worth knowing:
//!
//! * two-adicity is 13, not `f23201`'s 20, so `trace_length * blowup <= 2^13 = 8192`. At the current
//!   512 rows and blowup 4 that is 2048, and zero-knowledge doubling the trace to 1024 gives 4096 --
//!   comfortable, but the headroom is 2x rather than 256x;
//! * `SexticExtension` over this field needs `y^2 - 5`, not `f23201`'s `y^2 + 3` (`-3` is a quadratic
//!   residue mod `q`, so `y^2 + 3` is reducible here). That fix has to be present in the winterfell
//!   being built against, or every sextic inverse is wrong and no proof verifies.

pub use winterfell::math::fields::f23::BaseElement;

/// Prime modulus of [`BaseElement`]. Every module that needs it should take it from here.
pub const M: u32 = 8380417;

/// `(M - 1) / 88`, Dilithium2's low-order rounding parameter.
pub const GAMMA2: u32 = 95232;

/// `2^17`, Dilithium2's mask bound.
pub const GAMMA1: u32 = 131072;

const _: () = assert!(M == 2u32.pow(23) - 2u32.pow(13) + 1);
const _: () = assert!(GAMMA2 == (M - 1) / 88);
const _: () = assert!(GAMMA1 == 2u32.pow(17));