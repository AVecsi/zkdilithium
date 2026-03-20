# Post-Quantum Digital Identity

A Rust implementation of an optimized [zkDilithium](https://eprint.iacr.org/2023/414) based anonymous credential scheme with extensions to support multi-show unlinkability and selective disclosure.

> **⚠️ WARNING:** This is an academic proof-of-concept prototype and has not received careful code review. This implementation is **NOT ready for production use**.

## Overview

This library implements a post-quantum anonymous credential scheme based on zkDilithium signatures and STARK proofs. It supports:

- **Anonymous credentials** — prove possession of a valid credential without revealing the underlying signature
- **Multi-show unlinkability** — repeated presentations of the same credential cannot be linked to one another
- **Selective disclosure** — reveal only chosen attributes from a credential while keeping others hidden
- **Hidden attributes** — credentials can include attributes that are hidden from the issuer

## Dependencies

This project uses the [winterfell](https://github.com/facebook/winterfell/) crate as the STARK prover backend. zkDilithium requires custom fields and extensions not present in upstream, and while a [prior fork](https://github.com/bwesterb/winterfell) added some of these, it lacked zero-knowledge proof support and had fallen out of date. Our [fork](https://github.com/avecsi/winterfell/) builds on this work and adds the necessary zkDilithium fields, field extensions, and ZK support.

The library also exposes a C-compatible FFI layer, with bindings generated automatically by [cbindgen](https://github.com/mozilla/cbindgen). This allows the Rust implementation to be called from Go via CGo, as used in [pq-gabi](https://github.com/AVecsi/pq-gabi).

## Getting Started

**Prerequisites:** Rust and Cargo (stable toolchain recommended) and [cbindgen](https://github.com/mozilla/cbindgen).

Clone the repository and build in release mode:

```bash
cargo run --release
```

## Module Structure

- [`src/utils`](src/utils) — Poseidon hash function implemented over the zkDilithium field, along with the corresponding constraints.
- [`src/starkpf`](src/starkpf/) — STARK prover that proves knowledge of a zkDilithium signature on a publicly known message `m`.
- [`src/multishowpf`](src/multishowpf/) — STARK prover that proves knowledge of a zkDilithium signature on a secret message `m` by publishing `H(m || salt)`, enabling unlinkability.
- [`src/disclosurepf2`](src/disclosurepf2/) — STARK prover that proves knowledge of a credential containing the disclosed attributes and contributing to `H(m || salt)`, enabling selective disclosure.

## References

- Guru-Vamsi Policharla, Bas Westerbaan, Armando Faz-Hernández, & Christopher A Wood. (2023). Post-Quantum Privacy Pass via Post-Quantum Anonymous Credentials. [https://eprint.iacr.org/2023/414](https://eprint.iacr.org/2023/414)
- [winterfell](https://github.com/facebook/winterfell/) — STARK proof system by Facebook

## License

This library is released under the [MIT License](LICENSE).