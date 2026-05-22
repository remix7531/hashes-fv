# RustCrypto: SHA-2 (formally verified)

![Apache2/MIT licensed][license-image]
![Rust Version][rustc-image]

Pure Rust implementation of the [SHA-2] cryptographic hash algorithms, refactored for formal verification via [Aeneas] with the [Lean 4] backend.

There are 6 standard algorithms specified in the SHA-2 standard: `Sha224`, `Sha256`, `Sha512_224`, `Sha512_256`, `Sha384`, and `Sha512`.

Algorithmically, there are only 2 core algorithms: SHA-256 and SHA-512. All other algorithms are just applications of these with different initial hash values, and truncated to different digest bit lengths. The first two algorithms in the list are based on SHA-256, while the last four are based on SHA-512.

## Design

This fork simplifies the upstream `digest` trait-based API with a pure functional API. The implementation exposes standalone functions that take and return plain data, with no trait objects or generics, making them amenable to extraction by [Charon] (Rust → LLBC) and [Aeneas] (LLBC → Lean 4).

Lean proofs can be found in the [`proofs/lean/`](proofs/lean/) directory. Run `make extract` to regenerate the Lean files from the Rust source, and `make prove` to typecheck the proofs.

The verification chain spans three repos:

```text
RustCrypto Rust source    →  Charon  →  LLBC
                          →  Aeneas  →  Lean monadic translation        (proofs/lean/Extraction/**)
                          →  hand-written refinement                    (this repo) (proofs/lean/*.lean)
                          ↔  bytewise reference impl + FIPS 180-4 spec  (remix7531/fips-180-4-lean)
```

Aeneas is consumed from the immutable [`remix7531/aeneas/sha2-fv-pin`](https://github.com/remix7531/aeneas/tree/sha2-fv-pin) tag (commit `3212a5fe`) until our fixes and feature PRs land upstream. Both `flake.nix` and `sha2/proofs/lean/lakefile.lean` pin this same tag so the Aeneas binary and Lean library stay on the same revision. The Lean proofs build on top of [Mathlib], pulled in transitively via the Aeneas Lean library.

## Verification scope and trust base

`make prove` checks the theorem `sha256_fips_correct`: the Aeneas-extracted `sha256` agrees with the FIPS 180-4 spec for any input shorter than 2⁶¹ bytes. The proof covers the `soft-compact` backend, which is the only backend retained in this fork (see [Backends](#backends) below). Only SHA-256 is verified — the other SHA-2 variants are not yet covered by a refinement proof.

The pinned axiom set is `{propext, Classical.choice, Quot.sound, Aeneas.Std.core.fmt.Formatter}`. The first three are Lean's classical foundations; the fourth is Aeneas's opacity for `core::fmt::Formatter`, introduced because the source pulls in `Display`/`Debug` trait bounds that Aeneas does not look inside. See [`proofs/lean/AxiomCheck.lean`][axioms] for the live audit.

[axioms]: proofs/lean/AxiomCheck.lean

## Examples

```rust
# #[cfg(feature = "sha256")] {
use hex_literal::hex;

let hash256 = sha2::sha256(b"hello world");
assert_eq!(hash256, hex!("b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9"));
# }
```

```rust
# #[cfg(feature = "sha512")] {
use hex_literal::hex;

let hash512 = sha2::sha512(b"hello world");
assert_eq!(hash512, hex!(
    "309ecc489c12d6eb4cc40f50c902f2b4d0ed77ee511a7c7a9bcd3ca86d4cd86f"
    "989dd35bc5ff499670da34255b45b0cfd830e81f605dcf7dc5542e93ae9cd76f"
));
# }
```

## Backends

This fork retains only the portable `soft-compact` backend. All
hardware-specific backends (`aarch64-sha2`, `aarch64-sha3`, `x86-shani`,
`x86-avx2`, `loongarch64-asm`, `riscv-zknh`, `riscv-zknh-compact`,
`wasm32-simd`, and the unrolled `soft` variant) have been removed to
narrow the verified surface.

## License

The crate (the Rust source under `src/` and `tests/`, plus build configuration) is licensed under either of:

* [Apache License, Version 2.0](http://www.apache.org/licenses/LICENSE-2.0)
* [MIT license](http://opensource.org/licenses/MIT)

at your option, matching upstream RustCrypto.

The Lean refinement proofs in [`proofs/lean/`](proofs/lean/) are licensed under **GPL-3.0-or-later**, inherited from [`fips-180-4-lean`](https://github.com/remix7531/fips-180-4-lean); see [`proofs/lean/LICENSE`](proofs/lean/LICENSE). The Rust crate does not link the proof code at runtime, so consumers of the crate are not affected by GPL terms.

[//]: # (badges)

[license-image]: https://img.shields.io/badge/license-Apache2.0/MIT-blue.svg
[rustc-image]: https://img.shields.io/badge/rustc-1.85+-blue.svg

[//]: # (general links)

[SHA-2]: https://en.wikipedia.org/wiki/SHA-2
[Aeneas]: https://github.com/AeneasVerif/aeneas
[Charon]: https://github.com/AeneasVerif/charon
[Lean 4]: https://lean-lang.org/
[Mathlib]: https://github.com/leanprover-community/mathlib4
