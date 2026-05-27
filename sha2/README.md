# RustCrypto: SHA-2 (formally verified)

![Apache2/MIT licensed][license-image]
![Rust Version][rustc-image]

Pure Rust implementation of the [SHA-2] cryptographic hash algorithms, refactored for formal verification via [Aeneas] with the [Lean 4] backend against a mechanised [FIPS 180-4 specification][fips-180-4-lean].

The standard specifies six algorithms (`sha256`, `sha224`, `sha512`, `sha384`, `sha512_256`, `sha512_224`) over two cores (SHA-256, SHA-512); the rest are IV swaps with a state truncation.

## Design

This fork replaces upstream's `digest` trait-based API with standalone byte-in / byte-out functions: no trait objects, no generics, friendly to [Charon] (Rust → LLBC) and [Aeneas] (LLBC → Lean 4).

```text
RustCrypto Rust source  ->  Charon  ->  LLBC
                        ->  Aeneas  ->  Lean monadic translation  (proofs/lean/Extraction/)
                        ->  hand-written refinement              (proofs/lean/)
                        <-> FIPS 180-4 spec                       (remix7531/fips-180-4-lean)
```

`make extract` regenerates the Lean files; `make prove` typechecks the proofs. [Mathlib] comes in transitively via the Aeneas Lean library.

## Verification

`make prove` checks one public theorem per algorithm:

```lean4
theorem sha256_spec (data : Slice U8) (h : data.length < 2 ^ 61) :
    Extraction.sha256 data
    ⦃ out =>
        let hb := bytesToBits_length_lt_2_64 data.val h
        SHS.Word.fromBits (bytesToBits out.val) =
          SHS.SHA256.sha256 (bytesToBits data.val) hb ⦄
```

The Aeneas-extracted entry point returns the FIPS 180-4 digest for any input under 2^61 bytes. `bytesToBits` is the single MSB-first byte-to-bit primitive used on both sides; `hb` lifts the byte bound to the `< 2^64` bit bound the spec wants. The five siblings live in [`Sha512.lean`](proofs/lean/Sha512.lean) and [`Sha256.lean`](proofs/lean/Sha256.lean) and share the shape.

Pinned axiom set: `{propext, Classical.choice, Quot.sound, Aeneas.Std.core.fmt.Formatter}`. The fourth is Aeneas's opacity for `core::fmt::Formatter`. [`AxiomCheck.lean`](proofs/lean/AxiomCheck.lean) audits every pinned theorem on each `make prove`.

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

Only the portable `soft-compact` backend is retained; all hardware-specific variants (`aarch64-sha2`, `aarch64-sha3`, `x86-shani`, `x86-avx2`, `loongarch64-asm`, `riscv-zknh`, `riscv-zknh-compact`, `wasm32-simd`, unrolled `soft`) are dropped to keep the verified surface narrow.

## License

The Rust crate is dual-licensed [Apache-2.0](http://www.apache.org/licenses/LICENSE-2.0) or [MIT](http://opensource.org/licenses/MIT), matching upstream RustCrypto.

The Lean proofs under [`proofs/lean/`](proofs/lean/) are **GPL-3.0-or-later**, inherited from [`fips-180-4-lean`](https://github.com/remix7531/fips-180-4-lean) (see [`proofs/lean/LICENSE`](proofs/lean/LICENSE)). The crate does not link the proof code at runtime, so crate consumers are unaffected by GPL terms.

[//]: # (badges)

[license-image]: https://img.shields.io/badge/license-Apache2.0/MIT-blue.svg
[rustc-image]: https://img.shields.io/badge/rustc-1.85+-blue.svg

[//]: # (general links)

[SHA-2]: https://en.wikipedia.org/wiki/SHA-2
[Aeneas]: https://github.com/AeneasVerif/aeneas
[Charon]: https://github.com/AeneasVerif/charon
[Lean 4]: https://lean-lang.org/
[Mathlib]: https://github.com/leanprover-community/mathlib4
[fips-180-4-lean]: https://remix7531.com/fips-180-4-lean/
