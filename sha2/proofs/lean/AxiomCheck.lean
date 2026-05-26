import Word
import Sha256
import Sha512
import Aeneas

/-! # Axiom audit for the SHA-2 refinement proofs

Each `<algo>_spec` is the public top-level theorem in its respective
module (e.g., `Sha256/Sha256.lean`), relating the Aeneas-extracted
`Extraction.<algo>` to the FIPS-180-4 bitwise spec `SHS.SHA<XXX>.<algo>`
via `digestBitVec` and `sliceBitMessage` (from `Common/Digest.lean`)
and the per-algorithm Impl↔Spec proof from `fips-pub-180-4-lean`. -/

/-! ## Aeneas backend bridge lemmas (theorems, not axioms — for reference). -/
#print axioms Aeneas.Std.slice_iter_loop_eq_foldl
#print axioms Aeneas.Std.range_loop_eq_finFoldl
#print axioms Aeneas.Std.core.array.from_fn_aux_state_spec

/-! ## SHA-256 family — load-bearing trust statement. -/
#print axioms _root_.sha256_spec
#print axioms _root_.sha224_spec

/-! ## SHA-512 family — load-bearing trust statement. -/
#print axioms _root_.sha512_spec
#print axioms _root_.sha384_spec
#print axioms _root_.sha512_256_spec
#print axioms _root_.sha512_224_spec
