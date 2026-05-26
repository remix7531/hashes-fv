import U32
import U64
import ToU32s
import ToU64s
import Compress
import SetChain
import FinalBlock
import Loop0
import Loop1
import Sha256
import Sha224
import Sha512
import Sha384
import Sha512_256
import Sha512_224
import Spec
import Aeneas

/-! # Axiom audit for the SHA-2 refinement proofs

The SHA-256 family is fully proved; the SHA-512 family currently
admits its top-level `_spec` statement via `sorry`, so the SHA-512
audit lines below are expected to report `sorryAx`. They are kept so
that the audit becomes meaningful automatically once the SHA-512
proof lands.
-/

/-! ## Aeneas backend bridge lemmas (theorems, not axioms — for reference). -/
#print axioms Aeneas.Std.slice_iter_loop_eq_foldl
#print axioms Aeneas.Std.range_loop_eq_finFoldl
#print axioms Aeneas.Std.core.array.from_fn_aux_state_spec

/-! ## SHA-256 family — load-bearing trust statement. -/
#print axioms _root_.sha256_spec
#print axioms _root_.sha256_correct
#print axioms _root_.sha256_fips_correct
#print axioms _root_.sha224_spec
#print axioms _root_.sha224_correct
#print axioms _root_.sha224_fips_correct

/-! ## SHA-512 family — pending (expected: `sorryAx`). -/
#print axioms _root_.sha512_spec
#print axioms _root_.sha512_correct
#print axioms _root_.sha512_fips_correct
#print axioms _root_.sha384_spec
#print axioms _root_.sha384_correct
#print axioms _root_.sha384_fips_correct
#print axioms _root_.sha512_256_spec
#print axioms _root_.sha512_256_correct
#print axioms _root_.sha512_256_fips_correct
#print axioms _root_.sha512_224_spec
#print axioms _root_.sha512_224_correct
#print axioms _root_.sha512_224_fips_correct
