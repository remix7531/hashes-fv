import U32
import ToU32s
import Compress
import SetChain
import FinalBlock
import Loop0
import Loop1
import Sha256
import Sha224
import Spec
import Aeneas

/-! # Axiom audit for the SHA-256 refinement proof -/

/-! ## Aeneas backend bridge lemmas (theorems, not axioms — for reference). -/
#print axioms Aeneas.Std.slice_iter_loop_eq_foldl
#print axioms Aeneas.Std.range_loop_eq_finFoldl
#print axioms Aeneas.Std.core.array.from_fn_aux_state_spec

/-! ## Top-level theorems — load-bearing trust statement. -/
#print axioms _root_.sha256_spec
#print axioms _root_.sha256_correct
#print axioms _root_.sha256_fips_correct
#print axioms _root_.sha224_spec
#print axioms _root_.sha224_correct
#print axioms _root_.sha224_fips_correct
