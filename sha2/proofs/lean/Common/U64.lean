import Aeneas

/-!
# Word-size-agnostic 64-bit helpers: Aeneas `Std.U64` ↔ Lean core `UInt64`

Mirrors `Common/U8.lean` and the `toUInt32`/`fromUInt32` bridge in
`U32.lean`. These conversions are width-agnostic — the SHA-256
padding-length tag uses them at 64 bits, and the (future) SHA-512
refinement proof will reuse them in the same shape.

SHA-256-specific padding bookkeeping (the BE byte-emit lemmas for the
`[56, 64)` length-tag layout) stays in `FinalBlock.lean`.
-/

open Aeneas Aeneas.Std

/-! ## Scalar conversions -/

@[inline] def toUInt64 (x : U64) : UInt64 := ⟨x.bv⟩
@[inline] def fromUInt64 (x : UInt64) : U64 := ⟨x.toBitVec⟩

@[simp] theorem toUInt64_bv (x : U64) : (toUInt64 x).toBitVec = x.bv := rfl
@[simp] theorem fromUInt64_bv (x : UInt64) : (fromUInt64 x).bv = x.toBitVec := rfl

@[simp] theorem toUInt64_fromUInt64 (x : UInt64) : toUInt64 (fromUInt64 x) = x := rfl
@[simp] theorem fromUInt64_toUInt64 (x : U64) : fromUInt64 (toUInt64 x) = x := rfl
