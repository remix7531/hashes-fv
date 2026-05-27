import Extraction
import impl.SHA256
import Mathlib.Tactic.IntervalCases
import Common.U8

/-!
# Type bridge: Aeneas `Std.U32`/`Std.U8` ↔ Lean core `UInt32`/`UInt8`

Both wrap the same `BitVec`. Conversions are definitional and operations
agree pointwise. We expose round-trip lemmas plus operation-preservation
lemmas keyed on `BitVec` equality, so refinement proofs can rewrite
through a `Vector UInt32 _` view of an `Array Std.U32 _`.
-/

open Aeneas Aeneas.Std

/-! ## Scalar conversions -/

@[inline] def toUInt32 (x : U32) : UInt32 := ⟨x.bv⟩
@[inline] def fromUInt32 (x : UInt32) : U32 := ⟨x.toBitVec⟩

@[simp] theorem toUInt32_bv (x : U32) : (toUInt32 x).toBitVec = x.bv := rfl
@[simp] theorem fromUInt32_bv (x : UInt32) : (fromUInt32 x).bv = x.toBitVec := rfl

@[simp] theorem toUInt32_fromUInt32 (x : UInt32) : toUInt32 (fromUInt32 x) = x := rfl
@[simp] theorem fromUInt32_toUInt32 (x : U32) : fromUInt32 (toUInt32 x) = x := rfl

/-! ## Pointwise operation preservation -/

@[simp] theorem toUInt32_xor (x y : U32) :
    toUInt32 (x ^^^ y) = toUInt32 x ^^^ toUInt32 y := rfl

@[simp] theorem toUInt32_and (x y : U32) :
    toUInt32 (x &&& y) = toUInt32 x &&& toUInt32 y := rfl

@[simp] theorem toUInt32_or (x y : U32) :
    toUInt32 (x ||| y) = toUInt32 x ||| toUInt32 y := rfl

@[simp] theorem toUInt32_not (x : U32) :
    toUInt32 (~~~ x) = ~~~ (toUInt32 x) := rfl

/-- Aeneas `wrapping_add` is `BitVec` addition; matches `UInt32.add`. -/
@[simp] theorem toUInt32_wrapping_add (x y : U32) :
    toUInt32 (UScalar.wrapping_add x y) = toUInt32 x + toUInt32 y := rfl

/-- Aeneas `rotate_right` (after the local `BitVec.rotateRight` patch) ↔
`Impl.UInt32.rotr`. Holds for `0 < n < 32`, which every SHA-256 callsite
(literal 2/6/7/11/13/17/18/19/22/25) satisfies. -/
theorem toUInt32_rotate_right (x n : U32) (hn : 0 < n.val) (hn2 : n.val < 32) :
    toUInt32 (UScalar.rotate_right x n) =
      SHS.SHA256.Impl.UInt32.rotr (toUInt32 x) (toUInt32 n) := by
  apply UInt32.toBitVec_inj.mp
  unfold UScalar.rotate_right SHS.SHA256.Impl.UInt32.rotr
  show x.bv.rotateRight n.val = _
  rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt hn2]
  simp [BitVec.toNat_sub, Nat.mod_eq_of_lt, hn2]; grind

/-! ## Literal rotation bridges for SHA-256

The general `toUInt32_rotate_right` bridge carries side-conditions
`0 < n.val < 32`, so it cannot be a `simp` lemma directly. Materialize
the 10 literal-amount instances actually used by SHA-256
(2, 6, 7, 11, 13, 17, 18, 19, 22, 25) as side-condition-free lemmas.
The `compress_u32_body_spec` proof rewrites with these via `simp only`. -/

theorem rotr_bridge_2 (x : U32) :
    toUInt32 (UScalar.rotate_right x 2#u32) = SHS.SHA256.Impl.UInt32.rotr (toUInt32 x) 2 :=
  toUInt32_rotate_right x 2#u32 (by decide) (by decide)
theorem rotr_bridge_6 (x : U32) :
    toUInt32 (UScalar.rotate_right x 6#u32) = SHS.SHA256.Impl.UInt32.rotr (toUInt32 x) 6 :=
  toUInt32_rotate_right x 6#u32 (by decide) (by decide)
theorem rotr_bridge_7 (x : U32) :
    toUInt32 (UScalar.rotate_right x 7#u32) = SHS.SHA256.Impl.UInt32.rotr (toUInt32 x) 7 :=
  toUInt32_rotate_right x 7#u32 (by decide) (by decide)
theorem rotr_bridge_11 (x : U32) :
    toUInt32 (UScalar.rotate_right x 11#u32) = SHS.SHA256.Impl.UInt32.rotr (toUInt32 x) 11 :=
  toUInt32_rotate_right x 11#u32 (by decide) (by decide)
theorem rotr_bridge_13 (x : U32) :
    toUInt32 (UScalar.rotate_right x 13#u32) = SHS.SHA256.Impl.UInt32.rotr (toUInt32 x) 13 :=
  toUInt32_rotate_right x 13#u32 (by decide) (by decide)
theorem rotr_bridge_17 (x : U32) :
    toUInt32 (UScalar.rotate_right x 17#u32) = SHS.SHA256.Impl.UInt32.rotr (toUInt32 x) 17 :=
  toUInt32_rotate_right x 17#u32 (by decide) (by decide)
theorem rotr_bridge_18 (x : U32) :
    toUInt32 (UScalar.rotate_right x 18#u32) = SHS.SHA256.Impl.UInt32.rotr (toUInt32 x) 18 :=
  toUInt32_rotate_right x 18#u32 (by decide) (by decide)
theorem rotr_bridge_19 (x : U32) :
    toUInt32 (UScalar.rotate_right x 19#u32) = SHS.SHA256.Impl.UInt32.rotr (toUInt32 x) 19 :=
  toUInt32_rotate_right x 19#u32 (by decide) (by decide)
theorem rotr_bridge_22 (x : U32) :
    toUInt32 (UScalar.rotate_right x 22#u32) = SHS.SHA256.Impl.UInt32.rotr (toUInt32 x) 22 :=
  toUInt32_rotate_right x 22#u32 (by decide) (by decide)
theorem rotr_bridge_25 (x : U32) :
    toUInt32 (UScalar.rotate_right x 25#u32) = SHS.SHA256.Impl.UInt32.rotr (toUInt32 x) 25 :=
  toUInt32_rotate_right x 25#u32 (by decide) (by decide)

/-! ## `Array Std.U32 N` ↔ `Vector UInt32 N` -/

@[inline] def arrayU32ToVec {N : Usize} (a : Array U32 N) : Vector UInt32 N.val :=
  ⟨(a.val.map toUInt32).toArray, by simp [a.property]⟩

@[simp] theorem arrayU32ToVec_size {N : Usize} (a : Array U32 N) :
    (arrayU32ToVec a).size = N.val := by simp [arrayU32ToVec]

/-! ## Big-endian 4-byte decode bridge -/

open SHS.SHA256 in
/-- The four-byte BE decoder in Aeneas's stdlib equals the shift-or chain
that `Impl.beU32` materializes. -/
/-
Strategy: Pattern-match the 4-byte array to expose its bytes `b0..b3`, then
prove the goal at the `BitVec`-level via `UInt32.toBitVec_inj`. The proof
walks three layers:

1.  **LE byte ladder.** `h0..h4` are four definitional (`rfl`) unfoldings of
    `BitVec.fromLEBytes` on lists of length 0..4. They expose the recursive
    `setWidth ||| shift-left` structure one byte at a time.
2.  **BE ↔ LE cast.** `hBE` is the single `rfl`-cast that rewrites
    `BitVec.fromBEBytes [b0..b3]` to `BitVec.fromLEBytes [b3..b0]` (reversed
    list).  This is the only non-`setWidth`/`||| <<<` rewrite needed.
3.  **Bit-blast closer.** After `simp only` collapses the ladder against the
    `UInt8.toUInt32`/`<<<`/`|||` simp set, `BitVec.eq_of_getLsbD_eq` reduces
    the equality to a per-bit check, dispatched by
    `interval_cases i <;> simp` over the 32 bit positions.

Mirrors `Word/U64.lean::toUInt64_from_be_bytes` at width 64 / 8 bytes.
-/
theorem toUInt32_from_be_bytes (a : Array U8 4#usize) :
    toUInt32 (core.num.U32.from_be_bytes a) =
      ((toUInt8 a.val[0]!).toUInt32 <<< 24) ||| ((toUInt8 a.val[1]!).toUInt32 <<< 16) |||
      ((toUInt8 a.val[2]!).toUInt32 <<< 8)  ||| (toUInt8 a.val[3]!).toUInt32 := by
  rcases a with ⟨l, hl⟩
  match l, hl with
  | [b0, b1, b2, b3], _ =>
    apply UInt32.toBitVec_inj.mp
    simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
    show
      ((BitVec.cast (by simp : 32 = UScalarTy.U32.numBits)
          (BitVec.cast (by simp : 8 * [b0.bv, b1.bv, b2.bv, b3.bv].length = 32)
            (BitVec.fromBEBytes [b0.bv, b1.bv, b2.bv, b3.bv])))
        : BitVec UScalarTy.U32.numBits)
        = ((⟨b0.bv⟩ : UInt8).toUInt32 <<< 24
            ||| (⟨b1.bv⟩ : UInt8).toUInt32 <<< 16
            ||| (⟨b2.bv⟩ : UInt8).toUInt32 <<< 8
            ||| (⟨b3.bv⟩ : UInt8).toUInt32).toBitVec
    have h4 : BitVec.fromLEBytes [b3.bv, b2.bv, b1.bv, b0.bv]
        = BitVec.setWidth 32 b3.bv
          ||| ((BitVec.fromLEBytes [b2.bv, b1.bv, b0.bv]).setWidth 32 <<< 8) := rfl
    have h3 : BitVec.fromLEBytes [b2.bv, b1.bv, b0.bv]
        = BitVec.setWidth 24 b2.bv
          ||| ((BitVec.fromLEBytes [b1.bv, b0.bv]).setWidth 24 <<< 8) := rfl
    have h2 : BitVec.fromLEBytes [b1.bv, b0.bv]
        = BitVec.setWidth 16 b1.bv
          ||| ((BitVec.fromLEBytes [b0.bv]).setWidth 16 <<< 8) := rfl
    have h1 : BitVec.fromLEBytes [b0.bv]
        = BitVec.setWidth 8 b0.bv
          ||| ((BitVec.fromLEBytes ([] : List _)).setWidth 8 <<< 8) := rfl
    have h0 : BitVec.fromLEBytes ([] : List _) = BitVec.ofNat 0 0 := rfl
    have hBE : BitVec.fromBEBytes [b0.bv, b1.bv, b2.bv, b3.bv]
        = BitVec.cast (by simp) (BitVec.fromLEBytes [b3.bv, b2.bv, b1.bv, b0.bv]) := rfl
    simp only [hBE, h4, h3, h2, h1, h0,
      UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt8.toBitVec_toUInt32]
    simp [BitVec.setWidth_setWidth]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    interval_cases i <;> simp

open SHS.SHA256 in
/-- Corollary linking `core.num.U32.from_be_bytes` directly to
`Impl.beU32 (arrayU8ToVec block) ⟨j, hj⟩`, given that `chunk` is the
4-byte slice `[block[4j], block[4j+1], block[4j+2], block[4j+3]]`.
The hypothesis is what the calling site materializes from the
`to_u32s` extracted closure. -/
/-
Strategy: Rewrite the LHS by the previous theorem `toUInt32_from_be_bytes`
and the slice equation `hchunk`, then unfold `Impl.beU32` on the RHS. The
two sides then differ only in how byte access is phrased — `block.val[…]!`
on the left vs `(arrayU8ToVec block)[…]` on the right. The local helper
`hidx` discharges that mismatch for any in-range index by reducing both
forms to `toUInt8 (block.val[i]!)`. Four `← hidx` rewrites align the four
byte positions, after which `rfl` closes the goal.

Mirrors `Word/U64.lean::toUInt64_from_be_bytes_eq_beU64` at width 64 /
8 bytes (block size 128 vs 64, 16 eight-byte chunks vs 16 four-byte chunks).
-/
theorem toUInt32_from_be_bytes_eq_beU32
    (block : Array U8 64#usize) (chunk : Array U8 4#usize)
    (j : Nat) (hj : j < 16)
    (hchunk : chunk.val = [block.val[4 * j]!, block.val[4 * j + 1]!,
                           block.val[4 * j + 2]!, block.val[4 * j + 3]!]) :
    toUInt32 (core.num.U32.from_be_bytes chunk) =
      Impl.beU32 (arrayU8ToVec block) ⟨j, hj⟩ := by
  rw [toUInt32_from_be_bytes, hchunk]
  simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
  unfold Impl.beU32
  have hidx : ∀ (i : Nat) (hi : i < 64),
      (arrayU8ToVec block)[i]'(by simp; omega) = toUInt8 (block.val[i]!) := fun i hi => by
    simp [arrayU8ToVec, hi, block.property]
  rw [← hidx (4 * j) (by omega), ← hidx (4 * j + 1) (by omega),
      ← hidx (4 * j + 2) (by omega), ← hidx (4 * j + 3) (by omega)]
  rfl

/-! ## Vector indexing through `arrayU32ToVec` / `arrayU8ToVec` -/

@[simp] theorem arrayU32ToVec_getElem
    {N : Usize} (block : Array U32 N) (i : Nat) (h : i < N.val)
    (h' : i < (arrayU32ToVec block).size := by simp [arrayU32ToVec]; omega) :
    (arrayU32ToVec block)[i]'h' =
      toUInt32 (block.val[i]'(by simpa [block.property] using h)) := by
  simp [arrayU32ToVec]

/-! ## Rewrite-friendly reformulations of `arrayU32ToVec` indexing

These alternative forms target goals where the bound on the indexing
operator is implicit or stated differently than `(arrayU32ToVec block).size`. -/

/-- The underlying `toList` of `arrayU32ToVec block` is `block.val.map toUInt32`.
This is `rfl`-shaped and lets standard `List.getElem`/`List.getElem!` lemmas
fire on the result. -/
@[simp] theorem arrayU32ToVec_toList {N : Usize} (block : Array U32 N) :
    (arrayU32ToVec block).toList = block.val.map toUInt32 := by
  simp [arrayU32ToVec]

/-- `getElem!`-form of `arrayU32ToVec` indexing. Pattern matches goals
where the bound is implicit. -/
@[simp] theorem arrayU32ToVec_getElem!
    {N : Usize} (block : Array U32 N) (i : Nat) :
    (arrayU32ToVec block).toList[i]! = toUInt32 (block.val[i]!) := by
  rw [arrayU32ToVec_toList]
  by_cases h : i < N.val <;> (simp [block.property, h]; try rfl)

/-! ## `arrayU32ToVec` of `Array.set`

These bridge `Aeneas.Std.Array.set` (which returns an `Array α n` directly,
preserving the size invariant) through the `arrayU32ToVec` view to a
`Vector.set` call. The downstream proof
(`compress_u32_body_spec`'s i ≥ 16 branch in `Sha256.lean`)
uses these to align an Aeneas-side schedule write with the Impl-side
`Vector.set`. -/

/-- `toList` form: the underlying list of `arrayU32ToVec (block.set i v)` is
the list `block.val` mapped through `toUInt32` with index `i.val` overwritten
by `toUInt32 v`. This is the cleanest form for downstream `simp`. -/
theorem arrayU32ToVec_set_toList
    {N : Usize} (block : Array U32 N) (i : Usize) (v : U32) :
    (arrayU32ToVec (block.set i v)).toList =
      (block.val.map toUInt32).set i.val (toUInt32 v) := by
  simp [arrayU32ToVec, Aeneas.Std.Array.set, List.map_set]

/-- Main bridge lemma: `arrayU32ToVec` distributes over `Aeneas.Std.Array.set`,
mapping it to `Vector.set` on the converted vector. The bound
`hi : i.val < (arrayU32ToVec block).size` on the RHS `Vector.set` is
threaded through explicitly so callers can supply whatever shape the
ambient context has produced. -/
theorem arrayU32ToVec_set
    {N : Usize} (block : Array U32 N) (i : Usize) (v : U32)
    (hi : i.val < (arrayU32ToVec block).size) :
    arrayU32ToVec (block.set i v) =
      (arrayU32ToVec block).set i.val (toUInt32 v) hi := by
  apply Vector.toList_inj.mp; rw [arrayU32ToVec_set_toList, Vector.toList_set, arrayU32ToVec_toList]

/-! ## SHA-256 round-constant table equivalence -/

/-- Entry-wise equivalence between the Aeneas-extracted round constants
and the FIPS-spec `Impl.K32` table. -/
theorem K32_eq (i : Nat) (hi : i < 64) :
    toUInt32 ((Extraction.consts.K32 : Array U32 64#usize).val[i]!) =
      SHS.SHA256.Impl.K32[i]'(by simpa using hi) := by
  unfold Extraction.consts.K32; revert hi i; decide

/-! ## SHA-256 initial-hash-value table equivalence -/

/-- The Aeneas-extracted SHA-256 IV bridges to the FIPS-spec `Impl.H256_256`. -/
theorem H256_256_eq :
    arrayU32ToVec Extraction.consts.H256_256 = SHS.SHA256.Impl.H256_256 := by
  apply Vector.toList_inj.mp; unfold Extraction.consts.H256_256; decide
