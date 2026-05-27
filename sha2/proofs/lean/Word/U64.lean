import Extraction
import impl.SHA512
import Common.U64
import Mathlib.Tactic.IntervalCases

/-!
# Type bridge: Aeneas `Std.U64` ↔ Lean core `UInt64` (SHA-512 width)

Mirrors `U32.lean` at 64-bit width.  The basic `toUInt64`/`fromUInt64`
scalar conversions live in `Common/U64.lean` (shared between SHA-256's
`u64` length-tag emit and SHA-512's state words); this module adds the
SHA-512-specific BE 8-byte decode bridge, `arrayU64ToVec` view-level
lemmas, and the `K64` / `H0_512*` constant-table equivalences against
the upstream `Impl.{K64, H0_512, H0_384, H0_512_256, H0_512_224}`.
-/

open Aeneas Aeneas.Std

/-! ## Pointwise operation preservation -/

@[simp] theorem toUInt64_xor (x y : U64) :
    toUInt64 (x ^^^ y) = toUInt64 x ^^^ toUInt64 y := rfl

@[simp] theorem toUInt64_and (x y : U64) :
    toUInt64 (x &&& y) = toUInt64 x &&& toUInt64 y := rfl

@[simp] theorem toUInt64_or (x y : U64) :
    toUInt64 (x ||| y) = toUInt64 x ||| toUInt64 y := rfl

@[simp] theorem toUInt64_not (x : U64) :
    toUInt64 (~~~ x) = ~~~ (toUInt64 x) := rfl

/-- Aeneas `wrapping_add` is `BitVec` addition; matches `UInt64.add`. -/
@[simp] theorem toUInt64_wrapping_add (x y : U64) :
    toUInt64 (UScalar.wrapping_add x y) = toUInt64 x + toUInt64 y := rfl

/-- Aeneas `rotate_right` ↔ `Impl.UInt64.rotr`.  Aeneas's `UScalar.rotate_right`
takes shift counts at the `U32` width (Rust's `u32::rotate_right(u32)` /
`u64::rotate_right(u32)` convention); the Impl side `UInt64.rotr` takes
`UInt64`. We pass the shift through `BitVec.ofNat 64 n.val` so the
two sides agree at the bit level for `0 < n < 64` (which every SHA-512
callsite — literal 1/6/7/8/14/18/19/28/34/39/41/61 — satisfies). -/
theorem toUInt64_rotate_right (x : U64) (n : U32) (hn : 0 < n.val) (hn2 : n.val < 64) :
    toUInt64 (UScalar.rotate_right x n) =
      SHS.SHA512.Impl.UInt64.rotr (toUInt64 x) ⟨BitVec.ofNat 64 n.val⟩ := by
  apply UInt64.toBitVec_inj.mp
  unfold UScalar.rotate_right SHS.SHA512.Impl.UInt64.rotr
  show x.bv.rotateRight n.val = _
  rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt hn2]
  simp [BitVec.toNat_sub, Nat.mod_eq_of_lt, hn2]; grind

/-! ## Literal rotation bridges for SHA-512

The general `toUInt64_rotate_right` bridge carries side-conditions
`0 < n.val < 64`, so it cannot be a `simp` lemma directly. Materialize
the 10 literal-amount instances actually used by SHA-512
(1, 8, 14, 18, 19, 28, 34, 39, 41, 61) as side-condition-free lemmas. -/

theorem rotr64_bridge_1 (x : U64) :
    toUInt64 (UScalar.rotate_right x 1#u32) = SHS.SHA512.Impl.UInt64.rotr (toUInt64 x) 1 :=
  toUInt64_rotate_right x 1#u32 (by decide) (by decide)
theorem rotr64_bridge_8 (x : U64) :
    toUInt64 (UScalar.rotate_right x 8#u32) = SHS.SHA512.Impl.UInt64.rotr (toUInt64 x) 8 :=
  toUInt64_rotate_right x 8#u32 (by decide) (by decide)
theorem rotr64_bridge_14 (x : U64) :
    toUInt64 (UScalar.rotate_right x 14#u32) = SHS.SHA512.Impl.UInt64.rotr (toUInt64 x) 14 :=
  toUInt64_rotate_right x 14#u32 (by decide) (by decide)
theorem rotr64_bridge_18 (x : U64) :
    toUInt64 (UScalar.rotate_right x 18#u32) = SHS.SHA512.Impl.UInt64.rotr (toUInt64 x) 18 :=
  toUInt64_rotate_right x 18#u32 (by decide) (by decide)
theorem rotr64_bridge_19 (x : U64) :
    toUInt64 (UScalar.rotate_right x 19#u32) = SHS.SHA512.Impl.UInt64.rotr (toUInt64 x) 19 :=
  toUInt64_rotate_right x 19#u32 (by decide) (by decide)
theorem rotr64_bridge_28 (x : U64) :
    toUInt64 (UScalar.rotate_right x 28#u32) = SHS.SHA512.Impl.UInt64.rotr (toUInt64 x) 28 :=
  toUInt64_rotate_right x 28#u32 (by decide) (by decide)
theorem rotr64_bridge_34 (x : U64) :
    toUInt64 (UScalar.rotate_right x 34#u32) = SHS.SHA512.Impl.UInt64.rotr (toUInt64 x) 34 :=
  toUInt64_rotate_right x 34#u32 (by decide) (by decide)
theorem rotr64_bridge_39 (x : U64) :
    toUInt64 (UScalar.rotate_right x 39#u32) = SHS.SHA512.Impl.UInt64.rotr (toUInt64 x) 39 :=
  toUInt64_rotate_right x 39#u32 (by decide) (by decide)
theorem rotr64_bridge_41 (x : U64) :
    toUInt64 (UScalar.rotate_right x 41#u32) = SHS.SHA512.Impl.UInt64.rotr (toUInt64 x) 41 :=
  toUInt64_rotate_right x 41#u32 (by decide) (by decide)
theorem rotr64_bridge_61 (x : U64) :
    toUInt64 (UScalar.rotate_right x 61#u32) = SHS.SHA512.Impl.UInt64.rotr (toUInt64 x) 61 :=
  toUInt64_rotate_right x 61#u32 (by decide) (by decide)

/-! ## `Array Std.U64 N` ↔ `Vector UInt64 N` -/

@[inline] def arrayU64ToVec {N : Usize} (a : Array U64 N) : Vector UInt64 N.val :=
  ⟨(a.val.map toUInt64).toArray, by simp [a.property]⟩

@[simp] theorem arrayU64ToVec_size {N : Usize} (a : Array U64 N) :
    (arrayU64ToVec a).size = N.val := by simp [arrayU64ToVec]

/-! ## Big-endian 8-byte decode bridge -/

open SHS.SHA512 in
/-- The eight-byte BE decoder in Aeneas's stdlib equals the shift-or chain
that `Impl.beU64` materializes. -/
theorem toUInt64_from_be_bytes (a : Array U8 8#usize) :
    toUInt64 (core.num.U64.from_be_bytes a) =
      ((toUInt8 a.val[0]!).toUInt64 <<< 56) |||
      ((toUInt8 a.val[1]!).toUInt64 <<< 48) |||
      ((toUInt8 a.val[2]!).toUInt64 <<< 40) |||
      ((toUInt8 a.val[3]!).toUInt64 <<< 32) |||
      ((toUInt8 a.val[4]!).toUInt64 <<< 24) |||
      ((toUInt8 a.val[5]!).toUInt64 <<< 16) |||
      ((toUInt8 a.val[6]!).toUInt64 <<< 8) |||
      (toUInt8 a.val[7]!).toUInt64 := by
  rcases a with ⟨l, hl⟩
  match l, hl with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    apply UInt64.toBitVec_inj.mp
    simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
    show
      ((BitVec.cast (by simp : 64 = UScalarTy.U64.numBits)
          (BitVec.cast (by simp : 8 * [b0.bv, b1.bv, b2.bv, b3.bv,
                                         b4.bv, b5.bv, b6.bv, b7.bv].length = 64)
            (BitVec.fromBEBytes [b0.bv, b1.bv, b2.bv, b3.bv,
                                  b4.bv, b5.bv, b6.bv, b7.bv])))
        : BitVec UScalarTy.U64.numBits)
        = ((⟨b0.bv⟩ : UInt8).toUInt64 <<< 56
            ||| (⟨b1.bv⟩ : UInt8).toUInt64 <<< 48
            ||| (⟨b2.bv⟩ : UInt8).toUInt64 <<< 40
            ||| (⟨b3.bv⟩ : UInt8).toUInt64 <<< 32
            ||| (⟨b4.bv⟩ : UInt8).toUInt64 <<< 24
            ||| (⟨b5.bv⟩ : UInt8).toUInt64 <<< 16
            ||| (⟨b6.bv⟩ : UInt8).toUInt64 <<< 8
            ||| (⟨b7.bv⟩ : UInt8).toUInt64).toBitVec
    have h8 : BitVec.fromLEBytes [b7.bv, b6.bv, b5.bv, b4.bv, b3.bv, b2.bv, b1.bv, b0.bv]
        = BitVec.setWidth 64 b7.bv
          ||| ((BitVec.fromLEBytes [b6.bv, b5.bv, b4.bv, b3.bv, b2.bv, b1.bv, b0.bv]).setWidth 64 <<< 8) := rfl
    have h7 : BitVec.fromLEBytes [b6.bv, b5.bv, b4.bv, b3.bv, b2.bv, b1.bv, b0.bv]
        = BitVec.setWidth 56 b6.bv
          ||| ((BitVec.fromLEBytes [b5.bv, b4.bv, b3.bv, b2.bv, b1.bv, b0.bv]).setWidth 56 <<< 8) := rfl
    have h6 : BitVec.fromLEBytes [b5.bv, b4.bv, b3.bv, b2.bv, b1.bv, b0.bv]
        = BitVec.setWidth 48 b5.bv
          ||| ((BitVec.fromLEBytes [b4.bv, b3.bv, b2.bv, b1.bv, b0.bv]).setWidth 48 <<< 8) := rfl
    have h5 : BitVec.fromLEBytes [b4.bv, b3.bv, b2.bv, b1.bv, b0.bv]
        = BitVec.setWidth 40 b4.bv
          ||| ((BitVec.fromLEBytes [b3.bv, b2.bv, b1.bv, b0.bv]).setWidth 40 <<< 8) := rfl
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
    have hBE : BitVec.fromBEBytes [b0.bv, b1.bv, b2.bv, b3.bv,
                                    b4.bv, b5.bv, b6.bv, b7.bv]
        = BitVec.cast (by simp)
            (BitVec.fromLEBytes [b7.bv, b6.bv, b5.bv, b4.bv,
                                  b3.bv, b2.bv, b1.bv, b0.bv]) := rfl
    simp only [hBE, h8, h7, h6, h5, h4, h3, h2, h1, h0,
      UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64]
    simp [BitVec.setWidth_setWidth]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    interval_cases i <;> simp

open SHS.SHA512 in
/-- Corollary linking `core.num.U64.from_be_bytes` directly to
`Impl.beU64 (arrayU8ToVec block) ⟨j, hj⟩`, given that `chunk` is the
8-byte slice `[block[8j], block[8j+1], …, block[8j+7]]`.
The hypothesis is what the calling site materializes from the
`to_u64s` extracted closure. -/
theorem toUInt64_from_be_bytes_eq_beU64
    (block : Array U8 128#usize) (chunk : Array U8 8#usize)
    (j : Nat) (hj : j < 16)
    (hchunk : chunk.val = [block.val[8 * j]!, block.val[8 * j + 1]!,
                           block.val[8 * j + 2]!, block.val[8 * j + 3]!,
                           block.val[8 * j + 4]!, block.val[8 * j + 5]!,
                           block.val[8 * j + 6]!, block.val[8 * j + 7]!]) :
    toUInt64 (core.num.U64.from_be_bytes chunk) =
      Impl.beU64 (arrayU8ToVec block) ⟨j, hj⟩ := by
  rw [toUInt64_from_be_bytes, hchunk]
  simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
  unfold Impl.beU64
  have hidx : ∀ (i : Nat) (hi : i < 128),
      (arrayU8ToVec block)[i]'(by simp; omega) = toUInt8 (block.val[i]!) := fun i hi => by
    simp [arrayU8ToVec, hi, block.property]
  rw [← hidx (8 * j) (by omega), ← hidx (8 * j + 1) (by omega),
      ← hidx (8 * j + 2) (by omega), ← hidx (8 * j + 3) (by omega),
      ← hidx (8 * j + 4) (by omega), ← hidx (8 * j + 5) (by omega),
      ← hidx (8 * j + 6) (by omega), ← hidx (8 * j + 7) (by omega)]
  rfl

/-! ## Vector indexing through `arrayU64ToVec` -/

@[simp] theorem arrayU64ToVec_getElem
    {N : Usize} (block : Array U64 N) (i : Nat) (h : i < N.val)
    (h' : i < (arrayU64ToVec block).size := by simp [arrayU64ToVec]; omega) :
    (arrayU64ToVec block)[i]'h' =
      toUInt64 (block.val[i]'(by simpa [block.property] using h)) := by
  simp [arrayU64ToVec]

/-- The underlying `toList` of `arrayU64ToVec block` is `block.val.map toUInt64`. -/
@[simp] theorem arrayU64ToVec_toList {N : Usize} (block : Array U64 N) :
    (arrayU64ToVec block).toList = block.val.map toUInt64 := by
  simp [arrayU64ToVec]

/-- `getElem!`-form of `arrayU64ToVec` indexing. -/
@[simp] theorem arrayU64ToVec_getElem!
    {N : Usize} (block : Array U64 N) (i : Nat) :
    (arrayU64ToVec block).toList[i]! = toUInt64 (block.val[i]!) := by
  rw [arrayU64ToVec_toList]
  by_cases h : i < N.val <;> (simp [block.property, h]; try rfl)

/-! ## `arrayU64ToVec` of `Array.set` (used by SHA-512 schedule writes) -/

theorem arrayU64ToVec_set_toList
    {N : Usize} (block : Array U64 N) (i : Usize) (v : U64) :
    (arrayU64ToVec (block.set i v)).toList =
      (block.val.map toUInt64).set i.val (toUInt64 v) := by
  simp [arrayU64ToVec, Aeneas.Std.Array.set, List.map_set]

theorem arrayU64ToVec_set
    {N : Usize} (block : Array U64 N) (i : Usize) (v : U64)
    (hi : i.val < (arrayU64ToVec block).size) :
    arrayU64ToVec (block.set i v) =
      (arrayU64ToVec block).set i.val (toUInt64 v) hi := by
  apply Vector.toList_inj.mp; rw [arrayU64ToVec_set_toList, Vector.toList_set, arrayU64ToVec_toList]

/-! ## SHA-512 round-constant table equivalence -/

/-- Entry-wise equivalence between the Aeneas-extracted round constants
and the FIPS-spec `Impl.K64` table. -/
theorem K64_eq (i : Nat) (hi : i < 80) :
    toUInt64 ((Extraction.consts.K64 : Array U64 80#usize).val[i]!) =
      SHS.SHA512.Impl.K64[i]'(by simpa using hi) := by
  unfold Extraction.consts.K64; revert hi i; decide

/-! ## SHA-512 IV table equivalences -/

theorem H512_512_eq :
    arrayU64ToVec Extraction.consts.H512_512 = SHS.SHA512.Impl.H0_512 := by
  apply Vector.toList_inj.mp; unfold Extraction.consts.H512_512; decide

theorem H512_384_eq :
    arrayU64ToVec Extraction.consts.H512_384 = SHS.SHA512.Impl.H0_384 := by
  apply Vector.toList_inj.mp; unfold Extraction.consts.H512_384; decide

theorem H512_256_eq :
    arrayU64ToVec Extraction.consts.H512_256 = SHS.SHA512.Impl.H0_512_256 := by
  apply Vector.toList_inj.mp; unfold Extraction.consts.H512_256; decide

theorem H512_224_eq :
    arrayU64ToVec Extraction.consts.H512_224 = SHS.SHA512.Impl.H0_512_224 := by
  apply Vector.toList_inj.mp; unfold Extraction.consts.H512_224; decide
