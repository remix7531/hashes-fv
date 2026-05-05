import Extraction
import impl.SHA256
import Mathlib.Tactic.IntervalCases

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
@[inline] def toUInt8  (x : U8)  : UInt8  := ⟨x.bv⟩
@[inline] def fromUInt32 (x : UInt32) : U32 := ⟨x.toBitVec⟩
@[inline] def fromUInt8  (x : UInt8)  : U8  := ⟨x.toBitVec⟩

@[simp] theorem toUInt32_bv (x : U32) : (toUInt32 x).toBitVec = x.bv := rfl
@[simp] theorem toUInt8_bv  (x : U8)  : (toUInt8 x).toBitVec  = x.bv := rfl
@[simp] theorem fromUInt32_bv (x : UInt32) : (fromUInt32 x).bv = x.toBitVec := rfl
@[simp] theorem fromUInt8_bv  (x : UInt8)  : (fromUInt8 x).bv  = x.toBitVec := rfl

@[simp] theorem toUInt32_fromUInt32 (x : UInt32) : toUInt32 (fromUInt32 x) = x := rfl
@[simp] theorem fromUInt32_toUInt32 (x : U32) : fromUInt32 (toUInt32 x) = x := rfl
@[simp] theorem toUInt8_fromUInt8 (x : UInt8) : toUInt8 (fromUInt8 x) = x := rfl
@[simp] theorem fromUInt8_toUInt8 (x : U8) : fromUInt8 (toUInt8 x) = x := rfl

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
  simp [BitVec.toNat_sub, Nat.mod_eq_of_lt, hn2]
  congr 2
  have h : (4294967296 : Nat) = 32 * 134217728 := by norm_num
  omega

/-! ## `Array Std.U32 N` ↔ `Vector UInt32 N` -/

@[inline] def arrayU32ToVec {N : Usize} (a : Array U32 N) : Vector UInt32 N.val :=
  ⟨(a.val.map toUInt32).toArray, by simp [a.property]⟩

@[inline] def arrayU8ToVec {N : Usize} (a : Array U8 N) : Vector UInt8 N.val :=
  ⟨(a.val.map toUInt8).toArray, by simp [a.property]⟩

@[simp] theorem arrayU32ToVec_size {N : Usize} (a : Array U32 N) :
    (arrayU32ToVec a).size = N.val := by simp [arrayU32ToVec]

@[simp] theorem arrayU8ToVec_size {N : Usize} (a : Array U8 N) :
    (arrayU8ToVec a).size = N.val := by simp [arrayU8ToVec]

/-! ## Big-endian 4-byte decode bridge -/

open SHS.SHA256 in
/-- The four-byte BE decoder in Aeneas's stdlib equals the shift-or chain
that `Impl.beU32` materializes. -/
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
  have hlen : block.val.length = 64 := block.property
  have hidx : ∀ (i : Nat) (hi : i < 64),
      (arrayU8ToVec block)[i]'(by simp; omega)
        = toUInt8 (block.val[i]!) := by
    intro i hi
    show (List.map toUInt8 block.val).toArray[i]'(by simp; omega) = _
    simp [getElem!_pos, hi, hlen]
  rw [← hidx (4 * j) (by omega), ← hidx (4 * j + 1) (by omega),
      ← hidx (4 * j + 2) (by omega), ← hidx (4 * j + 3) (by omega)]
  rfl

/-! ## Vector indexing through `arrayU32ToVec` / `arrayU8ToVec` -/

@[simp] theorem arrayU32ToVec_getElem
    {N : Usize} (block : Array U32 N) (i : Nat) (h : i < N.val)
    (h' : i < (arrayU32ToVec block).size := by simp [arrayU32ToVec]; omega) :
    (arrayU32ToVec block)[i]'h' =
      toUInt32 (block.val[i]'(by simpa [block.property] using h)) := by
  show ((block.val.map toUInt32).toArray)[i]'(by simpa [arrayU32ToVec] using h') = _
  simp

@[simp] theorem arrayU8ToVec_getElem
    {N : Usize} (block : Array U8 N) (i : Nat) (h : i < N.val)
    (h' : i < (arrayU8ToVec block).size := by simp [arrayU8ToVec]; omega) :
    (arrayU8ToVec block)[i]'h' =
      toUInt8 (block.val[i]'(by simpa [block.property] using h)) := by
  show ((block.val.map toUInt8).toArray)[i]'(by simpa [arrayU8ToVec] using h') = _
  simp

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
  by_cases h : i < N.val
  · simp [block.property, h]
  · simp [block.property, h]; rfl

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
  apply Vector.toList_inj.mp
  rw [arrayU32ToVec_set_toList, Vector.toList_set, arrayU32ToVec_toList]

/-- Sanity check that `arrayU32ToVec_set` fires on a goal of the
shape arising in the i ≥ 16 schedule-write branch. -/
example (block : Array U32 16#usize) (i : Usize) (v : U32) (hi : i.val < 16) :
    arrayU32ToVec (block.set i v) =
      (arrayU32ToVec block).set i.val (toUInt32 v)
        (by simp; exact hi) := by
  rw [arrayU32ToVec_set]

/-! ## `Slice U8 → ByteArray` view

A `ByteArray` whose underlying `data : Array UInt8` matches the
Aeneas slice's logical contents (mapped through `toUInt8`). -/

/-- Materialize a `ByteArray` from a `Slice U8` via `toUInt8`. -/
def sliceToByteArray (data : Slice U8) : ByteArray :=
  ⟨(data.val.map toUInt8).toArray⟩

@[simp] theorem sliceToByteArray_data (data : Slice U8) :
    (sliceToByteArray data).data = (data.val.map toUInt8).toArray := rfl

@[simp] theorem sliceToByteArray_size (data : Slice U8) :
    (sliceToByteArray data).size = data.length := by
  simp [sliceToByteArray, ByteArray.size, Slice.length]

/-- For any `ByteArray`, `toList` equals the underlying array's `toList`. -/
theorem ByteArray.toList_eq_data_toList (bs : ByteArray) :
    bs.toList = bs.data.toList := by
  -- Generalize over loop accumulator and starting index.
  suffices h : ∀ (i : Nat) (acc : List UInt8),
      i ≤ bs.size →
      ByteArray.toList.loop bs i acc =
        acc.reverse ++ (bs.data.toList.drop i) by
    have := h 0 [] (Nat.zero_le _)
    simpa [ByteArray.toList] using this
  intro i acc hi
  induction k : bs.size - i generalizing i acc with
  | zero =>
    have hnlt : ¬ i < bs.size := by omega
    rw [ByteArray.toList.loop]
    simp [hnlt]
    omega
  | succ n ih =>
    have hlt : i < bs.size := by omega
    rw [ByteArray.toList.loop]
    simp [hlt]
    rw [ih (i + 1) (bs.get! i :: acc) hlt (by omega)]
    rw [show bs.get! i = bs.data[i]! from rfl, List.reverse_cons, List.append_assoc]
    congr 1
    have hidata : i < bs.data.size := by simpa [← ByteArray.size_data] using hlt
    rw [getElem!_pos bs.data i hidata, List.drop_eq_getElem_cons hidata]
    simp [Array.getElem_toList]

/-! ## SHA-256 round-constant table equivalence -/

/-- Unfold the Aeneas-extracted `K32` constants table to a literal list.
The Aeneas definition is marked `@[irreducible]`, so we expose its body
behind a non-irreducible name. -/
private theorem sha2_K32_val :
    (Extraction.consts.K32 : Array U32 64#usize).val =
      [1116352408#u32, 1899447441#u32, 3049323471#u32, 3921009573#u32,
       961987163#u32, 1508970993#u32, 2453635748#u32, 2870763221#u32,
       3624381080#u32, 310598401#u32, 607225278#u32, 1426881987#u32,
       1925078388#u32, 2162078206#u32, 2614888103#u32, 3248222580#u32,
       3835390401#u32, 4022224774#u32, 264347078#u32, 604807628#u32,
       770255983#u32, 1249150122#u32, 1555081692#u32, 1996064986#u32,
       2554220882#u32, 2821834349#u32, 2952996808#u32, 3210313671#u32,
       3336571891#u32, 3584528711#u32, 113926993#u32, 338241895#u32,
       666307205#u32, 773529912#u32, 1294757372#u32, 1396182291#u32,
       1695183700#u32, 1986661051#u32, 2177026350#u32, 2456956037#u32,
       2730485921#u32, 2820302411#u32, 3259730800#u32, 3345764771#u32,
       3516065817#u32, 3600352804#u32, 4094571909#u32, 275423344#u32,
       430227734#u32, 506948616#u32, 659060556#u32, 883997877#u32,
       958139571#u32, 1322822218#u32, 1537002063#u32, 1747873779#u32,
       1955562222#u32, 2024104815#u32, 2227730452#u32, 2361852424#u32,
       2428436474#u32, 2756734187#u32, 3204031479#u32, 3329325298#u32] := by
  unfold Extraction.consts.K32
  rfl

/-- Entry-wise equivalence between the Aeneas-extracted round constants
and the FIPS-spec `Impl.K32` table. -/
theorem K32_eq (i : Nat) (hi : i < 64) :
    toUInt32 ((Extraction.consts.K32 : Array U32 64#usize).val[i]!) =
      SHS.SHA256.Impl.K32[i]'(by simpa using hi) := by
  rw [sha2_K32_val]
  revert hi
  revert i
  decide

/-! ## SHA-256 initial-hash-value table equivalence -/

/-- Unfold the Aeneas-extracted `H256_256` constants table to a literal list.
The Aeneas definition is marked `@[irreducible]`, so we expose its body
behind a non-irreducible name. -/
private theorem sha2_H256_256_val :
    (Extraction.consts.H256_256 : Array U32 8#usize).val =
      [1779033703#u32, 3144134277#u32, 1013904242#u32, 2773480762#u32,
       1359893119#u32, 2600822924#u32, 528734635#u32, 1541459225#u32] := by
  unfold Extraction.consts.H256_256
  rfl

/-- The Aeneas-extracted SHA-256 IV bridges to the FIPS-spec `Impl.H256_256`. -/
theorem H256_256_eq :
    arrayU32ToVec Extraction.consts.H256_256 = SHS.SHA256.Impl.H256_256 := by
  apply Vector.toList_inj.mp
  rw [arrayU32ToVec_toList, sha2_H256_256_val]
  decide


