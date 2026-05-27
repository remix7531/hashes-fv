import Aeneas

/-!
# Word-size-agnostic byte helpers: Aeneas `Std.U8` ↔ Lean core `UInt8`

Conversions between Aeneas `U8` and Lean core `UInt8`, plus the
`Array U8 N` ↔ `Vector UInt8 N` and `Slice U8` ↔ `ByteArray` views.
These helpers are shared between the SHA-256 and (future) SHA-512
refinement proofs — neither set of byte plumbing depends on the
word size of the hash function.
-/

open Aeneas Aeneas.Std

/-! ## Scalar conversions -/

@[inline] def toUInt8  (x : U8)  : UInt8  := ⟨x.bv⟩
@[inline] def fromUInt8  (x : UInt8)  : U8  := ⟨x.toBitVec⟩

@[simp] theorem toUInt8_bv  (x : U8)  : (toUInt8 x).toBitVec  = x.bv := rfl
@[simp] theorem fromUInt8_bv  (x : UInt8)  : (fromUInt8 x).bv  = x.toBitVec := rfl

@[simp] theorem toUInt8_fromUInt8 (x : UInt8) : toUInt8 (fromUInt8 x) = x := rfl
@[simp] theorem fromUInt8_toUInt8 (x : U8) : fromUInt8 (toUInt8 x) = x := rfl

/-! ## `Array Std.U8 N` ↔ `Vector UInt8 N` -/

@[inline] def arrayU8ToVec {N : Usize} (a : Array U8 N) : Vector UInt8 N.val :=
  ⟨(a.val.map toUInt8).toArray, by simp [a.property]⟩

@[simp] theorem arrayU8ToVec_size {N : Usize} (a : Array U8 N) :
    (arrayU8ToVec a).size = N.val := by simp [arrayU8ToVec]

@[simp] theorem arrayU8ToVec_getElem
    {N : Usize} (block : Array U8 N) (i : Nat) (h : i < N.val)
    (h' : i < (arrayU8ToVec block).size := by simp [arrayU8ToVec]; omega) :
    (arrayU8ToVec block)[i]'h' =
      toUInt8 (block.val[i]'(by simpa [block.property] using h)) := by
  simp [arrayU8ToVec]

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
    rw [ByteArray.toList.loop]; simp [show ¬ i < bs.size from by omega]; omega
  | succ n ih =>
    have hlt : i < bs.size := by omega
    have hidata : i < bs.data.size := by simpa [← ByteArray.size_data] using hlt
    rw [ByteArray.toList.loop, if_pos hlt, ih (i + 1) (bs.get! i :: acc) hlt (by omega),
        show bs.get! i = bs.data[i]! from rfl, List.reverse_cons, List.append_assoc]
    fcongr 1
    simp [getElem!_pos bs.data i hidata, List.drop_eq_getElem_cons hidata, Array.getElem_toList]

/-- `toList` of `sliceToByteArray data` is the `toUInt8`-mapped slice data. -/
theorem sliceToByteArray_toList (data : Slice U8) :
    (sliceToByteArray data).toList = data.val.map toUInt8 := by
  rw [ByteArray.toList_eq_data_toList]; simp [sliceToByteArray]

/-! ## Byte-chunk view of one block

Generic over the chunk width `C : Usize`.  SHA-256 instantiates at `C = 64`,
SHA-512 at `C = 128`. -/

/-- The view-level shape `arrayU8ToVec block` of the `i`-th `C`-byte chunk of
`data` matches the `Vector.ofFn` view of the corresponding bytes of
`sliceToByteArray data`, as long as the chunk is in range and the entries
of `block` agree with `data` slot-by-slot. -/
theorem arrayU8ToVec_eq_chunk_view
    {C : Usize} (data : Slice U8) (i : Usize) (block : Array U8 C)
    (hbound : i.val * C.val + C.val ≤ data.length)
    (hblock : ∀ (j : Nat) (hj : j < C.val),
      block.val[j]'(by simpa [block.property] using hj) =
        data.val[i.val * C.val + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) hbound)) :
    arrayU8ToVec block =
      Vector.ofFn (fun j : Fin C.val =>
        (sliceToByteArray data).get! (i.val * C.val + j.val)) := by
  apply Vector.toArray_inj.mp
  rw [Vector.toArray_ofFn]
  apply Array.ext
  · simp [arrayU8ToVec, block.property]
  intro k h1 h2
  have hkC : k < C.val := by simpa [arrayU8ToVec, block.property] using h1
  simp [arrayU8ToVec, Array.getElem_ofFn, hblock k hkC, ByteArray.get!,
    show i.val * C.val + k < data.val.length from by change ↑i * C.val + k < data.length; omega]
