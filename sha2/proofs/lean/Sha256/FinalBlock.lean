import Word.U32
import Common.U64
import Aeneas

/-!
# Padding-block byte-equality bridge for SHA-256's final block

The Aeneas extraction (`Extraction.sha256_inner`) builds the FIPS 180-4 §5.1.1
padded final block in four regions: data copy `[0, remaining)`, the
`0x80` marker at `remaining`, zeros up to byte 56, then the BE-encoded
bit-length at `[56, 64)`. The Impl-side spec
(`SHS.SHA256.Impl.sha256` in `fips-180-4-lean/impl/SHA256.lean`)
materializes the same regions via three `Vector.ofFn` snapshots
(`finalBlockA` after the marker write, `finalBlockB` post-branch, and
`finalBlockC` after the length-tag write).

This file's load-bearing lemma is `u64_be_bytes_match`: the `i`-th byte
of `core.num.U64.to_be_bytes total_bits` (Aeneas) equals
`((toUInt64 total_bits >>> ((63 - (56 + i)) * 8)) &&& 0xff).toUInt8`
(Impl-side `finalBlockC` byte at index `56 + i`). It reduces to the
shared `toUInt8_be_byte` lemma in `Common/U64.lean`, which in turn
reduces to the width-generic upstream-Aeneas lemma
`BitVec.toBEBytes_getElem!_eq_shift_mask`.
-/

open Aeneas Aeneas.Std Result WP SHS.SHA256

/-! ## Consumer-facing form of `Common.toUInt8_be_byte` at U64

The Impl side indexes the BE length bytes at `i` for `56 ≤ i < 64` via
`((totalBits >>> ((63 - i) * 8)) &&& 0xff).toUInt8`. With `i = 56 + k`
(`k < 8`), `63 - i = 7 - k`, matching the Aeneas-side `to_be_bytes`
position `k`. -/

theorem u64_be_bytes_match (total_bits : U64) (k : Nat) (hk : k < 8) :
    toUInt8 ((core.num.U64.to_be_bytes total_bits).val[k]!) =
      ((toUInt64 total_bits >>> (UInt64.ofNat ((63 - (56 + k)) * 8))) &&& 0xff).toUInt8 := by
  show toUInt8 ((total_bits.bv.toBEBytes.map (UScalar.mk (ty := .U8)) : List U8)[k]!) = _
  rw [toUInt8_be_byte total_bits k hk, show 63 - (56 + k) = 7 - k from by omega]

/-- The BV-shift on the U64-cast of `Slice.len data` agrees with the
Impl-side `data.size.toUInt64 <<< 3`. Pure scalar identity; the
length bound argument is unused but kept for caller symmetry. -/
theorem total_bits_bv_eq (data : Slice U8) (_h : data.length < 2 ^ 61) :
    ((UScalar.cast .U64 (Slice.len data)).bv <<< (3 : Nat)) =
      ((sliceToByteArray data).size.toUInt64 <<< 3).toBitVec := by
  show ((Slice.len data).bv.zeroExtend 64) <<< 3 = _
  rw [sliceToByteArray_size]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft]

/-- Byte-by-byte equality between the Aeneas-side
final block (post the `[56..64] ← to_be_bytes total_bits` write) and
the Impl-side `finalBlockC`.

**Contract.** Suppose `finalBlockB_bytes : Array U8 64#usize` has its
low 56 bytes (indices `0..56`) matching the spec's `finalBlockB`
post-branch shape (i.e. either `finalBlockA` in the <-arm, or all
zeros in the ≥-arm). Specifically, abstracted over the `finalBlockB`
spec value `vB : Vector UInt8 64`:

  ∀ i < 56, toUInt8 finalBlockB_bytes.val[i]! = vB[i]

Then after writing the 8 BE bytes of `total_bits` into indices
`[56, 64)`, the resulting array's `arrayU8ToVec` view equals the
spec's `finalBlockC` built from `vB` and `total_bits`.

This is the load-bearing combinatorial lemma: it walks through one
`core.array.Array.index_mut` (range `[56..64]`) + `to_be_bytes` +
`copy_from_slice` + `index_mut_back` chain, using
`u64_be_bytes_match` for the per-byte BE equality. -/
theorem padded_block_spec
    (finalBlockB_bytes : Array U8 64#usize)
    (vB : Vector UInt8 64)
    (hlow : ∀ (i : Nat) (hi : i < 56),
        toUInt8 (finalBlockB_bytes.val[i]'(by simp [finalBlockB_bytes.property]; omega)) =
          vB[i]'(by omega))
    (total_bits : U64) :
    (do
      let __discr ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeUsizeSlice U8)) finalBlockB_bytes
          { start := 56#usize, «end» := 64#usize }
      let a ← lift (core.num.U64.to_be_bytes total_bits)
      let s4 ← lift (Array.to_slice a)
      let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 __discr.1 s4
      ok (__discr.2 s5) : Result (Array U8 64#usize))
    ⦃ final_block3 => arrayU8ToVec final_block3 =
        (Vector.ofFn fun i : Fin 64 =>
          if i.val < 56 then vB[i]
          else ((toUInt64 total_bits >>>
                  (UInt64.ofNat ((63 - i.val) * 8))) &&& 0xff).toUInt8) ⦄ := by
  -- Walks `index_mut [56..64]` + `to_be_bytes` + `copy_from_slice` +
  -- `index_mut_back`, then `Vector.ext`. For `i < 56` both sides equal
  -- `vB[i]`; for `56 ≤ i < 64` they agree via `u64_be_bytes_match`.
  unfold core.array.Array.index_mut core.ops.index.IndexMutSlice
    core.slice.index.Slice.index_mut
    core.slice.index.SliceIndexRangeUsizeSlice
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut Array.to_slice
    core.slice.Slice.copy_from_slice
  have hfb_len : finalBlockB_bytes.val.length = 64 := finalBlockB_bytes.property
  simp only [show (56#usize : Usize) ≤ 64#usize ∧
      (↑(64#usize : Usize) : ℕ) ≤ finalBlockB_bytes.val.length
      from ⟨by decide, by simp [hfb_len]⟩,
    bind_tc_ok, lift, and_self, ↓reduceIte]
  have hlen_eq : Slice.len (⟨List.slice (↑(56#usize : Usize) : Nat) (↑(64#usize : Usize) : Nat)
        finalBlockB_bytes.val, by scalar_tac⟩ : Slice U8) =
      Slice.len (⟨(core.num.U64.to_be_bytes total_bits).val, by scalar_tac⟩ : Slice U8) := by
    apply UScalar.eq_of_val_eq; simp [List.slice, hfb_len]
  simp only [hlen_eq, ↓reduceIte, bind_tc_ok, spec, theta, wp_return, Array.from_slice]
  have hsetSlice_len : ((finalBlockB_bytes.val).setSlice!
      (↑(56#usize : Usize) : Nat) (core.num.U64.to_be_bytes total_bits).val).length =
      (64#usize : Usize).val := by simp [hfb_len]
  simp only [hsetSlice_len, ↓reduceDIte]
  apply Vector.toArray_inj.mp; rw [Vector.toArray_ofFn]
  show (((finalBlockB_bytes.val.setSlice! 56 (core.num.U64.to_be_bytes total_bits).val).map
      toUInt8).toArray : Array UInt8) = _
  apply Array.ext
  · simp
  intro k h1 _; have hk : k < 64 := by simp at h1; omega
  rw [Array.getElem_ofFn, List.getElem_toArray, List.getElem_map,
      ← getElem!_pos _ _ (by simp [hfb_len]; exact hk)]
  by_cases hk56 : k < 56
  · rw [List.getElem!_setSlice!_prefix _ _ 56 k hk56]
    show toUInt8 (finalBlockB_bytes.val[k]!) = _
    rw [getElem!_pos finalBlockB_bytes.val k (by omega)]
    show _ = if (⟨k, hk⟩ : Fin 64).val < 56 then _ else _
    rw [if_pos (show (⟨k, hk⟩ : Fin 64).val < 56 from hk56)]; exact hlow k hk56
  · push Not at hk56
    rw [List.getElem!_setSlice!_middle _ _ 56 k (⟨hk56, by simp; omega, by omega⟩)]
    show _ = if (⟨k, hk⟩ : Fin 64).val < 56 then _ else _
    rw [if_neg (show ¬ (⟨k, hk⟩ : Fin 64).val < 56 from by simp; omega)]
    show toUInt8 ((core.num.U64.to_be_bytes total_bits).val[k - 56]!) =
        ((toUInt64 total_bits >>> UInt64.ofNat ((63 - (⟨k, hk⟩ : Fin 64).val) * 8))
          &&& 255).toUInt8
    rw [u64_be_bytes_match total_bits (k - 56) (by omega)]
    show _ = ((toUInt64 total_bits >>> UInt64.ofNat ((63 - k) * 8)) &&& 255).toUInt8
    rw [show 63 - (56 + (k - 56)) = 63 - k from by omega]

/-! ## Iota-reshape for `padded_block_spec` consumers

Both arms of the `remaining ≥ 56` branch in `Sha2InnerSpec.lean` need to
reshape the `do`-block so the prefix matches `padded_block_spec`'s
statement (which uses `lift (core.num.U64.to_be_bytes total_bits)` and
`lift (Array.to_slice a)`). This is a pure monadic-laws rewrite — both
sides reduce to the same `bind`-tree once `lift` is unfolded. -/

/-- The fused `index_mut`-then-`copy_from_slice` `do`-block equals the
explicit `lift`-decomposed prefix used by `padded_block_spec`, threaded
through an arbitrary continuation `k`. Closes both reshape obligations
in `sha2_inner_spec` with a single one-liner per arm. -/
theorem padded_block_reshape {α : Type}
    (fb_initial : Array U8 64#usize) (total_bits : U64)
    (k : Array U8 64#usize → Result α) :
    (do
      let (s3, index_mut_back2) ←
        core.array.Array.index_mut (core.ops.index.IndexMutSlice
          (core.slice.index.SliceIndexRangeUsizeSlice U8))
          fb_initial { start := 56#usize, «end» := 64#usize }
      let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3
                 (core.num.U64.to_be_bytes total_bits).to_slice
      k (index_mut_back2 s5))
    = ((do
        let __discr ←
          core.array.Array.index_mut (core.ops.index.IndexMutSlice
            (core.slice.index.SliceIndexRangeUsizeSlice U8))
            fb_initial { start := 56#usize, «end» := 64#usize }
        let a ← lift (core.num.U64.to_be_bytes total_bits)
        let s4 ← lift (Array.to_slice a)
        let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 __discr.1 s4
        ok (__discr.2 s5)) >>= k) := by
  simp [lift, bind_tc_ok]

