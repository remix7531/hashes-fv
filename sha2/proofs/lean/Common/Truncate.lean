import Common.U8

/-!
# Generic array truncation refinement

Bridges the Aeneas-extracted `core.array.Array.index` (with a
`..N` range) / `core.array.TryFromArrayCopySlice.try_from` /
`Result.unwrap` chain to `target.toList.take N` for arbitrary
`M, N : Usize` with `N ≤ M`.

Used by SHA-224 (28 from 32), SHA-384 (48 from 64),
SHA-512/224 (28 from 64), SHA-512/256 (32 from 64), and similar
truncations.
-/

open Aeneas Aeneas.Std Result WP

/-- The truncation chain `index ..N + try_from + unwrap` returns the
first `N` bytes of an `Array U8 M`. -/
theorem array_truncate_spec
    {M N : Usize} (hNM : N.val ≤ M.val)
    (state : Array U8 M)
    (target : Vector UInt8 M.val) (htarget : arrayU8ToVec state = target) :
    (do
      let s ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice U8)) state
          { «end» := N }
      let r ← core.array.TryFromArrayCopySlice.try_from N
                core.marker.CopyU8 s
      core.result.Result.unwrap core.fmt.DebugTryFromSliceError r)
    ⦃ out => (arrayU8ToVec out).toList = target.toList.take N.val ⦄ := by
  have hsv_len : state.val.length = M.val := by
    have := state.property; simp
  -- Step 1: `Array.index` reduces to slice indexing.
  step as ⟨s1, hs1_val, hs1_len⟩
  -- Step 2: `try_from` returns `.Ok` with `arr.val = s1.val`.
  have hlen_s1 : s1.length = N.val := by
    have := hs1_len; simpa using this
  have hclone : ∀ x : U8, core.marker.CopyU8.cloneInst.clone x = Result.ok x := by
    intro x; rfl
  apply spec_bind
    (core.array.TryFromArrayCopySlice.try_from.step_spec
       N core.marker.CopyU8 s1 hlen_s1 hclone)
  rintro r ⟨arr, hr_eq, harr_val⟩
  -- Step 3: `Result.unwrap` extracts the array.
  apply spec_mono
    (core.result.Result.unwrap.step_spec core.fmt.DebugTryFromSliceError r arr hr_eq)
  intro out hout
  rw [hout]
  have harr_eq : arr.val = state.val.take N.val := by
    rw [harr_val, hs1_val, List.slice_zero_j, Array.val_to_slice]
  have hLeq : (arrayU8ToVec arr).toList = arr.val.map toUInt8 := by
    show ((arr.val.map toUInt8).toArray).toList = arr.val.map toUInt8
    simp
  have hTeq : target.toList = state.val.map toUInt8 := by
    rw [← htarget]
    show ((state.val.map toUInt8).toArray).toList = state.val.map toUInt8
    simp
  rw [hLeq, harr_eq, hTeq, List.map_take]
