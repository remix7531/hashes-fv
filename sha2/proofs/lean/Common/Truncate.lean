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

In addition to the low-level `array_truncate_spec`, this module
provides `inner_truncate_digest_spec` — a one-shot wrapper that
encapsulates the entire `inner_call >>= truncate_chain` pattern
used by the four truncated FIPS bridges (SHA-224, SHA-384,
SHA-512/256, SHA-512/224).
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
  -- Step 1: `Array.index` reduces to slice indexing.
  step as ⟨s1, hs1_val, hs1_len⟩
  -- Step 2: `try_from` returns `.Ok` with `arr.val = s1.val`.
  apply spec_bind
    (core.array.TryFromArrayCopySlice.try_from.step_spec
       N core.marker.CopyU8 s1 hs1_len (fun _ => rfl))
  rintro r ⟨arr, hr_eq, harr_val⟩
  -- Step 3: `Result.unwrap` extracts the array.
  apply spec_mono
    (core.result.Result.unwrap.step_spec core.fmt.DebugTryFromSliceError r arr hr_eq)
  intro out hout
  simp [hout, arrayU8ToVec, harr_val, hs1_val, List.slice_zero_j, Array.val_to_slice,
        ← htarget, List.map_take]

/-- Generic refinement for the `inner_call >>= truncate-chain` body shared by
SHA-224 / SHA-384 / SHA-512/256 / SHA-512/224. Given an inner-spec
witnessing `arrayU8ToVec inner_out = full` and a take-equality
`truncated.toList = full.toList.take N`, the composed action satisfies
`arrayU8ToVec out = truncated`.

Each caller (e.g., `sha224_impl_spec`) invokes this with:
  * `inner` = the `sha2_inner_spec[_512]` application at the relevant IV,
  * `take_eq` = the `Local.<algo>_eq_sha2Inner<256|512>_take` lemma. -/
theorem inner_truncate_digest_spec
    {M N : Usize} (hNM : N.val ≤ M.val)
    (inner : Result (Array U8 M))
    (full_digest : Vector UInt8 M.val) (truncated : Vector UInt8 N.val)
    (hinner : inner ⦃ out => arrayU8ToVec out = full_digest ⦄)
    (take_eq : truncated.toList = full_digest.toList.take N.val) :
    (do
      let inner_out ← inner
      let s ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeToUsizeSlice U8)) inner_out
          { «end» := N }
      let r ← core.array.TryFromArrayCopySlice.try_from N
                core.marker.CopyU8 s
      core.result.Result.unwrap core.fmt.DebugTryFromSliceError r)
    ⦃ out => arrayU8ToVec out = truncated ⦄ := by
  refine spec_bind hinner (fun inner_out hinner_out => ?_)
  refine spec_mono (array_truncate_spec hNM inner_out full_digest hinner_out) (fun out hout => ?_)
  exact Vector.toList_inj.mp (hout.trans take_eq.symm)
