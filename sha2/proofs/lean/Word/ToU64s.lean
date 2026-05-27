import Word.U64

/-!
# Refinement: `Extraction.sha512.to_u64s` ↔ `SHS.SHA512.Impl.toU64s`

Parallel to `ToU32s.lean` at 64-bit width: the Aeneas extraction expresses
`to_u64s` as `core::array::from_fn(|i| u64::from_be_bytes(block[8*i..][..8]))`.
The matching Impl-side function is `Vector.ofFn (beU64 ·)`.
-/

open Aeneas Aeneas.Std Result WP SHS.SHA512

/-- Closure body: produces the BE-decoded `U64` at word index `j` from
the eight bytes `block₀[8*j..8*j+8]` and threads the closure state
unchanged. -/
theorem to_u64s_closure_call_mut_spec
    (block₀ block : Extraction.sha512.to_u64s.closure) (j : Usize)
    (hj : j.val < 16) (hinv : block = block₀) :
    Extraction.sha512.to_u64s.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut block j
    ⦃ (val, block') => block' = block₀ ∧
        toUInt64 val = Impl.beU64 (arrayU8ToVec block₀) ⟨j.val, by omega⟩ ⦄ := by
  unfold Extraction.sha512.to_u64s.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  step; step; step
  step with core.array.TryFromArrayCopySlice.try_from.step_spec
    (copyInst := core.marker.CopyU8) (hclone := fun _ => rfl)
    as ⟨ chunk_arr, hOk, hchunk_val ⟩
  rw [hchunk_val]
  simp only [core.result.Result.unwrap, lift, bind_tc_ok]
  refine ⟨hinv, ?_⟩
  apply toUInt64_from_be_bytes_eq_beU64 block₀ chunk_arr j.val hj
  rename_i hchunk_eq_s1
  -- chunk_arr.val = take 8 (drop (8*j) block₀.val)
  rw [hchunk_eq_s1, s1_post1, s_post1, show (Array.to_slice block).val = block.val from rfl,
      i_post, hinv,
      show List.slice 0 8 (List.drop (8 * j.val) block₀.val) =
           List.take 8 (List.drop (8 * j.val) block₀.val) from by simp [List.slice]]
  have hlen : block₀.val.length = 128 := block₀.property
  have htake8 : (List.take 8 (List.drop (8 * j.val) block₀.val)).length = 8 :=
    List.length_take_of_le (by simp [List.length_drop, hlen]; omega)
  refine List.ext_getElem (by simp [htake8]) (fun i h1 _ => ?_)
  rw [List.getElem_take, List.getElem_drop,
      ← getElem!_pos block₀.val (8 * j.val + i) (by omega)]
  match i, htake8 ▸ h1 with | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl

/-- `to_u64s block` succeeds and equals `Impl.toU64s` after the U64-bridge
view conversion. -/
theorem to_u64s_spec (block : Array U8 128#usize) :
    Extraction.sha512.to_u64s block
    ⦃ arr => arrayU64ToVec arr = Impl.toU64s (arrayU8ToVec block) ⦄ := by
  unfold Extraction.sha512.to_u64s core.array.from_fn
  apply WP.spec_mono
  · apply core.array.from_fn_aux_state_spec 16#usize
        Extraction.sha512.to_u64s.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
        (inv := fun b => b = block)
        (P := fun b j v => j < 16 ∧
              ∀ hj : j < 16, toUInt64 v = Impl.beU64 (arrayU8ToVec b) ⟨j, hj⟩)
        (hcall := ?_)
        (Pmono := ?_)
        (f := block) (hf := rfl) (i := 0) (acc := []) (hacc := by simp) (hi := by scalar_tac)
        (hpre := by intro j hj; omega)
    · intro b' j hj hinv
      have h := to_u64s_closure_call_mut_spec block b' j hj hinv
      simp only [spec, theta] at h ⊢
      revert h
      set call :=
        Extraction.sha512.to_u64s.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
          b' j
      /- Three arms (cdot form to avoid the MISSION-banned named-constructor
         `cases ... with | ok ... | ...`). Named hypotheses (`hfail`,
         `hdiv`) per arm keep the two elim-form proofs distinct so Lean's
         auto-generated `._proof_N` names cannot collide. -/
      cases call
      · -- ok p: dispatch the postcondition
        rename_i p
        intro h
        simp only [wp_return] at h ⊢
        exact ⟨h.1, hj, fun _ => hinv ▸ h.2⟩
      · -- fail _: WP of `fail` is `False`, eliminate
        intro hfail
        exact hfail.elim
      · -- div: WP of `div` is `False`, eliminate
        intro hdiv
        exact hdiv.elim
    · intro f f' j v hf hf' hP; subst hf hf'; exact hP
  · intro arr h
    refine Vector.ext fun k hk => ?_
    have hkl : k < arr.val.length := by scalar_tac
    have hPj := (h k hk).2 hk
    have e1 : (arrayU64ToVec arr)[k]'hk = toUInt64 (arr.val[k]'hkl) := by simp [arrayU64ToVec]
    rw [e1, show arr.val[k]'hkl = arr.val[k]! from (getElem!_pos arr.val k hkl).symm, hPj]
    unfold Impl.toU64s; exact (Vector.getElem_ofFn hk).symm
