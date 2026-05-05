import U32
import Aeneas

/-!
# Refinement: `Extraction.sha256.to_u32s` ↔ `SHS.SHA256.Impl.toU32s`

The Aeneas extraction expresses `to_u32s` as
`core::array::from_fn(|i| u32::from_be_bytes(block[4*i..][..4]))`. The
matching Impl-side function is `Vector.ofFn (beU32 ·)`.

`core.array.from_fn_aux_state_spec` (upstream Aeneas) lets us track
that the closure preserves its state, so the per-index predicate can
refer to the original block bytes.
-/

open Aeneas Aeneas.Std Result WP SHS.SHA256

/-- Closure body: produces the BE-decoded `U32` at word index `j` from
the four bytes `block₀[4*j..4*j+4]` and threads the closure state
unchanged. The state-preservation conjunct lets the outer `from_fn`
induction propagate the predicate. -/
theorem to_u32s_closure_call_mut_spec
    (block₀ block : Extraction.sha256.to_u32s.closure) (j : Usize)
    (hj : j.val < 16) (hinv : block = block₀) :
    Extraction.sha256.to_u32s.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut block j
    ⦃ (val, block') => block' = block₀ ∧
        toUInt32 val = Impl.beU32 (arrayU8ToVec block₀) ⟨j.val, by omega⟩ ⦄ := by
  unfold Extraction.sha256.to_u32s.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  step
  step
  step
  step with core.array.TryFromArrayCopySlice.try_from.step_spec
    (copyInst := core.marker.CopyU8) (hclone := fun _ => rfl)
    as ⟨ chunk_arr, hOk, hchunk_val ⟩
  rw [hchunk_val]
  simp only [core.result.Result.unwrap, lift, bind_tc_ok]
  refine ⟨hinv, ?_⟩
  apply toUInt32_from_be_bytes_eq_beU32 block₀ chunk_arr j.val hj
  rename_i hchunk_eq_s1
  -- chunk_arr.val = take 4 (drop (4*j) block₀.val)
  rw [hchunk_eq_s1, s1_post1, s_post1, show (Array.to_slice block).val = block.val from rfl,
      i_post, hinv,
      show List.slice 0 4 (List.drop (4 * j.val) block₀.val) =
           List.take 4 (List.drop (4 * j.val) block₀.val) from by simp [List.slice]]
  have hlen : block₀.val.length = 64 := block₀.property
  have htake4 : (List.take 4 (List.drop (4 * j.val) block₀.val)).length = 4 :=
    List.length_take_of_le (by simp [List.length_drop, hlen]; omega)
  refine List.ext_getElem (by simp [htake4]) (fun i h1 _ => ?_)
  rw [List.getElem_take, List.getElem_drop,
      ← getElem!_pos block₀.val (4 * j.val + i) (by omega)]
  match i, htake4 ▸ h1 with
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl

/-- `to_u32s block` succeeds and equals `Impl.toU32s` after the U32-bridge
view conversion. The structural plumbing is here; `to_u32s_closure_call_mut_spec`
carries the byte-level reasoning. -/
theorem to_u32s_spec (block : Array U8 64#usize) :
    Extraction.sha256.to_u32s block
    ⦃ arr => arrayU32ToVec arr = Impl.toU32s (arrayU8ToVec block) ⦄ := by
  unfold Extraction.sha256.to_u32s core.array.from_fn
  apply WP.spec_mono
  · apply core.array.from_fn_aux_state_spec 16#usize
        Extraction.sha256.to_u32s.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
        (inv := fun b => b = block)
        (P := fun b j v => j < 16 ∧
              ∀ hj : j < 16, toUInt32 v = Impl.beU32 (arrayU8ToVec b) ⟨j, hj⟩)
        (hcall := ?_)
        (Pmono := ?_)
        (f := block) (hf := rfl) (i := 0) (acc := []) (hacc := by simp) (hi := by scalar_tac)
        (hpre := by intro j hj; omega)
    · intro b' j hj hinv
      have h := to_u32s_closure_call_mut_spec block b' j hj hinv
      simp only [spec, theta] at h ⊢
      revert h
      cases Extraction.sha256.to_u32s.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut b' j with
      | ok p =>
        intro h
        simp only [wp_return] at h ⊢
        refine ⟨h.1, hj, ?_⟩
        intro _; rw [hinv]; exact h.2
      | fail _ => intro h; exact h.elim
      | div => intro h; exact h.elim
    · intro f f' j v hf hf' hP
      subst hf; subst hf'; exact hP
  · intro arr h
    apply Vector.ext
    intro k hk
    have hk16 : k < 16 := hk
    have hkl : k < arr.val.length := by scalar_tac
    have hPj := (h k hk16).2 hk16
    have e1 : (arrayU32ToVec arr)[k]'hk = toUInt32 (arr.val[k]'hkl) := by
      unfold arrayU32ToVec; simp
    rw [e1, show arr.val[k]'hkl = arr.val[k]! from (getElem!_pos arr.val k hkl).symm, hPj]
    unfold Impl.toU32s; exact (Vector.getElem_ofFn hk16).symm
