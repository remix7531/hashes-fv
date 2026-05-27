import Word.U64
import Word.ToU64s
import Sha512.Compress
import Common.Wp
import equiv.SHA512.ToU64s
import Aeneas

/-!
# Per-block outer-loop bridge for `Extraction.sha512_inner_loop0`

64-bit analogue of `Sha256/Loop0.lean`.  Bridges Aeneas's per-block
compression loop `for i in 0..blocks { state ← compress512 state block_i }`
to `Fin.foldl blocks (Impl.compress · ∘ Impl.toU64sFromBytes)` over the
byte-array input.
-/

open Aeneas Aeneas.Std Result WP SHS.SHA512

/-- The per-block fold-step viewed at the spec level. -/
@[inline] def loop0_step_512 (data : Slice U8) (blocks : Usize)
    (s : Vector UInt64 8) (i : Fin blocks.val) : Vector UInt64 8 :=
  SHS.SHA512.Impl.compress s
    (SHS.SHA512.Impl.toU64sFromBytes (sliceToByteArray data) (i.val * 128))

-- Per-iteration action spec — port of `Sha256/Loop0.lean`'s `loop0_action_spec`.
set_option maxHeartbeats 800000 in
private theorem loop0_action_spec_512
    (data : Slice U8) (blocks : Usize) (state : Array U64 8#usize)
    (hbl : blocks.val * 128 ≤ data.length)
    (i : Usize) (h : i.val < blocks.val) :
    (do
      let i1 ← i * 128#usize
      let s ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeFromUsizeSlice U8) data
          { start := i1 }
      let s1 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeToUsizeSlice U8) s
          { «end» := 128#usize }
      let r ← core.array.TryFromSharedArraySlice.try_from 128#usize s1
      let block ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
      let s2 ← lift (Array.to_slice (Array.make 1#usize [ block ]))
      Extraction.sha512.compress512 state s2 : Result (Array U64 8#usize))
    ⦃ s' => arrayU64ToVec s' =
        SHS.SHA512.Impl.compress (arrayU64ToVec state)
          (SHS.SHA512.Impl.toU64sFromBytes (sliceToByteArray data) (i.val * 128)) ⦄ := by
  have hi128 : i.val * 128 + 128 ≤ data.length := by scalar_tac +nonLin
  step as ⟨i1, hi1⟩
  step with core.slice.index.SliceIndexRangeFromUsizeSlice.index.step_spec
    as ⟨s, hs_val, hs_len⟩
  step with core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec
    as ⟨s1, hs1_val, hs1_len⟩
  unfold core.array.TryFromSharedArraySlice.try_from
  simp only [show s1.len = 128#usize from UScalar.eq_of_val_eq hs1_len, ↓reduceDIte,
             bind_tc_ok, core.result.Result.unwrap, lift, Array.to_slice]
  set block : Std.Array U8 128#usize := ⟨s1.val, by scalar_tac⟩ with hblock_def
  set bs : Slice (Std.Array U8 128#usize) := ⟨[block], by agrind⟩ with hbs_def
  show Extraction.sha512.compress512 state bs ⦃ _ ⦄
  apply spec_mono (compress512_spec state bs)
  intro out hout; rw [hout]
  simp only [hbs_def, List.foldl_cons, List.foldl_nil]
  have hu64 : SHS.SHA512.Impl.toU64s (arrayU8ToVec block) =
        SHS.SHA512.Impl.toU64sFromBytes (sliceToByteArray data) (i.val * 128) := by
    rw [SHS.Equiv.SHA512.ToU64s.toU64sFromBytes_eq_toU64s]
    have hbck : arrayU8ToVec block =
        Vector.ofFn (fun j : Fin 128 =>
          (sliceToByteArray data).get! (i.val * 128 + j.val)) := by
      apply arrayU8ToVec_eq_chunk_view data i block hi128
      intro j hj; show s1.val[j]'_ = data.val[i.val * 128 + j]'_
      have hs1_take : s1.val = (s.val).take 128 := by rw [hs1_val]; simp [List.slice]
      rw [List.getElem_of_eq hs1_take, List.getElem_take,
          List.getElem_of_eq hs_val, List.getElem_drop]
      agrind
    rw [hbck]
  rw [hu64]

/-- Outer per-block loop refinement. -/
theorem sha512_inner_loop0_spec
    (data : Slice U8) (state : Array U64 8#usize) (blocks : Usize)
    (hbl : blocks.val * 128 ≤ data.length) :
    Extraction.sha512_inner_loop0 ⟨0#usize, blocks⟩ data state
    ⦃ out => arrayU64ToVec out =
        Fin.foldl blocks.val (loop0_step_512 data blocks)
          (arrayU64ToVec state) ⦄ := by
  unfold Extraction.sha512_inner_loop0 Extraction.sha512_inner_loop0.body
  set action : Usize → Array U64 8#usize → Result (Array U64 8#usize) :=
    fun i state => do
      let i1 ← i * 128#usize
      let s ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeFromUsizeSlice U8) data
          { start := i1 }
      let s1 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeToUsizeSlice U8) s
          { «end» := 128#usize }
      let r ← core.array.TryFromSharedArraySlice.try_from 128#usize s1
      let block ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
      let s2 ← lift (Array.to_slice (Array.make 1#usize [ block ]))
      Extraction.sha512.compress512 state s2 with haction_def
  have haction_view : ∀ (i : Usize) (s : Array U64 8#usize) (h : i.val < blocks.val),
      action i s ⦃ s' => arrayU64ToVec s' = loop0_step_512 data blocks
        (arrayU64ToVec s) ⟨i.val, h⟩ ⦄ := by
    intro i s h; simp only [haction_def, loop0_step_512]
    exact loop0_action_spec_512 data blocks s hbl i h
  classical
  set f' : Array U64 8#usize → Fin blocks.val → Array U64 8#usize :=
    fun s i => match action ⟨i.val, by agrind⟩ s with
      | .ok v => v | _ => s with hf'_def
  have hf'_spec : ∀ (i : Usize) (s : Array U64 8#usize) (h : i.val < blocks.val),
      action i s ⦃ s' => s' = f' s ⟨i.val, h⟩ ⦄ := by
    intro i s h; obtain ⟨v, hact, _⟩ := ok_of_spec (haction_view i s h)
    simp only [hf'_def,
      show (⟨i.val, by scalar_tac⟩ : Usize) = i from UScalar.eq_of_val_eq rfl, hact]; rw [spec_ok]
  have hf'_to_view : ∀ (i : Fin blocks.val) (s : Array U64 8#usize),
      arrayU64ToVec (f' s i) = loop0_step_512 data blocks (arrayU64ToVec s) i := by
    intro i s; obtain ⟨v, hact, hpost⟩ := ok_of_spec (haction_view ⟨i.val, by agrind⟩ s i.isLt)
    simp only [hf'_def, hact]; exact hpost
  have hloop := range_loop_eq_finFoldl (N := blocks) (init := state) (f := f')
    (action := action) (haction := hf'_spec)
  have hfold_conv :
      ∀ (n : Nat) (hn : n ≤ blocks.val) (s : Array U64 8#usize),
        arrayU64ToVec
          (Fin.foldl n
            (fun st (i : Fin n) => f' st ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩) s) =
          Fin.foldl n
            (fun vs (i : Fin n) =>
              loop0_step_512 data blocks vs ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩)
            (arrayU64ToVec s) := by
    intro n; induction n with
    | zero => simp [Fin.foldl_zero]
    | succ k ih =>
      intro hn s
      rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
      simp only [Fin.val_last]; rw [hf'_to_view ⟨k, hn⟩ _]
      exact congrArg (loop0_step_512 data blocks · ⟨k, hn⟩) (ih (Nat.le_of_succ_le hn) s)
  have hpost : ∀ (p : Array U64 8#usize), p = Fin.foldl blocks.val f' state →
      arrayU64ToVec p = Fin.foldl blocks.val (loop0_step_512 data blocks) (arrayU64ToVec state) :=
    fun p hp => hp ▸ hfold_conv blocks.val le_rfl state
  refine spec_mono ?_ hpost
  simp only [haction_def, bind_assoc] at hloop
  exact hloop
