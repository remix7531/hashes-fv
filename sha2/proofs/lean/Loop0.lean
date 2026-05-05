import U32
import ToU32s
import Compress
import equiv.SHA256.ToU32s
import Aeneas

/-!
# Per-block outer-loop bridge for `Extraction.sha256_inner_loop0`

Bridges Aeneas's per-block compression loop
`for i in 0..blocks { state ← compress_u32 state block_i }` to the
view-level `Fin.foldl blocks (Impl.compress · ∘ Impl.toU32sFromBytes)` over
the byte-array input. The outer-loop body extracts a 64-byte chunk, runs
`to_u32s` to obtain a 16-word block, then applies `compress_u32`. Each piece
has its own bridge lemma; this file glues them together via `range_loop_eq_finFoldl`.
-/

open Aeneas Aeneas.Std Result WP SHS.SHA256

/-! ## Byte-chunk view of one block -/

theorem arrayU8ToVec_eq_chunk_view
    (data : Slice U8) (i : Usize) (block : Array U8 64#usize)
    (hbound : i.val * 64 + 64 ≤ data.length)
    (hblock : ∀ (j : Nat) (hj : j < 64),
      block.val[j]'(by simpa [block.property] using hj) =
        data.val[i.val * 64 + j]'(by
          exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) hbound)) :
    arrayU8ToVec block =
      Vector.ofFn (fun j : Fin 64 =>
        (sliceToByteArray data).get! (i.val * 64 + j.val)) := by
  apply Vector.toArray_inj.mp
  rw [Vector.toArray_ofFn]
  show (block.val.map toUInt8).toArray = _
  apply Array.ext
  · simp [block.property]
  intro k h1 h2
  have hk64 : k < 64 := by simpa [block.property] using h1
  rw [Array.getElem_ofFn]
  rw [show ((block.val.map toUInt8).toArray)[k]'h1
        = toUInt8 (block.val[k]'(by simpa [block.property] using hk64)) by simp]
  rw [hblock k hk64]
  have hidx : i.val * 64 + k < data.val.length := by change ↑i * 64 + k < data.length; omega
  show toUInt8 _ = ByteArray.get! _ _
  unfold ByteArray.get!
  show toUInt8 _ = ((data.val.map toUInt8).toArray)[i.val * 64 + k]!
  rw [getElem!_pos _ _ (by simp; omega)]
  simp

/-! ## Per-iteration action spec -/

set_option maxHeartbeats 800000 in
theorem loop0_action_spec
    (data : Slice U8) (blocks : Usize) (state : Array U32 8#usize)
    (hbl : blocks.val * 64 ≤ data.length)
    (i : Usize) (h : i.val < blocks.val) :
    (do
      let i1 ← i * 64#usize
      let s ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeFromUsizeSlice U8) data
          { start := i1 }
      let s1 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeToUsizeSlice U8) s
          { «end» := 64#usize }
      let r ← core.array.TryFromSharedArraySlice.try_from 64#usize s1
      let block ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
      let s2 ← lift (Array.to_slice (Array.make 1#usize [ block ]))
      Extraction.sha256.compress256 state s2 : Result (Array U32 8#usize))
    ⦃ s' => arrayU32ToVec s' =
        Impl.compress (arrayU32ToVec state)
          (Impl.toU32sFromBytes (sliceToByteArray data) (i.val * 64)) ⦄ := by
  have hi64 : i.val * 64 + 64 ≤ data.length := by nlinarith
  step as ⟨i1, hi1⟩
  step with core.slice.index.SliceIndexRangeFromUsizeSlice.index.step_spec
    as ⟨s, hs_val, hs_len⟩
  step with core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec
    as ⟨s1, hs1_val, hs1_len⟩
  -- Inline try_from to .ok (.Ok block)
  unfold core.array.TryFromSharedArraySlice.try_from
  simp only [show s1.len = 64#usize from by
    apply UScalar.eq_of_val_eq; exact hs1_len, ↓reduceDIte, bind_tc_ok]
  simp only [core.result.Result.unwrap, bind_tc_ok]
  simp only [lift, Array.to_slice, bind_tc_ok]
  set block : Std.Array U8 64#usize := ⟨s1.val, by scalar_tac⟩ with hblock_def
  set bs : Slice (Std.Array U8 64#usize) := ⟨[block], by simp; scalar_tac⟩ with hbs_def
  show Extraction.sha256.compress256 state bs ⦃ _ ⦄
  apply spec_mono (compress256_spec state bs)
  intro out hout
  rw [hout]
  simp only [hbs_def, List.foldl_cons, List.foldl_nil]
  have hu32 : Impl.toU32s (arrayU8ToVec block) =
        Impl.toU32sFromBytes (sliceToByteArray data) (i.val * 64) := by
    rw [SHS.Equiv.SHA256.ToU32s.toU32sFromBytes_eq_toU32s]
    have hbck : arrayU8ToVec block =
        Vector.ofFn (fun j : Fin 64 =>
          (sliceToByteArray data).get! (i.val * 64 + j.val)) := by
      apply arrayU8ToVec_eq_chunk_view data i block hi64
      intro j hj
      show s1.val[j]'_ = data.val[i.val * 64 + j]'_
      have hs1_take : s1.val = (s.val).take 64 := by
        rw [hs1_val]; simp [List.slice]
      rw [List.getElem_of_eq hs1_take]
      rw [List.getElem_take]
      rw [List.getElem_of_eq hs_val]
      rw [List.getElem_drop]
      simp [hi1]
    rw [hbck]
  rw [hu32]

@[inline] def loop0_step (data : Slice U8) (blocks : Usize)
    (s : Vector UInt32 8) (_i : Fin blocks.val) : Vector UInt32 8 :=
  Impl.compress s (Impl.toU32sFromBytes (sliceToByteArray data) (_i.val * 64))

/-! ## Outer-loop fold -/

theorem sha256_inner_loop0_spec
    (data : Slice U8) (state : Array U32 8#usize) (blocks : Usize)
    (hbl : blocks.val * 64 ≤ data.length) :
    Extraction.sha256_inner_loop0 ⟨0#usize, blocks⟩ data state
    ⦃ out => arrayU32ToVec out =
        Fin.foldl blocks.val (loop0_step data blocks)
          (arrayU32ToVec state) ⦄ := by
  unfold Extraction.sha256_inner_loop0 Extraction.sha256_inner_loop0.body
  set action : Usize → Array U32 8#usize → Result (Array U32 8#usize) :=
    fun i state => do
      let i1 ← i * 64#usize
      let s ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeFromUsizeSlice U8) data
          { start := i1 }
      let s1 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeToUsizeSlice U8) s
          { «end» := 64#usize }
      let r ← core.array.TryFromSharedArraySlice.try_from 64#usize s1
      let block ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
      let s2 ← lift (Array.to_slice (Array.make 1#usize [ block ]))
      Extraction.sha256.compress256 state s2 with haction_def
  have haction_view : ∀ (i : Usize) (s : Array U32 8#usize) (h : i.val < blocks.val),
      action i s ⦃ s' => arrayU32ToVec s' = loop0_step data blocks
        (arrayU32ToVec s) ⟨i.val, h⟩ ⦄ := by
    intro i s h
    have hact := loop0_action_spec data blocks s hbl i h
    simp only [haction_def, loop0_step]
    exact hact
  classical
  set f' : Array U32 8#usize → Fin blocks.val → Array U32 8#usize :=
    fun s i =>
      match action ⟨i.val, by have := i.isLt; have hle := blocks.hBounds; omega⟩ s with
      | .ok v => v
      | .fail _ => s
      | .div => s with hf'_def
  have hf'_spec : ∀ (i : Usize) (s : Array U32 8#usize) (h : i.val < blocks.val),
      action i s ⦃ s' => s' = f' s ⟨i.val, h⟩ ⦄ := by
    intro i s h
    have hview := haction_view i s h
    simp only [spec, theta] at hview ⊢
    cases hact : action i s with
    | ok v =>
      rw [hact] at hview
      simp only [wp_return] at hview ⊢
      simp only [hf'_def]; rw [show (⟨i.val, by scalar_tac⟩ : Usize) = i from UScalar.eq_of_val_eq rfl, hact]
    | fail e => rw [hact] at hview; exact hview.elim
    | div => rw [hact] at hview; exact hview.elim
  have hf'_to_view : ∀ (i : Fin blocks.val) (s : Array U32 8#usize),
      arrayU32ToVec (f' s i) = loop0_step data blocks (arrayU32ToVec s) i := by
    intro i s
    have h1 := haction_view ⟨i.val, by have := i.isLt; have hle := blocks.hBounds; omega⟩ s i.isLt
    have h2 := hf'_spec ⟨i.val, by have := i.isLt; have hle := blocks.hBounds; omega⟩ s i.isLt
    simp only [spec, theta] at h1 h2
    cases hact : action ⟨i.val, _⟩ s with
    | ok v =>
      rw [hact] at h1 h2
      simp only [wp_return] at h1 h2
      exact h2 ▸ h1
    | fail e => rw [hact] at h1; exact h1.elim
    | div => rw [hact] at h1; exact h1.elim
  have hloop := range_loop_eq_finFoldl
    (N := blocks) (init := state) (f := f')
    (action := action) (haction := hf'_spec)
  have hfold_conv :
      ∀ (n : Nat) (hn : n ≤ blocks.val) (s : Array U32 8#usize),
        arrayU32ToVec
          (Fin.foldl n
            (fun st (i : Fin n) => f' st ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩) s) =
          Fin.foldl n
            (fun vs (i : Fin n) =>
              loop0_step data blocks vs ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩)
            (arrayU32ToVec s) := by
    intro n
    induction n with
    | zero =>
      intro hn s
      simp [Fin.foldl_zero]
    | succ k ih =>
      intro hn s
      have hk : k ≤ blocks.val := Nat.le_of_succ_le hn
      rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
      simp only [Fin.val_last]
      rw [hf'_to_view ⟨k, hn⟩ _]
      congr 1; exact ih hk s
  have hpost : ∀ (p : Array U32 8#usize), p = Fin.foldl blocks.val f' state →
      arrayU32ToVec p = Fin.foldl blocks.val (loop0_step data blocks) (arrayU32ToVec state) :=
    fun p hp => hp ▸ hfold_conv blocks.val le_rfl state
  refine spec_mono ?_ hpost
  -- Unfold `action` so the loop body syntactically matches `hloop`.
  rw [show action = fun i state => do
        let i1 ← i * 64#usize
        let s ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeFromUsizeSlice U8) data
            { start := i1 }
        let s1 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeToUsizeSlice U8) s
            { «end» := 64#usize }
        let r ← core.array.TryFromSharedArraySlice.try_from 64#usize s1
        let block ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
        let s2 ← lift (Array.to_slice (Array.make 1#usize [ block ]))
        Extraction.sha256.compress256 state s2 from haction_def] at hloop
  simp only [bind_assoc] at hloop
  exact hloop
