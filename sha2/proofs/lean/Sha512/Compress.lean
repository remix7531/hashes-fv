import Sha512.RoundStep
import Sha512.SetChain
import Common.Vec
import Common.Wp

/-!
# Refinement of `compress_u64` and `compress512` against `SHS.SHA512.Impl`

64-bit analogue of `Sha256/Compress.lean`.  Unlike SHA-256 — which uses
one fused `compress_u32_loop` — SHA-512's `compress_u64` has two
separate Aeneas loops (`loop0` schedule extension over indices 16..80,
`loop1` 80-round mix), so the per-loop specs are stated separately and
joined in `compress_u64_spec`.

`compress_u64_spec` joins the per-loop specs via `fin_foldl_split 16 80`,
gated by `arrayU64ToVec_schedule_copy` (the [0,16) block copy bridge);
no `sorry`s remain.
-/

open Aeneas Aeneas.Std Result WP SHS.SHA512
open SHS.Equiv.SHA512.Compress.Impl
open SHS.Equiv.Loop

/-! ## 64-step loop1 ↔ Fin.foldl over `tupledRoundStep64` -/

theorem compress_u64_loop1_spec
    (w : Array U64 80#usize) (a b c d e f g h : U64) :
    Extraction.sha512.soft_compact.compress_u64_loop1
        { start := 0#usize, «end» := 80#usize } a b c d e f g h w
    ⦃ r =>
      let init : UInt64 × UInt64 × UInt64 × UInt64 ×
                 UInt64 × UInt64 × UInt64 × UInt64 :=
        (toUInt64 a, toUInt64 b, toUInt64 c, toUInt64 d,
         toUInt64 e, toUInt64 f, toUInt64 g, toUInt64 h)
      let final := Fin.foldl 80
        (fun s (i : Fin 80) => tupledRoundStep64 (arrayU64ToVec w) i.val s) init
      let (a', b', c', d', e', f', g', h') := r
      toUInt64 a' = final.1 ∧ toUInt64 b' = final.2.1 ∧
      toUInt64 c' = final.2.2.1 ∧ toUInt64 d' = final.2.2.2.1 ∧
      toUInt64 e' = final.2.2.2.2.1 ∧ toUInt64 f' = final.2.2.2.2.2.1 ∧
      toUInt64 g' = final.2.2.2.2.2.2.1 ∧ toUInt64 h' = final.2.2.2.2.2.2.2 ⦄ := by
  set init : UInt64 × UInt64 × UInt64 × UInt64 ×
             UInt64 × UInt64 × UInt64 × UInt64 :=
    (toUInt64 a, toUInt64 b, toUInt64 c, toUInt64 d,
     toUInt64 e, toUInt64 f, toUInt64 g, toUInt64 h)
  unfold Extraction.sha512.soft_compact.compress_u64_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize ×
        U64 × U64 × U64 × U64 × U64 × U64 × U64 × U64) =>
      80 - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Usize ×
        U64 × U64 × U64 × U64 × U64 × U64 × U64 × U64) =>
      p.1.«end».val = 80 ∧ p.1.start.val ≤ 80 ∧
      let cur : UInt64 × UInt64 × UInt64 × UInt64 ×
          UInt64 × UInt64 × UInt64 × UInt64 :=
        (toUInt64 p.2.1, toUInt64 p.2.2.1, toUInt64 p.2.2.2.1,
         toUInt64 p.2.2.2.2.1, toUInt64 p.2.2.2.2.2.1,
         toUInt64 p.2.2.2.2.2.2.1, toUInt64 p.2.2.2.2.2.2.2.1,
         toUInt64 p.2.2.2.2.2.2.2.2)
      cur = partialFinFoldl 80
              (fun s (i : Fin 80) => tupledRoundStep64 (arrayU64ToVec w) i.val s)
              p.1.start.val init)
  · rintro ⟨iter, a', b', c', d', e', f', g', h'⟩ ⟨hend, hle, hcur⟩
    by_cases hlt : iter.start.val < 80
    · -- Step case
      obtain ⟨r, hev, start', aN, bN, cN, dN, eN, fN, gN, hN,
              hstart_val, hr_eq, ha_eq, hb_eq, hc_eq, hd_eq,
              he_eq, hf_eq, hg_eq, hh_eq⟩ :=
        ok_of_spec (compress_u64_loop1_body_spec w iter a' b' c' d' e' f' g' h' hlt hend)
      subst hr_eq
      simp only [spec, theta, hev, wp_return]
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · exact hend
      · show start'.val ≤ 80; scalar_tac
      · show (toUInt64 aN, toUInt64 bN, toUInt64 cN, toUInt64 dN,
              toUInt64 eN, toUInt64 fN, toUInt64 gN, toUInt64 hN) =
             partialFinFoldl 80
               (fun s (i : Fin 80) => tupledRoundStep64 (arrayU64ToVec w) i.val s)
               start'.val init
        rw [hstart_val,
            partialFinFoldl_succ 80
              (fun s (i : Fin 80) => tupledRoundStep64 (arrayU64ToVec w) i.val s)
              iter.start.val hlt,
            ← hcur]
        simp [*]
      · show 80 - start'.val < 80 - iter.start.val; scalar_tac
    · -- Done case
      have hnlt : ¬ iter.start.val < iter.«end».val := by scalar_tac
      simp only [Extraction.sha512.soft_compact.compress_u64_loop1.body,
        core.iter.range.IteratorRange.next_Usize_def,
        hnlt, ↓reduceIte, bind_tc_ok, spec, theta]
      rw [show iter.start.val = 80 from by scalar_tac, partialFinFoldl_full] at hcur
      simpa [Prod.ext_iff] using hcur
  · refine ⟨rfl, ?_, ?_⟩
    · show (0#usize : Usize).val ≤ 80; decide
    · show (toUInt64 a, toUInt64 b, toUInt64 c, toUInt64 d,
            toUInt64 e, toUInt64 f, toUInt64 g, toUInt64 h) =
           partialFinFoldl 80
             (fun s (i : Fin 80) => tupledRoundStep64 (arrayU64ToVec w) i.val s)
             (0#usize : Usize).val init
      rw [show ((0#usize : Usize).val) = 0 from rfl, partialFinFoldl_zero]

/-! ## Schedule-extension loop0 ↔ Fin.foldl over `extScheduleStep` -/

theorem compress_u64_loop0_spec
    (w : Array U64 80#usize) :
    Extraction.sha512.soft_compact.compress_u64_loop0
        { start := 16#usize, «end» := 80#usize } w
    ⦃ w' =>
      arrayU64ToVec w' =
        Fin.foldl 64
          (fun sched (i : Fin 64) => extScheduleStep (16 + i.val) sched)
          (arrayU64ToVec w) ⦄ := by
  set init : SHS.SHA512.Impl.Schedule := arrayU64ToVec w
  unfold Extraction.sha512.soft_compact.compress_u64_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × Array U64 80#usize) =>
      80 - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Usize × Array U64 80#usize) =>
      p.1.«end».val = 80 ∧ 16 ≤ p.1.start.val ∧ p.1.start.val ≤ 80 ∧
      arrayU64ToVec p.2 =
        partialFinFoldl 64
          (fun sched (i : Fin 64) => extScheduleStep (16 + i.val) sched)
          (p.1.start.val - 16) init)
  · rintro ⟨iter, w'⟩ ⟨hend, hlo, hle, hcur⟩
    by_cases hlt : iter.start.val < 80
    · -- Step case
      obtain ⟨r, hev, start', w'', hstart_val, hr_eq, hext⟩ :=
        ok_of_spec (compress_u64_loop0_body_spec iter w' hlo hlt hend)
      subst hr_eq
      simp only [spec, theta, hev, wp_return]
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · exact hend
      · show 16 ≤ start'.val; scalar_tac
      · show start'.val ≤ 80; scalar_tac
      · -- Partial fold extends by one step.
        show arrayU64ToVec w'' =
               partialFinFoldl 64
                 (fun sched (i : Fin 64) => extScheduleStep (16 + i.val) sched)
                 (start'.val - 16) init
        have hbnd : iter.start.val - 16 < 64 := by scalar_tac
        rw [show start'.val - 16 = (iter.start.val - 16) + 1 from by scalar_tac,
            partialFinFoldl_succ 64
              (fun sched (i : Fin 64) => extScheduleStep (16 + i.val) sched)
              (iter.start.val - 16) hbnd,
            ← hcur,
            show (⟨iter.start.val - 16, hbnd⟩ : Fin 64).val = iter.start.val - 16
              from rfl,
            show 16 + (iter.start.val - 16) = iter.start.val from by scalar_tac]
        exact hext
      · show 80 - start'.val < 80 - iter.start.val; scalar_tac
    · -- Done case: iter.start = 80
      have hnlt : ¬ iter.start.val < iter.«end».val := by scalar_tac
      simp only [Extraction.sha512.soft_compact.compress_u64_loop0.body,
        core.iter.range.IteratorRange.next_Usize_def,
        hnlt, ↓reduceIte, bind_tc_ok, spec, theta]
      rw [show iter.start.val - 16 = 64 from by scalar_tac, partialFinFoldl_full] at hcur
      exact hcur
  · -- Initial invariant
    refine ⟨rfl, ?_, ?_, ?_⟩
    · show 16 ≤ (16#usize : Usize).val; decide
    · show (16#usize : Usize).val ≤ 80; decide
    · show arrayU64ToVec w =
           partialFinFoldl 64
             (fun sched (i : Fin 64) => extScheduleStep (16 + i.val) sched)
             ((16#usize : Usize).val - 16) init
      rw [show ((16#usize : Usize).val - 16) = 0 from rfl, partialFinFoldl_zero]

/-! ## Single-block compression -/

/-! ## Helper: `arrayU64ToVec` of the schedule after the [0,16) block copy

After `index_mut [..16] + copy_from_slice block`, the schedule (length-80,
zero-initialized) has slots `[0,16)` filled with `block`'s words and slots
`[16,80)` still zero.  We need this shape to match the result of the
first 16 steps of `implScheduleFoldl`. -/

private theorem arrayU64ToVec_schedule_copy
    (block : Array U64 16#usize) (w1 : Array U64 80#usize)
    (hw1_val : w1.val =
      (Array.repeat 80#usize (0#u64 : U64)).val.setSlice! 0 block.val) :
    arrayU64ToVec w1 =
      (Fin.foldl 16
        (fun (w : SHS.SHA512.Impl.Schedule) (i : Fin 16) =>
          w.set i.val ((arrayU64ToVec block).toList[i.val]!)
            (Nat.lt_of_lt_of_le i.isLt (by decide)))
        (Vector.replicate 80 0) :
       SHS.SHA512.Impl.Schedule) := by
  /- Both sides have length 80; compare element-by-element. -/
  apply Vector.ext; intro k hk
  have hk80 : k < 80 := by simpa using hk
  /- LHS: pull through the map. -/
  have hblen : block.val.length = 16 := block.property
  /- Closed form for the foldl's [k] entry: if k < 16 then toUInt64 block.val[k]!
     else 0.  Prove via partialFinFoldl induction over the fold count. -/
  have hFfold_get : ∀ (n : Nat) (_hn : n ≤ 16),
      (partialFinFoldl 16
        (fun (w : SHS.SHA512.Impl.Schedule) (i : Fin 16) =>
          w.set i.val ((arrayU64ToVec block).toList[i.val]!)
            (Nat.lt_of_lt_of_le i.isLt (by decide)))
        n (Vector.replicate 80 0))[k]'hk =
      if k < n then ((arrayU64ToVec block).toList[k]!)
      else (0 : UInt64) := by
    intro n hn
    induction n with
    | zero => simp [partialFinFoldl_zero]
    | succ j ih =>
      have hj : j < 16 := hn
      rw [partialFinFoldl_succ 16 _ j hj]
      have ih' := ih (Nat.le_of_lt hj)
      rw [Vector.getElem_set (hi := Nat.lt_of_lt_of_le hj (by decide))]
      by_cases heq : j = k
      · subst heq; simp [show j < j + 1 from Nat.lt_succ_self _]
      · simp only [heq, ↓reduceIte]
        rw [ih']
        by_cases hklt : k < j
        · simp [hklt, show k < j + 1 from Nat.lt_succ_of_lt hklt]
        · simp [hklt, show ¬ k < j + 1 from by scalar_tac]
  have hfold_at_k := hFfold_get 16 (le_refl _)
  rw [partialFinFoldl_full] at hfold_at_k
  /- LHS: arrayU64ToVec w1 at k. -/
  have hw1_len : w1.val.length = 80 := w1.property
  /- LHS rewrite: lift `(arrayU64ToVec w1)[k]` to `toUInt64 (w1.val[k])`. -/
  rw [show (arrayU64ToVec w1)[k]'hk =
        toUInt64 (w1.val[k]'(by rw [hw1_len]; exact hk80))
      from by simp [arrayU64ToVec]]
  /- RHS rewrite via hfold_at_k.  The goal's RHS bound is `k < ↑80#usize`
     while hfold_at_k uses `k < 80`.  Bridge via explicit normal form. -/
  refine .trans ?_ hfold_at_k.symm
  /- Massage the LHS: `(↑w1)[k]` has bound that depends on `↑w1.length`;
     bridge to `w1.val[k]'(< 80)` form to make `rw [hw1_val]` work. -/
  have hk_in_w1 : k < w1.val.length := by rw [hw1_len]; exact hk80
  show toUInt64 (w1.val[k]'hk_in_w1) =
    if k < 16 then (arrayU64ToVec block).toList[k]! else (0 : UInt64)
  by_cases hk16 : k < 16
  · /- k < 16: w1.val[k] = block.val[k]. -/
    simp only [hk16, ↓reduceIte]
    rw [(getElem!_pos w1.val k hk_in_w1).symm, hw1_val,
        List.getElem!_setSlice!_middle _ _ 0 k (by simp [hblen, Array.repeat_val]; scalar_tac),
        Nat.sub_zero, getElem!_pos block.val k (by rw [hblen]; exact hk16),
        arrayU64ToVec_toList]
    simp [hblen, hk16]
  · /- k ≥ 16: w1.val[k] = 0. -/
    simp only [hk16, ↓reduceIte]
    rw [(getElem!_pos w1.val k hk_in_w1).symm, hw1_val,
        List.getElem!_setSlice!_suffix _ _ 0 k (by rw [hblen]; scalar_tac),
        Array.repeat_val,
        getElem!_pos (List.replicate 80#usize.val (0#u64 : U64)) k
          (by rw [List.length_replicate]; exact hk80),
        List.getElem_replicate]
    rfl

/-! ## Single-block compression -/

set_option maxHeartbeats 1000000 in
theorem compress_u64_spec
    (state : Array U64 8#usize) (block : Array U64 16#usize) :
    Extraction.sha512.soft_compact.compress_u64 state block
    ⦃ out => arrayU64ToVec out =
        SHS.SHA512.Impl.compress (arrayU64ToVec state) (arrayU64ToVec block) ⦄ := by
  unfold Extraction.sha512.soft_compact.compress_u64
  step ; step ; step ; step ; step ; step ; step ; step
  /- Schedule construction phase. -/
  step as ⟨discr1, hd1⟩
  obtain ⟨s, index_mut_back⟩ := discr1
  step as ⟨s1, hs1_val⟩
  apply spec_bind (core.slice.Slice.copy_from_slice.step_spec _ s s1
    (by rw [hd1.2.1, hs1_val]; simp [Slice.length]))
  intro s2 hs2_eq
  set w1 : Array U64 80#usize := index_mut_back s2 with hw1_def
  have hw1_val : w1.val =
      (Array.repeat 80#usize (0#u64 : U64)).val.setSlice! 0 block.val := by
    rw [hw1_def, hd1.2.2 s2,
        show s2.val = block.val from by rw [← hs2_eq, hs1_val]; simp [Array.val_to_slice]]
  /- View through arrayU64ToVec: w1 is the first-16-fold over Vector.replicate 80 0. -/
  have hw1_to_vec := arrayU64ToVec_schedule_copy block w1 hw1_val
  /- Loop0: extend the schedule over slots [16,80). -/
  apply spec_bind (compress_u64_loop0_spec w1)
  intro w2 hw2_eq
  /- Loop1: 80-round mix. -/
  apply spec_bind (compress_u64_loop1_spec w2 a b c d e f g h)
  rintro ⟨a1, b1, c1, d1, e1, f1, g1, h1⟩ ⟨ha1, hb1, hc1, hd1', he1, hf1, hg1, hh1⟩
  /- Final 24 monadic steps (8 state reads + 8 wrapping_adds + 8 state writes). -/
  step ; step ; step ; step ; step ; step ; step ; step
  step ; step ; step ; step ; step ; step ; step ; step
  step ; step ; step ; step ; step ; step ; step ; step
  /- Rename `i`-binder to avoid shadow with outer `out`. -/
  rename_i i i_post
  /- Bridge to Impl.compress via the foldl form. -/
  rw [← SHS.Equiv.SHA512.Compress.Impl.impl_compress_eq_foldl]
  unfold SHS.Equiv.SHA512.Compress.Impl.implCompressFoldl
  /- Rewrite Impl.messageSchedule via its foldl form. -/
  simp only [SHS.Equiv.SHA512.Compress.Impl.messageSchedule_eq_foldl]
  unfold SHS.Equiv.SHA512.Compress.Impl.implScheduleFoldl
  /- Split the 80-fold at index 16. -/
  /- Show the schedule fold's result equals `arrayU64ToVec w2`. -/
  have hsched_eq :
      Fin.foldl 80
        (fun (w : SHS.SHA512.Impl.Schedule) (t : Fin 80) =>
          SHS.Equiv.SHA512.Compress.Impl.implScheduleStep (arrayU64ToVec block) t.val w)
        (Vector.replicate 80 0 : SHS.SHA512.Impl.Schedule) = arrayU64ToVec w2 := by
    let fInit : SHS.SHA512.Impl.Schedule := Vector.replicate 80 0
    let fStep : SHS.SHA512.Impl.Schedule → Fin 80 → SHS.SHA512.Impl.Schedule :=
      fun w (t : Fin 80) =>
        SHS.Equiv.SHA512.Compress.Impl.implScheduleStep (arrayU64ToVec block) t.val w
    show Fin.foldl 80 fStep fInit = arrayU64ToVec w2
    /- fStep splits as: copyStep for t < 16, extStep for t ≥ 16. -/
    let copyStep : Nat → SHS.SHA512.Impl.Schedule → SHS.SHA512.Impl.Schedule :=
      fun n w =>
        if hn : n < 16 then
          w.set n ((arrayU64ToVec block).toList[n]!)
            (Nat.lt_of_lt_of_le hn (by decide))
        else w
    have hfStep_split :
        ∀ (w : SHS.SHA512.Impl.Schedule) (t : Fin 80),
          fStep w t =
            (if t.val < 16 then copyStep t.val w else extScheduleStep t.val w) := fun w t => by
      simp only [fStep, SHS.Equiv.SHA512.Compress.Impl.implScheduleStep,
                 extScheduleStep, copyStep]
      by_cases ht : t.val < 16
      · simp only [ht, ↓reduceIte, ↓reduceDIte]
        have h80 : t.val < 80 := t.isLt
        show Vector.set! w t.val (arrayU64ToVec block)[t.val]! =
             Vector.set w t.val ((arrayU64ToVec block).toList[t.val]!) h80
        rw [vector_set!_eq_set_of_lt _ _ _ h80]
        fcongr 1; rw [arrayU64ToVec_toList]; simp [block.property, ht]
      · simp only [ht, ↓reduceIte]
    rw [show Fin.foldl 80 fStep fInit =
          Fin.foldl 80
            (fun w (t : Fin 80) =>
              if t.val < 16 then copyStep t.val w else extScheduleStep t.val w) fInit from by
      fcongr 1; funext w t; exact hfStep_split w t]
    rw [fin_foldl_split 16 80 (by decide) copyStep extScheduleStep fInit]
    /- The inner [0,16) fold is the copyStep fold; it equals arrayU64ToVec w1. -/
    have hinner : Fin.foldl 16 (fun s (i : Fin 16) => copyStep i.val s) fInit =
        arrayU64ToVec w1 := by
      rw [hw1_to_vec]; fcongr 1; funext w (t : Fin 16)
      simp only [copyStep, t.isLt, ↓reduceDIte]
    /- The outer [16,80) fold is the extension; show it matches loop0. -/
    rw [hinner, hw2_eq]
    /- Show the two outer folds match. -/
    fcongr 1; funext w (i : Fin 64); fcongr 1; scalar_tac
  simp only [hsched_eq]
  /- Now the round-mix fold needs bridging via finFoldl_roundStep64_eq_tupled. -/
  set init_st : SHS.SHA512.Impl.State :=
    #v[toUInt64 a, toUInt64 b, toUInt64 c, toUInt64 d,
       toUInt64 e, toUInt64 f, toUInt64 g, toUInt64 h]
  set init_tup : UInt64 × UInt64 × UInt64 × UInt64 ×
                 UInt64 × UInt64 × UInt64 × UInt64 :=
    (toUInt64 a, toUInt64 b, toUInt64 c, toUInt64 d,
     toUInt64 e, toUInt64 f, toUInt64 g, toUInt64 h)
  /- We need: arrayU64ToVec state = init_st (after the 8 state reads, each
     state element [k] = a..h's value). -/
  have hstate_init : arrayU64ToVec state = init_st := by
    apply Vector.ext; intro k hk; simp only [init_st]
    have hk8 : k < 8 := by simpa using hk
    rw [arrayU64ToVec_getElem state k hk8]; interval_cases k <;> (simp [getElem!_pos, *]; rfl)
  /- Bridge: project init_st to init_tup (trivially equal by definition). -/
  have hinit_proj :
      (init_st[0], init_st[1], init_st[2], init_st[3],
       init_st[4], init_st[5], init_st[6], init_st[7]) = init_tup := by simp [init_st, init_tup]
  have hbridge := finFoldl_roundStep64_eq_tupled (arrayU64ToVec w2) init_st init_tup hinit_proj
  /- Project the 8 components and combine with the loop1 spec. -/
  simp only [Prod.ext_iff] at hbridge
  obtain ⟨ha, hb, hc, hd, he, hf, hg, hh⟩ := hbridge
  simp only [← ha1, ← hb1, ← hc1, ← hd1', ← he1, ← hf1, ← hg1, ← hh1] at ha hb hc hd he hf hg hh
  /- Final state write chain. -/
  have set_get_ne : ∀ {N : Usize} (a : Aeneas.Std.Array U64 N) (j : Usize) (v : U64) (k : ℕ),
      j.val ≠ k → (a.set j v).val[k]! = a.val[k]! := fun _ _ _ k hjk => by
    show (_root_.List.set _ _ _)[k]! = _; simp [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne hjk]
  have hlen : state.val.length = 8 := state.property
  have hi : i = state.val[0]! := i_post
  have hi2 : i2 = state.val[1]! := by rw [i2_post, state1_post]; repeat rw [set_get_ne _ _ _ _ (by decide)]
  have hi4 : i4 = state.val[2]! := by rw [i4_post, state2_post, state1_post]; repeat rw [set_get_ne _ _ _ _ (by decide)]
  have hi6 : i6 = state.val[3]! := by rw [i6_post, state3_post, state2_post, state1_post]; repeat rw [set_get_ne _ _ _ _ (by decide)]
  have hi8 : i8 = state.val[4]! := by rw [i8_post, state4_post, state3_post, state2_post, state1_post]; repeat rw [set_get_ne _ _ _ _ (by decide)]
  have hi10 : i10 = state.val[5]! := by rw [i10_post, state5_post, state4_post, state3_post, state2_post, state1_post]; repeat rw [set_get_ne _ _ _ _ (by decide)]
  have hi12 : i12 = state.val[6]! := by rw [i12_post, state6_post, state5_post, state4_post, state3_post, state2_post, state1_post]; repeat rw [set_get_ne _ _ _ _ (by decide)]
  have hi14 : i14 = state.val[7]! := by rw [i14_post, state7_post, state6_post, state5_post, state4_post, state3_post, state2_post, state1_post]; repeat rw [set_get_ne _ _ _ _ (by decide)]
  rw [out_post, state7_post, state6_post, state5_post, state4_post, state3_post,
      state2_post, state1_post, arrayU64ToVec_set8_chain,
      i1_post, i3_post, i5_post, i7_post, i9_post, i11_post, i13_post, i15_post,
      hi, hi2, hi4, hi6, hi8, hi10, hi12, hi14]
  simp only [core.num.U64.wrapping_add, toUInt64_wrapping_add]
  have hgv : ∀ (k : Nat) (hk : k < 8),
      (arrayU64ToVec state)[k]'(by simp; scalar_tac) = toUInt64 (state.val[k]!) := fun k hk => by
    rw [arrayU64ToVec_getElem state k hk (by simp; scalar_tac),
        getElem!_pos _ _ (by simp [hlen]; scalar_tac)]
  /- The final state is #v[init_st[0] + final[0], ..., init_st[7] + final[7]].
     But we computed in terms of arrayU64ToVec state.  Bridge through hstate_init. -/
  simp only [← hgv 0 (by decide), ← hgv 1 (by decide), ← hgv 2 (by decide),
             ← hgv 3 (by decide), ← hgv 4 (by decide), ← hgv 5 (by decide),
             ← hgv 6 (by decide), ← hgv 7 (by decide),
             ← ha, ← hb, ← hc, ← hd, ← he, ← hf, ← hg, ← hh,
             hstate_init, init_st]
  rfl

/-! ## Multi-block compression -/

theorem compress512_spec
    (state : Array U64 8#usize) (blocks : Slice (Array U8 128#usize)) :
    Extraction.sha512.compress512 state blocks
    ⦃ out => arrayU64ToVec out =
        blocks.val.foldl
          (fun s (b : Array U8 128#usize) =>
            SHS.SHA512.Impl.compress s (SHS.SHA512.Impl.toU64s (arrayU8ToVec b)))
          (arrayU64ToVec state) ⦄ := by
  unfold Extraction.sha512.compress512 Extraction.sha512.soft_compact.compress
    Extraction.sha512.soft_compact.compress_loop
  simp only [core.slice.Slice.iter, bind_tc_ok,
    Extraction.sha512.soft_compact.compress_loop.body]
  set f : Vector UInt64 8 → Array U8 128#usize → Vector UInt64 8 :=
    fun s b => SHS.SHA512.Impl.compress s (SHS.SHA512.Impl.toU64s (arrayU8ToVec b)) with hf
  set action : Array U8 128#usize → Array U64 8#usize → Result (Array U64 8#usize) :=
    fun b s => do
      let words ← Extraction.sha512.to_u64s b
      Extraction.sha512.soft_compact.compress_u64 s words with haction_def
  have haction_view :
      ∀ (b : Array U8 128#usize) (s : Array U64 8#usize),
        action b s ⦃ s' => arrayU64ToVec s' = f (arrayU64ToVec s) b ⦄ := fun b s => by
    simp only [haction_def]
    apply spec_bind (to_u64s_spec b); intro words hwords
    apply spec_mono (compress_u64_spec s words)
    intro out hout; simp only [hf]; rw [hout, hwords]
  classical
  set f' : Array U64 8#usize → Array U8 128#usize → Array U64 8#usize :=
    fun s b =>
      match action b s with
      | .ok v => v
      | .fail _ => s
      | .div => s with hf'_def
  have hf'_spec :
      ∀ (b : Array U8 128#usize) (s : Array U64 8#usize),
        action b s ⦃ s' => s' = f' s b ⦄ := fun b s => by
    obtain ⟨v, hact, _⟩ := ok_of_spec (haction_view b s)
    simp only [hf'_def, hact]; rw [spec_ok]
  have hf'_to_f : ∀ (b : Array U8 128#usize) (s : Array U64 8#usize),
      arrayU64ToVec (f' s b) = f (arrayU64ToVec s) b := fun b s => by
    obtain ⟨v, hact, hpost⟩ := ok_of_spec (haction_view b s)
    simp only [hf'_def, hact]; exact hpost
  have hloop := slice_iter_loop_eq_foldl
    (slice₀ := blocks) (init := state) (f := f')
    (action := action) (haction := hf'_spec)
  have hfold_conv : ∀ (l : List (Array U8 128#usize)) (s : Array U64 8#usize),
      arrayU64ToVec (l.foldl f' s) = l.foldl f (arrayU64ToVec s) := fun l => by
    induction l with
    | nil => intro s; simp
    | cons b bs ih => intro s; simp only [List.foldl_cons]; rw [ih, hf'_to_f]
  simp only [haction_def, bind_assoc] at hloop
  refine spec_mono ?_ (fun p (hp : p = _) => hp ▸ hfold_conv _ _)
  convert hloop using 2
  funext p; fcongr 1; funext ⟨o, _⟩; cases o <;> rfl
