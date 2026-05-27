import Sha256.RoundStep
import Sha256.SetChain
import Common.Wp

/-!
# Refinement of `compress_u32` and `compress256` against `SHS.SHA256.Impl`

Extracted from `Sha256.lean` so `Loop0.lean` can
use `compress256_spec` without the Loop0 → Sha256 → Loop0 import cycle.
-/

open Aeneas Aeneas.Std Result WP SHS.SHA256

/-! The per-round body bridge (`tupledRoundStep`,
`compress_u32_body_spec`, `finFoldl_roundStep_eq_tupled`,
plus the `rotr_bridge_*` family of literal-rotation lemmas) lives in
`RoundStep.lean`. -/


/-! ## 64-step loop ↔ Fin.foldl

Hooking Aeneas's `compress_u32_loop` into `Fin.foldl 64 tupledRoundStep`.
The bridge to `Fin.foldl 64 Impl.roundStep` over `Impl.RoundState` happens
one section down in `compress_u32_spec`, via `finFoldl_roundStep_eq_tupled`. -/

theorem compress_u32_loop_spec
    (block : Array U32 16#usize) (a b c d e f g h : U32) :
    Extraction.sha256.soft_compact.compress_u32_loop
        { start := 0#usize, «end» := 64#usize } block a b c d e f g h
    ⦃ r =>
      let init : Vector UInt32 16 × _ :=
        (arrayU32ToVec block,
         toUInt32 a, toUInt32 b, toUInt32 c, toUInt32 d,
         toUInt32 e, toUInt32 f, toUInt32 g, toUInt32 h)
      let final := Fin.foldl 64 (fun s i => tupledRoundStep i s) init
      let (a', b', c', d', e', f', g', h') := r
      toUInt32 a' = final.2.1 ∧ toUInt32 b' = final.2.2.1 ∧
      toUInt32 c' = final.2.2.2.1 ∧ toUInt32 d' = final.2.2.2.2.1 ∧
      toUInt32 e' = final.2.2.2.2.2.1 ∧ toUInt32 f' = final.2.2.2.2.2.2.1 ∧
      toUInt32 g' = final.2.2.2.2.2.2.2.1 ∧ toUInt32 h' = final.2.2.2.2.2.2.2.2 ⦄ := by
  -- Invariant: partial fold of `tupledRoundStep` over `Fin.foldl iter.start.val`.
  set init : Vector UInt32 16 × UInt32 × UInt32 × UInt32 × UInt32 ×
      UInt32 × UInt32 × UInt32 × UInt32 :=
    (arrayU32ToVec block,
     toUInt32 a, toUInt32 b, toUInt32 c, toUInt32 d,
     toUInt32 e, toUInt32 f, toUInt32 g, toUInt32 h) with hinit
  unfold Extraction.sha256.soft_compact.compress_u32_loop
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize ×
        Array U32 16#usize ×
        U32 × U32 × U32 × U32 × U32 × U32 × U32 × U32) =>
      64 - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Usize ×
        Array U32 16#usize ×
        U32 × U32 × U32 × U32 × U32 × U32 × U32 × U32) =>
      p.1.«end».val = 64 ∧ p.1.start.val ≤ 64 ∧
      let cur : Vector UInt32 16 × UInt32 × UInt32 × UInt32 × UInt32 ×
          UInt32 × UInt32 × UInt32 × UInt32 :=
        (arrayU32ToVec p.2.1,
         toUInt32 p.2.2.1, toUInt32 p.2.2.2.1, toUInt32 p.2.2.2.2.1,
         toUInt32 p.2.2.2.2.2.1, toUInt32 p.2.2.2.2.2.2.1,
         toUInt32 p.2.2.2.2.2.2.2.1, toUInt32 p.2.2.2.2.2.2.2.2.1,
         toUInt32 p.2.2.2.2.2.2.2.2.2)
      cur = partialFinFoldl 64 (fun s i => tupledRoundStep i s)
              p.1.start.val init)
  · rintro ⟨iter, block', a', b', c', d', e', f', g', h'⟩ ⟨hend, hle, hcur⟩
    simp only at hend hle hcur
    by_cases hlt : iter.start.val < 64
    · -- Step case: apply body spec, then close inv + measure.
      have hbody := compress_u32_body_spec iter block' a' b' c' d' e' f' g' h'
        hlt hend
      simp only [spec, theta] at hbody ⊢
      revert hbody
      cases hev : Extraction.sha256.soft_compact.compress_u32_loop.body iter block'
                    a' b' c' d' e' f' g' h' with
      | ok r =>
        intro hbody; simp only [wp_return] at hbody
        obtain ⟨start', blockN, aN, bN, cN, dN, eN, fN, gN, hN,
                hstart_val, hr_eq, hb_eq, ha_eq, hbb_eq, hc_eq, hd_eq,
                he_eq, hf_eq, hg_eq, hh_eq⟩ := hbody
        subst hr_eq; simp only [wp_return]
        refine ⟨⟨hend, by show start'.val ≤ 64; omega, ?_⟩,
                by show 64 - start'.val < 64 - iter.start.val; omega⟩
        -- Partial fold extends by one step.
        show (arrayU32ToVec blockN,
              toUInt32 aN, toUInt32 bN, toUInt32 cN, toUInt32 dN,
              toUInt32 eN, toUInt32 fN, toUInt32 gN, toUInt32 hN) =
             partialFinFoldl 64
               (fun s i => tupledRoundStep i s) start'.val init
        rw [hstart_val,
            partialFinFoldl_succ 64
              (fun s i => tupledRoundStep i s) iter.start.val hlt init,
            ← hcur]
        simp [hb_eq, ha_eq, hbb_eq, hc_eq, hd_eq, he_eq, hf_eq, hg_eq, hh_eq]
      | fail _ => intro h; exact h.elim
      | div => intro h; exact h.elim
    · -- Done case: iter.start = iter.end = 64.
      have hstart_eq : iter.start.val = 64 := by omega
      simp only [Extraction.sha256.soft_compact.compress_u32_loop.body,
        core.iter.range.IteratorRange.next_Usize_def]
      have hnlt : ¬ iter.start.val < iter.«end».val := by rw [hend]; omega
      simp only [hnlt, ↓reduceIte, bind_tc_ok, spec, theta]
      have hfull : partialFinFoldl 64
                     (fun s i => tupledRoundStep i s) iter.start.val init =
                   Fin.foldl 64 (fun s i => tupledRoundStep i s) init := by
        rw [hstart_eq, partialFinFoldl_full]
      rw [hfull] at hcur
      simp only [Prod.ext_iff] at hcur
      obtain ⟨-, ha', hb', hc', hd', he', hf', hg', hh'⟩ := hcur
      exact ⟨ha', hb', hc', hd', he', hf', hg', hh'⟩
  · -- Initial invariant
    refine ⟨rfl, ?_, ?_⟩
    · show (0#usize : Usize).val ≤ 64; decide
    · show (arrayU32ToVec block, toUInt32 a, toUInt32 b, toUInt32 c, toUInt32 d,
            toUInt32 e, toUInt32 f, toUInt32 g, toUInt32 h) =
           partialFinFoldl 64
             (fun s i => tupledRoundStep i s) (0#usize : Usize).val init
      rw [show ((0#usize : Usize).val) = 0 from rfl, partialFinFoldl_zero]; rfl

/-! ## Single-block compression -/

set_option maxHeartbeats 1000000 in
theorem compress_u32_spec
    (state : Array U32 8#usize) (block : Array U32 16#usize) :
    Extraction.sha256.soft_compact.compress_u32 state block
    ⦃ out => arrayU32ToVec out =
        Impl.compress (arrayU32ToVec state) (arrayU32ToVec block) ⦄ := by
  unfold Extraction.sha256.soft_compact.compress_u32
  iterate 8 step
  apply spec_bind (compress_u32_loop_spec block a b c d e f g h)
  rintro ⟨a1, b1, c1, d1, e1, f1, g1, h1⟩ hloop
  simp only at hloop
  obtain ⟨ha1, hb1, hc1, hd1, he1, hf1, hg1, hh1⟩ := hloop
  iterate 24 step
  -- The first inner `step` introduces `out✝, out_post✝` (inaccessible —
  -- the let-binder name `i` is shadowed by the outer post-condition's
  -- `out`). Rename to the names the rest of the proof expects.
  rename_i i i_post
  -- Rewrite Impl side via unroll64_eq_foldl, then bridge foldls via
  -- finFoldl_roundStep_eq_tupled.
  simp only [Impl.compress, SHS.Impl.Unroll.unroll64_eq_foldl]
  set init_tup : Vector UInt32 16 × UInt32 × UInt32 × UInt32 × UInt32 ×
      UInt32 × UInt32 × UInt32 × UInt32 :=
    (arrayU32ToVec block,
     toUInt32 a, toUInt32 b, toUInt32 c, toUInt32 d,
     toUInt32 e, toUInt32 f, toUInt32 g, toUInt32 h) with hinit_tup
  have hlen : state.val.length = 8 := state.property
  have hgv : ∀ (k : Nat) (hk : k < 8),
      (arrayU32ToVec state)[k]'(by simp; omega) = toUInt32 (state.val[k]!) := fun k hk => by
    rw [arrayU32ToVec_getElem state k hk (by simp; omega),
        getElem!_pos _ _ (by simp [hlen]; omega)]
  have hinit_match :
      let init_rs : Impl.RoundState :=
        Impl.RoundState.ofState (arrayU32ToVec state) (arrayU32ToVec block)
      (init_rs.schedule, init_rs.a, init_rs.b, init_rs.c, init_rs.d,
       init_rs.e, init_rs.f, init_rs.g, init_rs.h) = init_tup := by
    simp only [Impl.RoundState.ofState]
    have h0 : (arrayU32ToVec state)[0] = toUInt32 a := by rw [hgv 0 (by decide), ← a_post]
    have h1 : (arrayU32ToVec state)[1] = toUInt32 b := by rw [hgv 1 (by decide), ← b_post]
    have h2 : (arrayU32ToVec state)[2] = toUInt32 c := by rw [hgv 2 (by decide), ← c_post]
    have h3 : (arrayU32ToVec state)[3] = toUInt32 d := by rw [hgv 3 (by decide), ← d_post]
    have h4 : (arrayU32ToVec state)[4] = toUInt32 e := by rw [hgv 4 (by decide), ← e_post]
    have h5 : (arrayU32ToVec state)[5] = toUInt32 f := by rw [hgv 5 (by decide), ← f_post]
    have h6 : (arrayU32ToVec state)[6] = toUInt32 g := by rw [hgv 6 (by decide), ← g_post]
    have h7 : (arrayU32ToVec state)[7] = toUInt32 h := by rw [hgv 7 (by decide), ← h_post]
    simp only [hinit_tup, Prod.mk.injEq]
    exact ⟨trivial, h0, h1, h2, h3, h4, h5, h6, h7⟩
  have hbridge := finFoldl_roundStep_eq_tupled
    (Impl.RoundState.ofState (arrayU32ToVec state) (arrayU32ToVec block))
    init_tup hinit_match
  simp only at hbridge; simp only [Prod.ext_iff] at hbridge
  -- Project the 8 components and combine with the loop spec.
  obtain ⟨-, ha, hb, hc, hd, he, hf, hg, hh⟩ := hbridge
  rw [← ha1] at ha; rw [← hb1] at hb; rw [← hc1] at hc; rw [← hd1] at hd
  rw [← he1] at he; rw [← hf1] at hf; rw [← hg1] at hg; rw [← hh1] at hh
  -- `simp only` (rather than `rw`) avoids `maxRecDepth` on the `Fin.foldl 64 …` literal.
  simp only [ha, hb, hc, hd, he, hf, hg, hh]
  have set_get_ne : ∀ {N : Usize} (a : Aeneas.Std.Array U32 N) (j : Usize) (v : U32) (k : ℕ),
      j.val ≠ k → (a.set j v).val[k]! = a.val[k]! := fun _ _ _ k hjk => by
    show (_root_.List.set _ _ _)[k]! = _
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne hjk]
  -- Each `hi(2k)` chases `i_{2k}_post` through the chain of `state_j_post`
  -- rewrites; every off-diagonal lookup collapses via `set_get_ne`, applied
  -- repeatedly to cover all set sites in the chain.
  have hi : i = state.val[0]! := i_post
  have hi2 : i2 = state.val[1]! := by
    rw [i2_post, state1_post]; repeat rw [set_get_ne _ _ _ _ (by decide)]
  have hi4 : i4 = state.val[2]! := by
    rw [i4_post, state2_post, state1_post]
    repeat rw [set_get_ne _ _ _ _ (by decide)]
  have hi6 : i6 = state.val[3]! := by
    rw [i6_post, state3_post, state2_post, state1_post]
    repeat rw [set_get_ne _ _ _ _ (by decide)]
  have hi8 : i8 = state.val[4]! := by
    rw [i8_post, state4_post, state3_post, state2_post, state1_post]
    repeat rw [set_get_ne _ _ _ _ (by decide)]
  have hi10 : i10 = state.val[5]! := by
    rw [i10_post, state5_post, state4_post, state3_post, state2_post, state1_post]
    repeat rw [set_get_ne _ _ _ _ (by decide)]
  have hi12 : i12 = state.val[6]! := by
    rw [i12_post, state6_post, state5_post, state4_post, state3_post, state2_post, state1_post]
    repeat rw [set_get_ne _ _ _ _ (by decide)]
  have hi14 : i14 = state.val[7]! := by
    rw [i14_post, state7_post, state6_post, state5_post, state4_post, state3_post,
        state2_post, state1_post]
    repeat rw [set_get_ne _ _ _ _ (by decide)]
  rw [out_post, state7_post, state6_post, state5_post, state4_post, state3_post,
      state2_post, state1_post, arrayU32ToVec_set8_chain,
      i1_post, i3_post, i5_post, i7_post, i9_post, i11_post, i13_post, i15_post,
      hi, hi2, hi4, hi6, hi8, hi10, hi12, hi14]
  unfold core.num.U32.wrapping_add
  simp only [toUInt32_wrapping_add, ← hgv 0 (by decide), ← hgv 1 (by decide),
             ← hgv 2 (by decide), ← hgv 3 (by decide), ← hgv 4 (by decide),
             ← hgv 5 (by decide), ← hgv 6 (by decide), ← hgv 7 (by decide)]
  rfl

/-! ## Multi-block compression -/

theorem compress256_spec
    (state : Array U32 8#usize) (blocks : Slice (Array U8 64#usize)) :
    Extraction.sha256.compress256 state blocks
    ⦃ out => arrayU32ToVec out =
        blocks.val.foldl
          (fun s (b : Array U8 64#usize) =>
            Impl.compress s (Impl.toU32s (arrayU8ToVec b)))
          (arrayU32ToVec state) ⦄ := by
  unfold Extraction.sha256.compress256 Extraction.sha256.soft_compact.compress
    Extraction.sha256.soft_compact.compress_loop
  simp only [core.slice.Slice.iter, bind_tc_ok,
    Extraction.sha256.soft_compact.compress_loop.body]
  set f : Vector UInt32 8 → Array U8 64#usize → Vector UInt32 8 :=
    fun s b => Impl.compress s (Impl.toU32s (arrayU8ToVec b)) with hf
  set action : Array U8 64#usize → Array U32 8#usize → Result (Array U32 8#usize) :=
    fun b s => do
      let words ← Extraction.sha256.to_u32s b
      Extraction.sha256.soft_compact.compress_u32 s words with haction_def
  have haction_view :
      ∀ (b : Array U8 64#usize) (s : Array U32 8#usize),
        action b s ⦃ s' => arrayU32ToVec s' = f (arrayU32ToVec s) b ⦄ := fun b s => by
    simp only [haction_def]
    apply spec_bind (to_u32s_spec b); intro words hwords
    apply spec_mono (compress_u32_spec s words)
    intro out hout; simp only [hf]; rw [hout, hwords]
  classical
  set f' : Array U32 8#usize → Array U8 64#usize → Array U32 8#usize :=
    fun s b =>
      match action b s with
      | .ok v => v
      | .fail _ => s
      | .div => s with hf'_def
  have hf'_spec :
      ∀ (b : Array U8 64#usize) (s : Array U32 8#usize),
        action b s ⦃ s' => s' = f' s b ⦄ := fun b s => by
    obtain ⟨v, hact, _⟩ := ok_of_spec (haction_view b s)
    simp only [hf'_def, hact, spec_ok]
  have hf'_to_f : ∀ (b : Array U8 64#usize) (s : Array U32 8#usize),
      arrayU32ToVec (f' s b) = f (arrayU32ToVec s) b := fun b s => by
    obtain ⟨v, hact, hpost⟩ := ok_of_spec (haction_view b s)
    simp only [hf'_def, hact]; exact hpost
  have hloop := slice_iter_loop_eq_foldl
    (slice₀ := blocks) (init := state) (f := f')
    (action := action) (haction := hf'_spec)
  have hfold_conv : ∀ (l : List (Array U8 64#usize)) (s : Array U32 8#usize),
      arrayU32ToVec (l.foldl f' s) = l.foldl f (arrayU32ToVec s) := by
    intro l
    induction l with
    | nil => intro s; simp
    | cons b bs ih => intro s; simp only [List.foldl_cons]; rw [ih, hf'_to_f]
  simp only [haction_def, bind_assoc] at hloop
  have hpost : ∀ (p : Array U32 8#usize),
      p = List.foldl f' state blocks.val →
      arrayU32ToVec p = List.foldl f (arrayU32ToVec state) blocks.val :=
    fun p hp => hp ▸ hfold_conv _ _
  refine spec_mono ?_ hpost
  convert hloop using 2
  funext p; fcongr 1; funext discr
  obtain ⟨o, _⟩ := discr; cases o <;> rfl
