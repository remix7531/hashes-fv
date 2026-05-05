import ToU32s

/-!
# Per-round body bridge for `compress_u32`

Owns the per-round body bridge: literal-rotation lemmas
`rotr_bridge_{2,6,…,25}`, the tuple-shaped `tupledRoundStep`, the
single-iteration body equality `compress_u32_body_spec`,
and the 64-fold projection `finFoldl_roundStep_eq_tupled`. Split out of
`Compress.lean` (the body proof is the dominant cost) so that the
orchestration layer there reads top-down without a 230-line digression.
-/



open Aeneas Aeneas.Std Result WP SHS.SHA256

/-! ## Rotation bridges for SHA-256 literal rotations

The Aeneas `UScalar.rotate_right x n#u32` ↔ `Impl.UInt32.rotr` bridge
needs the side-conditions `0 < n.val < 32`, so we cannot make
`toUInt32_rotate_right` a `simp` lemma directly. Instead we materialize
the 10 literal-amount instances actually used by SHA-256
(2, 6, 7, 11, 13, 17, 18, 19, 22, 25) as side-condition-free lemmas.
The main proof of `compress_u32_body_spec` rewrites with
these via `simp only`. -/

private theorem rotr_bridge_2 (x : U32) :
    toUInt32 (UScalar.rotate_right x 2#u32) = Impl.UInt32.rotr (toUInt32 x) 2 :=
  toUInt32_rotate_right x 2#u32 (by decide) (by decide)
private theorem rotr_bridge_6 (x : U32) :
    toUInt32 (UScalar.rotate_right x 6#u32) = Impl.UInt32.rotr (toUInt32 x) 6 :=
  toUInt32_rotate_right x 6#u32 (by decide) (by decide)
private theorem rotr_bridge_7 (x : U32) :
    toUInt32 (UScalar.rotate_right x 7#u32) = Impl.UInt32.rotr (toUInt32 x) 7 :=
  toUInt32_rotate_right x 7#u32 (by decide) (by decide)
private theorem rotr_bridge_11 (x : U32) :
    toUInt32 (UScalar.rotate_right x 11#u32) = Impl.UInt32.rotr (toUInt32 x) 11 :=
  toUInt32_rotate_right x 11#u32 (by decide) (by decide)
private theorem rotr_bridge_13 (x : U32) :
    toUInt32 (UScalar.rotate_right x 13#u32) = Impl.UInt32.rotr (toUInt32 x) 13 :=
  toUInt32_rotate_right x 13#u32 (by decide) (by decide)
private theorem rotr_bridge_17 (x : U32) :
    toUInt32 (UScalar.rotate_right x 17#u32) = Impl.UInt32.rotr (toUInt32 x) 17 :=
  toUInt32_rotate_right x 17#u32 (by decide) (by decide)
private theorem rotr_bridge_18 (x : U32) :
    toUInt32 (UScalar.rotate_right x 18#u32) = Impl.UInt32.rotr (toUInt32 x) 18 :=
  toUInt32_rotate_right x 18#u32 (by decide) (by decide)
private theorem rotr_bridge_19 (x : U32) :
    toUInt32 (UScalar.rotate_right x 19#u32) = Impl.UInt32.rotr (toUInt32 x) 19 :=
  toUInt32_rotate_right x 19#u32 (by decide) (by decide)
private theorem rotr_bridge_22 (x : U32) :
    toUInt32 (UScalar.rotate_right x 22#u32) = Impl.UInt32.rotr (toUInt32 x) 22 :=
  toUInt32_rotate_right x 22#u32 (by decide) (by decide)
private theorem rotr_bridge_25 (x : U32) :
    toUInt32 (UScalar.rotate_right x 25#u32) = Impl.UInt32.rotr (toUInt32 x) 25 :=
  toUInt32_rotate_right x 25#u32 (by decide) (by decide)

/-! ## Per-round body of `compress_u32`

The Aeneas loop body's tuple state is `(iter, block, a, b, c, d, e, f, g, h)`.
The Impl side carries the same data inside `Impl.RoundState` (schedule = block;
working vars a..h). We bridge them via a tuple-shaped reformulation of
`Impl.roundStep`.

`tupledRoundStep i (block, a..h)` ≡ `Impl.roundStep ⟨block, a..h⟩ i` projected
to the Aeneas tuple. -/

/-- Aeneas-tuple form of one Impl round. -/
def tupledRoundStep (i : Fin 64)
    (s : Vector UInt32 16 × UInt32 × UInt32 × UInt32 × UInt32 ×
         UInt32 × UInt32 × UInt32 × UInt32) :
    Vector UInt32 16 × UInt32 × UInt32 × UInt32 × UInt32 ×
    UInt32 × UInt32 × UInt32 × UInt32 :=
  let ⟨block, a, b, c, d, e, f, g, h⟩ := s
  let rs : Impl.RoundState :=
    { schedule := block, a := a, b := b, c := c, d := d
      e := e, f := f, g := g, h := h }
  let rs' := Impl.roundStep rs i
  (rs'.schedule, rs'.a, rs'.b, rs'.c, rs'.d, rs'.e, rs'.f, rs'.g, rs'.h)

/-- One iteration of `compress_u32_loop.body` matches `tupledRoundStep`.

When `iter.start < iter.end = 64`, the body returns `cont` with the
incremented iterator and the per-round-updated working vars; the
working vars in `UInt32`-view equal `tupledRoundStep ⟨iter.start, hi⟩`
applied to the input state. -/
theorem compress_u32_body_spec
    (iter : core.ops.range.Range Usize) (block : Array U32 16#usize)
    (a b c d e f g h : U32)
    (hi : iter.start.val < 64) (hend : iter.«end».val = 64) :
    Extraction.sha256.soft_compact.compress_u32_loop.body iter block a b c d e f g h
    ⦃ r => ∃ (start' : Usize) (block' : Array U32 16#usize)
              (a' b' c' d' e' f' g' h' : U32),
        start'.val = iter.start.val + 1 ∧
        r = .cont ({ start := start', «end» := iter.«end» },
                   block', a', b', c', d', e', f', g', h') ∧
        let s : Vector UInt32 16 × _ :=
          (arrayU32ToVec block,
           toUInt32 a, toUInt32 b, toUInt32 c, toUInt32 d,
           toUInt32 e, toUInt32 f, toUInt32 g, toUInt32 h)
        let s' := tupledRoundStep ⟨iter.start.val, hi⟩ s
        arrayU32ToVec block' = s'.1 ∧
        toUInt32 a' = s'.2.1 ∧ toUInt32 b' = s'.2.2.1 ∧
        toUInt32 c' = s'.2.2.2.1 ∧ toUInt32 d' = s'.2.2.2.2.1 ∧
        toUInt32 e' = s'.2.2.2.2.2.1 ∧ toUInt32 f' = s'.2.2.2.2.2.2.1 ∧
        toUInt32 g' = s'.2.2.2.2.2.2.2.1 ∧ toUInt32 h' = s'.2.2.2.2.2.2.2.2 ⦄ := by
  -- Splits on `iter.start < 16#usize`; the i<16 branch threads 28 `step`s,
  -- the i≥16 branch 54, before unfolding `tupledRoundStep`/`Impl.roundStep`
  -- and rewriting via the U32 bridge `@[simp]` lemmas plus `rotr_bridge_*`
  -- for the 10 literal rotation amounts. A monolithic `step*` at this
  -- position times out, so the proof splits and `step*`s per branch.
  unfold Extraction.sha256.soft_compact.compress_u32_loop.body
  simp only [core.iter.range.IteratorRange.next_Usize_def,
             hend, show iter.start.val < 64 from hi, ↓reduceIte]
  step
  by_cases hlt : iter.start.val < 16
  · -- branch i < 16
    have hlt' : iter.start < 16#usize := hlt
    simp only [hlt', ↓reduceIte]
    step ; step ; step ; step ; step ; step ; step ; step ; step ; step
    step ; step ; step ; step ; step ; step ; step ; step ; step ; step
    step ; step ; step ; step ; step ; step ; step ; step
    refine ⟨r, block, a1, a, b, c, e1, e, f, g, r_post, rfl, ?_⟩
    simp only [tupledRoundStep, SHS.SHA256.Impl.roundStep, hlt, ↓reduceDIte]
    refine ⟨trivial, ?_, trivial, trivial, trivial, ?_, trivial, trivial, trivial⟩
    all_goals {
      simp only [← rotr_bridge_2, ← rotr_bridge_6, ← rotr_bridge_11,
                 ← rotr_bridge_13, ← rotr_bridge_22, ← rotr_bridge_25]
      rw [show core.num.U32.rotate_right = @UScalar.rotate_right .U32 from rfl]
        at i1_post i2_post i4_post i12_post i13_post i15_post
      simp only [show core.num.U32.wrapping_add = UScalar.wrapping_add from rfl]
        at *
      have hw : toUInt32 w =
          (arrayU32ToVec block)[iter.start.val]'hlt := by
        rw [w_post, getElem!_pos _ _ (by simp [block.property]; omega),
            ← arrayU32ToVec_getElem block iter.start.val hlt]
      have hK : toUInt32 i9 = Impl.K32[(⟨iter.start.val, hi⟩ : Fin 64)] := by
        rw [i9_post]; exact K32_eq iter.start.val hi
      refine hw ▸ hK ▸ ?_
      have hi3  : i3  = i1  ^^^ i2  := UScalar.eq_of_val_eq i3_post1
      have hs1  : s1  = i3  ^^^ i4  := UScalar.eq_of_val_eq s1_post1
      have hi5  : i5  = e   &&& f   := UScalar.eq_of_val_eq i5_post1
      have hi7  : i7  = i6  &&& g   := UScalar.eq_of_val_eq i7_post1
      have hch  : ch  = i5  ^^^ i7  := UScalar.eq_of_val_eq ch_post1
      have hi14 : i14 = i12 ^^^ i13 := UScalar.eq_of_val_eq i14_post1
      have hs0  : s0  = i14 ^^^ i15 := UScalar.eq_of_val_eq s0_post1
      have hi16 : i16 = a   &&& b   := UScalar.eq_of_val_eq i16_post1
      have hi17 : i17 = a   &&& c   := UScalar.eq_of_val_eq i17_post1
      have hi18 : i18 = i16 ^^^ i17 := UScalar.eq_of_val_eq i18_post1
      have hi19 : i19 = b   &&& c   := UScalar.eq_of_val_eq i19_post1
      have hmaj : maj = i18 ^^^ i19 := UScalar.eq_of_val_eq maj_post1
      subst hi3 hs1 hi5 hi7 hch hi14 hs0 hi16 hi17 hi18 hi19 hmaj
        i1_post i2_post i4_post i6_post i12_post i13_post i15_post
        i8_post i10_post i11_post t1_post t2_post a1_post e1_post
      simp only [toUInt32_wrapping_add, toUInt32_xor, toUInt32_and,
                 toUInt32_not, rotr_bridge_2, rotr_bridge_6, rotr_bridge_11,
                 rotr_bridge_13, rotr_bridge_22, rotr_bridge_25]
    }
  · -- branch i ≥ 16: schedule extension then same working-var update as above.
    have hlt' : ¬ iter.start < 16#usize := hlt
    simp only [hlt', ↓reduceIte]
    step ; step ; step ; step ; step ; step ; step ; step ; step ; step
    step ; step ; step ; step ; step ; step ; step ; step ; step ; step
    step ; step ; step ; step ; step ; step ; step ; step ; step ; step
    step ; step ; step ; step ; step ; step ; step ; step ; step ; step
    step ; step ; step ; step ; step ; step ; step ; step ; step ; step
    step ; step ; step ; step
    refine ⟨r, a1, a2, a, b, c, e1, e, f, g, r_post, rfl, ?_⟩
    simp only [tupledRoundStep, SHS.SHA256.Impl.roundStep, hlt, ↓reduceDIte]
    refine ⟨?_, ?_, trivial, trivial, trivial, ?_, trivial, trivial, trivial⟩
    · -- Conjunct 1: schedule-write equality.
      have hw15 : toUInt32 w15 =
          (arrayU32ToVec block)[(iter.start.val - 15) % 16]'(by simp; omega) := by
        rw [arrayU32ToVec_getElem block ((iter.start.val - 15) % 16) (by simp; omega)]
        rw [w15_post, getElem!_pos _ _ (by simp [block.property]; omega)]
        congr 2
        rw [i2_post, i1_post1]
      have hw2 : toUInt32 w2 =
          (arrayU32ToVec block)[(iter.start.val - 2) % 16]'(by simp; omega) := by
        rw [arrayU32ToVec_getElem block ((iter.start.val - 2) % 16) (by simp; omega)]
        rw [w2_post, getElem!_pos _ _ (by simp [block.property]; omega)]
        congr 2
        rw [i8_post, i7_post1]
      have hw16 : toUInt32 i15 =
          (arrayU32ToVec block)[(iter.start.val - 16) % 16]'(by simp; omega) := by
        rw [arrayU32ToVec_getElem block ((iter.start.val - 16) % 16) (by simp; omega)]
        rw [i15_post, getElem!_pos _ _ (by simp [block.property]; omega)]
        congr 2
        rw [i14_post, i13_post1]
      have hw7 : toUInt32 i19 =
          (arrayU32ToVec block)[(iter.start.val - 7) % 16]'(by simp; omega) := by
        rw [arrayU32ToVec_getElem block ((iter.start.val - 7) % 16) (by simp; omega)]
        rw [i19_post, getElem!_pos _ _ (by simp [block.property]; omega)]
        congr 2
        rw [i18_post, i17_post1]
      have h_sh3 : toUInt32 i6 = (toUInt32 w15) >>> 3 := by
        simp [toUInt32, i6_post2]
      have h_sh10 : toUInt32 i12 = (toUInt32 w2) >>> 10 := by
        simp [toUInt32, i12_post2]
      have hi3  : i3  = UScalar.rotate_right w15 7#u32 := i3_post
      have hi4  : i4  = UScalar.rotate_right w15 18#u32 := i4_post
      have hi5  : i5  = i3  ^^^ i4  := UScalar.eq_of_val_eq i5_post1
      have hs0  : s0  = i5  ^^^ i6  := UScalar.eq_of_val_eq s0_post1
      have hi9  : i9  = UScalar.rotate_right w2 17#u32 := i9_post
      have hi10 : i10 = UScalar.rotate_right w2 19#u32 := i10_post
      have hi11 : i11 = i9  ^^^ i10 := UScalar.eq_of_val_eq i11_post1
      have hs1  : s1  = i11 ^^^ i12 := UScalar.eq_of_val_eq s1_post1
      subst a1_post
      rw [arrayU32ToVec_set (hi := by simp; omega)]
      congr 1
      subst hi3 hi4 hi5 hs0 hi9 hi10 hi11 hs1
        new_w_post i16_post i20_post
      simp only [show core.num.U32.wrapping_add = UScalar.wrapping_add from rfl,
                 toUInt32_wrapping_add, toUInt32_xor,
                 rotr_bridge_7, rotr_bridge_18, rotr_bridge_17, rotr_bridge_19,
                 h_sh3, h_sh10, hw15, hw2, hw16, hw7]
      rfl
    -- Conjuncts 2 (a2-eq) and 3 (e1-eq): same template as i<16.
    all_goals {
      have hw15 : toUInt32 w15 =
          (arrayU32ToVec block)[(iter.start.val - 15) % 16]'(by simp; omega) := by
        rw [arrayU32ToVec_getElem block ((iter.start.val - 15) % 16) (by simp; omega)]
        rw [w15_post, getElem!_pos _ _ (by simp [block.property]; omega)]
        congr 2; rw [i2_post, i1_post1]
      have hw2 : toUInt32 w2 =
          (arrayU32ToVec block)[(iter.start.val - 2) % 16]'(by simp; omega) := by
        rw [arrayU32ToVec_getElem block ((iter.start.val - 2) % 16) (by simp; omega)]
        rw [w2_post, getElem!_pos _ _ (by simp [block.property]; omega)]
        congr 2; rw [i8_post, i7_post1]
      have hw16 : toUInt32 i15 =
          (arrayU32ToVec block)[(iter.start.val - 16) % 16]'(by simp; omega) := by
        rw [arrayU32ToVec_getElem block ((iter.start.val - 16) % 16) (by simp; omega)]
        rw [i15_post, getElem!_pos _ _ (by simp [block.property]; omega)]
        congr 2; rw [i14_post, i13_post1]
      have hw7 : toUInt32 i19 =
          (arrayU32ToVec block)[(iter.start.val - 7) % 16]'(by simp; omega) := by
        rw [arrayU32ToVec_getElem block ((iter.start.val - 7) % 16) (by simp; omega)]
        rw [i19_post, getElem!_pos _ _ (by simp [block.property]; omega)]
        congr 2; rw [i18_post, i17_post1]
      have hK : toUInt32 i30 = Impl.K32[(⟨iter.start.val, hi⟩ : Fin 64)] := by
        rw [i30_post]; exact K32_eq iter.start.val hi
      have h_sh3 : toUInt32 i6 = (toUInt32 w15) >>> 3 := by
        simp [toUInt32, i6_post2]
      have h_sh10 : toUInt32 i12 = (toUInt32 w2) >>> 10 := by
        simp [toUInt32, i12_post2]
      refine hw15 ▸ hw2 ▸ hw16 ▸ hw7 ▸ hK ▸ ?_
      have hi3  : i3  = UScalar.rotate_right w15 7#u32 := i3_post
      have hi4  : i4  = UScalar.rotate_right w15 18#u32 := i4_post
      have hi5  : i5  = i3  ^^^ i4  := UScalar.eq_of_val_eq i5_post1
      have hs0  : s0  = i5  ^^^ i6  := UScalar.eq_of_val_eq s0_post1
      have hi9  : i9  = UScalar.rotate_right w2 17#u32 := i9_post
      have hi10 : i10 = UScalar.rotate_right w2 19#u32 := i10_post
      have hi11 : i11 = i9  ^^^ i10 := UScalar.eq_of_val_eq i11_post1
      have hs1  : s1  = i11 ^^^ i12 := UScalar.eq_of_val_eq s1_post1
      have hi22 : i22 = UScalar.rotate_right e 6#u32 := i22_post
      have hi23 : i23 = UScalar.rotate_right e 11#u32 := i23_post
      have hi24 : i24 = i22 ^^^ i23 := UScalar.eq_of_val_eq i24_post1
      have hi25 : i25 = UScalar.rotate_right e 25#u32 := i25_post
      have hs11 : s11 = i24 ^^^ i25 := UScalar.eq_of_val_eq s11_post1
      have hi26 : i26 = e   &&& f   := UScalar.eq_of_val_eq i26_post1
      have hi28 : i28 = i27 &&& g   := UScalar.eq_of_val_eq i28_post1
      have hch  : ch  = i26 ^^^ i28 := UScalar.eq_of_val_eq ch_post1
      have hi33 : i33 = UScalar.rotate_right a 2#u32 := i33_post
      have hi34 : i34 = UScalar.rotate_right a 13#u32 := i34_post
      have hi35 : i35 = i33 ^^^ i34 := UScalar.eq_of_val_eq i35_post1
      have hi36 : i36 = UScalar.rotate_right a 22#u32 := i36_post
      have hs01 : s01 = i35 ^^^ i36 := UScalar.eq_of_val_eq s01_post1
      have hi37 : i37 = a   &&& b   := UScalar.eq_of_val_eq i37_post1
      have hi38 : i38 = a   &&& c   := UScalar.eq_of_val_eq i38_post1
      have hi39 : i39 = i37 ^^^ i38 := UScalar.eq_of_val_eq i39_post1
      have hi40 : i40 = b   &&& c   := UScalar.eq_of_val_eq i40_post1
      have hmaj : maj = i39 ^^^ i40 := UScalar.eq_of_val_eq maj_post1
      subst hi3 hi4 hi5 hs0 hi9 hi10 hi11 hs1
        hi22 hi23 hi24 hi25 hs11 hi26 hi28 hch hi33 hi34 hi35 hi36 hs01
        hi37 hi38 hi39 hi40 hmaj
        new_w_post i16_post i20_post i27_post i29_post i31_post i32_post
        t1_post t2_post a2_post e1_post
      simp only [show core.num.U32.wrapping_add = UScalar.wrapping_add from rfl,
                 toUInt32_wrapping_add, toUInt32_xor, toUInt32_and, toUInt32_not,
                 rotr_bridge_2, rotr_bridge_6, rotr_bridge_7, rotr_bridge_11,
                 rotr_bridge_13, rotr_bridge_17, rotr_bridge_18, rotr_bridge_19,
                 rotr_bridge_22, rotr_bridge_25, h_sh3, h_sh10]
    }

/-! ## Tupled-state foldl bridge -/

/-- `Fin.foldl 64 Impl.roundStep` over a `RoundState` projected to the
9-tuple shape (schedule + 8 working vars) equals
`Fin.foldl 64 tupledRoundStep` over the corresponding tuple. -/
theorem finFoldl_roundStep_eq_tupled
    (init_rs : Impl.RoundState)
    (init_tup : Vector UInt32 16 × UInt32 × UInt32 × UInt32 × UInt32 ×
        UInt32 × UInt32 × UInt32 × UInt32)
    (h0 : (init_rs.schedule, init_rs.a, init_rs.b, init_rs.c, init_rs.d,
           init_rs.e, init_rs.f, init_rs.g, init_rs.h) = init_tup) :
    let final_rs := Fin.foldl 64 Impl.roundStep init_rs
    let final_tup := Fin.foldl 64 (fun s i => tupledRoundStep i s) init_tup
    (final_rs.schedule, final_rs.a, final_rs.b, final_rs.c, final_rs.d,
     final_rs.e, final_rs.f, final_rs.g, final_rs.h) = final_tup := by
  set proj : Impl.RoundState → Vector UInt32 16 × UInt32 × UInt32 × UInt32 × UInt32 ×
      UInt32 × UInt32 × UInt32 × UInt32 :=
    fun rs => (rs.schedule, rs.a, rs.b, rs.c, rs.d, rs.e, rs.f, rs.g, rs.h)
  have hfold_eq :
    ∀ (n : Nat) (_ : n ≤ 64),
      proj (partialFinFoldl 64 (fun s i => Impl.roundStep s i) n init_rs) =
      partialFinFoldl 64
        (fun (s : Vector UInt32 16 × UInt32 × UInt32 × UInt32 × UInt32 ×
                UInt32 × UInt32 × UInt32 × UInt32) (i : Fin 64) =>
          tupledRoundStep i s) n init_tup := by
    intro n hn
    induction n with
    | zero =>
      simp only [partialFinFoldl_zero]
      exact h0
    | succ k ih =>
      have hk : k < 64 := hn
      have hk' : k ≤ 64 := Nat.le_of_lt hk
      have ih' := ih hk'
      rw [partialFinFoldl_succ 64 _ k hk,
          partialFinFoldl_succ 64 _ k hk]
      rw [← ih']
      simp only [tupledRoundStep, proj]
  have hbridge := hfold_eq 64 (le_refl _)
  rw [partialFinFoldl_full,
      partialFinFoldl_full] at hbridge
  exact hbridge


