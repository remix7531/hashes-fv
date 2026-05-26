import Word.U64
import Word.ToU64s
import equiv.SHA512.Compress.Impl

/-!
# Per-round body bridges for `compress_u64`

64-bit analogue of `Sha256/RoundStep.lean`.  Unlike SHA-256 — where one
fused loop performs both schedule extension (when `i<16`) and round
update — SHA-512 uses two separate Aeneas loops (`compress_u64_loop0`
for the schedule, `compress_u64_loop1` for the rounds).  We bridge
each individually, against `extScheduleStep` (the `t≥16` branch of
`SHS.Equiv.SHA512.Compress.Impl.implScheduleStep`) and
`tupledRoundStep64` (an Aeneas-tuple reshape of
`SHS.Equiv.SHA512.Compress.Impl.implRoundStep`), and provide
projection bridges between `Fin.foldl` over the tupled form and
the Impl-side `Fin.foldl`. -/

open Aeneas Aeneas.Std Result WP SHS.SHA512

/-! ## Rotation bridges for SHA-512 literal rotations

The Aeneas `UScalar.rotate_right x n#u32` ↔ `Impl.UInt64.rotr` bridge
needs side-conditions `0 < n.val < 64`, so we cannot make
`toUInt64_rotate_right` a `simp` lemma directly.  We materialize the
ten literal-amount instances actually used by SHA-512
(1, 8, 14, 18, 19, 28, 34, 39, 41, 61) as side-condition-free lemmas. -/

private theorem rotr64_bridge_1 (x : U64) :
    toUInt64 (UScalar.rotate_right x 1#u32) =
      SHS.SHA512.Impl.UInt64.rotr (toUInt64 x) 1 :=
  toUInt64_rotate_right x 1#u32 (by decide) (by decide)
private theorem rotr64_bridge_8 (x : U64) :
    toUInt64 (UScalar.rotate_right x 8#u32) =
      SHS.SHA512.Impl.UInt64.rotr (toUInt64 x) 8 :=
  toUInt64_rotate_right x 8#u32 (by decide) (by decide)
private theorem rotr64_bridge_14 (x : U64) :
    toUInt64 (UScalar.rotate_right x 14#u32) =
      SHS.SHA512.Impl.UInt64.rotr (toUInt64 x) 14 :=
  toUInt64_rotate_right x 14#u32 (by decide) (by decide)
private theorem rotr64_bridge_18 (x : U64) :
    toUInt64 (UScalar.rotate_right x 18#u32) =
      SHS.SHA512.Impl.UInt64.rotr (toUInt64 x) 18 :=
  toUInt64_rotate_right x 18#u32 (by decide) (by decide)
private theorem rotr64_bridge_19 (x : U64) :
    toUInt64 (UScalar.rotate_right x 19#u32) =
      SHS.SHA512.Impl.UInt64.rotr (toUInt64 x) 19 :=
  toUInt64_rotate_right x 19#u32 (by decide) (by decide)
private theorem rotr64_bridge_28 (x : U64) :
    toUInt64 (UScalar.rotate_right x 28#u32) =
      SHS.SHA512.Impl.UInt64.rotr (toUInt64 x) 28 :=
  toUInt64_rotate_right x 28#u32 (by decide) (by decide)
private theorem rotr64_bridge_34 (x : U64) :
    toUInt64 (UScalar.rotate_right x 34#u32) =
      SHS.SHA512.Impl.UInt64.rotr (toUInt64 x) 34 :=
  toUInt64_rotate_right x 34#u32 (by decide) (by decide)
private theorem rotr64_bridge_39 (x : U64) :
    toUInt64 (UScalar.rotate_right x 39#u32) =
      SHS.SHA512.Impl.UInt64.rotr (toUInt64 x) 39 :=
  toUInt64_rotate_right x 39#u32 (by decide) (by decide)
private theorem rotr64_bridge_41 (x : U64) :
    toUInt64 (UScalar.rotate_right x 41#u32) =
      SHS.SHA512.Impl.UInt64.rotr (toUInt64 x) 41 :=
  toUInt64_rotate_right x 41#u32 (by decide) (by decide)
private theorem rotr64_bridge_61 (x : U64) :
    toUInt64 (UScalar.rotate_right x 61#u32) =
      SHS.SHA512.Impl.UInt64.rotr (toUInt64 x) 61 :=
  toUInt64_rotate_right x 61#u32 (by decide) (by decide)

/-- `Vector.set` (bounds-proof form) coincides with `Vector.set!` when the
index is in range. -/
private theorem vector_set_eq_set!
    {α : Type _} {n : Nat} (v : Vector α n) (i : Nat) (x : α) (h : i < n) :
    v.set i x h = v.set! i x := by
  apply Vector.toArray_inj.mp
  simp [Array.setIfInBounds, h]

/-- `getElem!` agrees with `getElem` on Vectors when the index is in range. -/
private theorem vector_getElem!_eq_getElem
    {α : Type _} [Inhabited α] {n : Nat} (v : Vector α n) (i : Nat) (h : i < n) :
    v[i]! = v[i]'h := by
  simp [getElem!_pos, h]

/-! ## Schedule extension step (the `t ≥ 16` branch)

`loop0` only iterates `t ∈ [16, 80)`, so we factor the `t ≥ 16` branch
of `implScheduleStep` into a standalone `extScheduleStep` that does
not depend on the (unused) block argument.  In `Sha512/Compress.lean`
we will simp this back to `implScheduleStep block t w` under the
hypothesis `¬ t < 16`. -/

def extScheduleStep (t : Nat) (w : SHS.SHA512.Impl.Schedule) :
    SHS.SHA512.Impl.Schedule :=
  let w15 := w[t - 15]!
  let s0  := (SHS.SHA512.Impl.UInt64.rotr w15 1)
              ^^^ (SHS.SHA512.Impl.UInt64.rotr w15 8) ^^^ (w15 >>> 7)
  let w2  := w[t - 2]!
  let s1  := (SHS.SHA512.Impl.UInt64.rotr w2 19)
              ^^^ (SHS.SHA512.Impl.UInt64.rotr w2 61) ^^^ (w2 >>> 6)
  w.set! t (w[t - 16]! + s0 + w[t - 7]! + s1)

/-- For `t ∈ [16, 80)`, `extScheduleStep` matches the Impl-side
`implScheduleStep` regardless of the (unused) block argument. -/
theorem implScheduleStep_eq_extScheduleStep
    (block : SHS.SHA512.Impl.Block) (t : Nat) (ht : 16 ≤ t)
    (w : SHS.SHA512.Impl.Schedule) :
    SHS.Equiv.SHA512.Compress.Impl.implScheduleStep block t w =
      extScheduleStep t w := by
  unfold SHS.Equiv.SHA512.Compress.Impl.implScheduleStep extScheduleStep
  simp [Nat.not_lt.mpr ht]

/-! ## Round step (Aeneas-tuple reshape of `implRoundStep`)

`tupledRoundStep64` delegates to upstream's `implRoundStep` (a named
function), then projects the resulting `Vector UInt64 8` back to the
8-tuple shape Aeneas uses.  The body proof bridge
`compress_u64_loop1_body_spec` unfolds `tupledRoundStep64 ∘
implRoundStep` together via a single `simp only` set, mirroring the
SHA-256 `tupledRoundStep ∘ Impl.roundStep` unfold path. -/

/-- Aeneas-tuple form of one Impl round.  The Aeneas state tuple is
`(a, b, c, d, e, f, g, h)`. -/
def tupledRoundStep64 (w : SHS.SHA512.Impl.Schedule) (t : Nat)
    (s : UInt64 × UInt64 × UInt64 × UInt64 ×
         UInt64 × UInt64 × UInt64 × UInt64) :
    UInt64 × UInt64 × UInt64 × UInt64 ×
    UInt64 × UInt64 × UInt64 × UInt64 :=
  let ⟨a, b, c, d, e, f, g, h⟩ := s
  let s' := SHS.Equiv.SHA512.Compress.Impl.implRoundStep w t
              #v[a, b, c, d, e, f, g, h]
  (s'[0], s'[1], s'[2], s'[3], s'[4], s'[5], s'[6], s'[7])

/-- `implRoundStep w t s` projected to its 8-tuple equals
`tupledRoundStep64 w t` applied to the projection of `s`. -/
theorem proj_implRoundStep_eq_tupled
    (w : SHS.SHA512.Impl.Schedule) (t : Nat) (s : SHS.SHA512.Impl.State) :
    let s' := SHS.Equiv.SHA512.Compress.Impl.implRoundStep w t s
    (s'[0], s'[1], s'[2], s'[3], s'[4], s'[5], s'[6], s'[7]) =
      tupledRoundStep64 w t (s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]) := by
  rfl

/-! ## One iteration of `compress_u64_loop0.body`

When `iter.start ∈ [16, iter.end)` and `iter.end = 80`, the body returns
`cont` with the incremented iterator and the schedule with slot
`iter.start` overwritten by the four-term sum.  Its UInt64-view equals
`extScheduleStep iter.start.val` applied to the input schedule. -/
set_option maxHeartbeats 1000000 in
theorem compress_u64_loop0_body_spec
    (iter : core.ops.range.Range Usize) (w : Array U64 80#usize)
    (hlo : 16 ≤ iter.start.val) (hhi : iter.start.val < 80)
    (hend : iter.«end».val = 80) :
    Extraction.sha512.soft_compact.compress_u64_loop0.body iter w
    ⦃ r => ∃ (start' : Usize) (w' : Array U64 80#usize),
        start'.val = iter.start.val + 1 ∧
        r = .cont ({ start := start', «end» := iter.«end» }, w') ∧
        arrayU64ToVec w' =
          extScheduleStep iter.start.val (arrayU64ToVec w) ⦄ := by
  unfold Extraction.sha512.soft_compact.compress_u64_loop0.body
  simp only [core.iter.range.IteratorRange.next_Usize_def,
             hend, show iter.start.val < 80 from hhi, ↓reduceIte]
  step
  step ; step ; step ; step ; step ; step ; step ; step ; step ; step
  step ; step ; step ; step ; step ; step ; step ; step ; step ; step
  step ; step
  refine ⟨r, a, r_post, rfl, ?_⟩
  simp only [extScheduleStep]
  have hw15 : toUInt64 w15 =
      (arrayU64ToVec w)[iter.start.val - 15]'(by simp; scalar_tac) := by
    rw [arrayU64ToVec_getElem w (iter.start.val - 15) (by scalar_tac)]
    rw [w15_post, getElem!_pos _ _ (by simp [w.property]; scalar_tac)]
    congr 2
  have hw2 : toUInt64 w2 =
      (arrayU64ToVec w)[iter.start.val - 2]'(by simp; scalar_tac) := by
    rw [arrayU64ToVec_getElem w (iter.start.val - 2) (by scalar_tac)]
    rw [w2_post, getElem!_pos _ _ (by simp [w.property]; scalar_tac)]
    congr 2
  have hw16 : toUInt64 i12 =
      (arrayU64ToVec w)[iter.start.val - 16]'(by simp; scalar_tac) := by
    rw [arrayU64ToVec_getElem w (iter.start.val - 16) (by scalar_tac)]
    rw [i12_post, getElem!_pos _ _ (by simp [w.property]; scalar_tac)]
    congr 2
  have hw7 : toUInt64 i15 =
      (arrayU64ToVec w)[iter.start.val - 7]'(by simp; scalar_tac) := by
    rw [arrayU64ToVec_getElem w (iter.start.val - 7) (by scalar_tac)]
    rw [i15_post, getElem!_pos _ _ (by simp [w.property]; scalar_tac)]
    congr 2
  have h_sh7 : toUInt64 i5 = (toUInt64 w15) >>> 7 := by
    simp [toUInt64, i5_post2]
  have h_sh6 : toUInt64 i10 = (toUInt64 w2) >>> 6 := by
    simp [toUInt64, i10_post2]
  have hi2 : i2 = UScalar.rotate_right w15 1#u32 := i2_post
  have hi3 : i3 = UScalar.rotate_right w15 8#u32 := i3_post
  have hi4 : i4 = i2 ^^^ i3 := UScalar.eq_of_val_eq i4_post1
  have hs0 : s0 = i4 ^^^ i5 := UScalar.eq_of_val_eq s0_post1
  have hi7 : i7 = UScalar.rotate_right w2 19#u32 := i7_post
  have hi8 : i8 = UScalar.rotate_right w2 61#u32 := i8_post
  have hi9 : i9 = i7 ^^^ i8 := UScalar.eq_of_val_eq i9_post1
  have hs1 : s1 = i9 ^^^ i10 := UScalar.eq_of_val_eq s1_post1
  subst a_post
  have hbnd : iter.start.val < (arrayU64ToVec w).size := by simp; scalar_tac
  -- Convert `hw*` from `[i]` to `[i]!` form to match the RHS shape.
  rw [← vector_getElem!_eq_getElem (arrayU64ToVec w) (iter.start.val - 15)
        (by simp; scalar_tac)] at hw15
  rw [← vector_getElem!_eq_getElem (arrayU64ToVec w) (iter.start.val - 2)
        (by simp; scalar_tac)] at hw2
  rw [← vector_getElem!_eq_getElem (arrayU64ToVec w) (iter.start.val - 16)
        (by simp; scalar_tac)] at hw16
  rw [← vector_getElem!_eq_getElem (arrayU64ToVec w) (iter.start.val - 7)
        (by simp; scalar_tac)] at hw7
  rw [arrayU64ToVec_set (hi := hbnd), vector_set_eq_set! _ _ _ hbnd]
  subst hi2 hi3 hi4 hs0 hi7 hi8 hi9 hs1
    i13_post i16_post i17_post
  simp only [show core.num.U64.wrapping_add = UScalar.wrapping_add from rfl,
             toUInt64_wrapping_add, toUInt64_xor,
             rotr64_bridge_1, rotr64_bridge_8,
             rotr64_bridge_19, rotr64_bridge_61,
             h_sh7, h_sh6, hw15, hw2, hw16, hw7]
  rfl

/-! ## One iteration of `compress_u64_loop1.body` -/

/-- The two non-trivial outputs of `implRoundStep` (indices 0 and 4) expressed
as explicit formulas, with `(implRoundStep ...)[k]` reducing to them by `rfl`.
Used by `compress_u64_loop1_body_spec` to bypass simp-based unfolding of
`implRoundStep`'s body during proof-term construction. -/
private theorem implRoundStep_get_0 (w : SHS.SHA512.Impl.Schedule) (t : Nat)
    (a' b' c' d' e' f' g' h' : UInt64) :
    (SHS.Equiv.SHA512.Compress.Impl.implRoundStep w t
        #v[a', b', c', d', e', f', g', h'])[0] =
      (SHS.SHA512.Impl.UInt64.rotr e' 14 ^^^ SHS.SHA512.Impl.UInt64.rotr e' 18
        ^^^ SHS.SHA512.Impl.UInt64.rotr e' 41) +
      ((e' &&& f') ^^^ ((~~~ e') &&& g')) +
      SHS.SHA512.Impl.K64[t]! + w[t]! + h' +
      ((SHS.SHA512.Impl.UInt64.rotr a' 28 ^^^ SHS.SHA512.Impl.UInt64.rotr a' 34
        ^^^ SHS.SHA512.Impl.UInt64.rotr a' 39) +
       ((a' &&& b') ^^^ (a' &&& c') ^^^ (b' &&& c'))) :=
  rfl

private theorem implRoundStep_get_4 (w : SHS.SHA512.Impl.Schedule) (t : Nat)
    (a' b' c' d' e' f' g' h' : UInt64) :
    (SHS.Equiv.SHA512.Compress.Impl.implRoundStep w t
        #v[a', b', c', d', e', f', g', h'])[4] =
      d' +
      ((SHS.SHA512.Impl.UInt64.rotr e' 14 ^^^ SHS.SHA512.Impl.UInt64.rotr e' 18
        ^^^ SHS.SHA512.Impl.UInt64.rotr e' 41) +
       ((e' &&& f') ^^^ ((~~~ e') &&& g')) +
       SHS.SHA512.Impl.K64[t]! + w[t]! + h') :=
  rfl

private theorem implRoundStep_get_1 (w : SHS.SHA512.Impl.Schedule) (t : Nat)
    (a' b' c' d' e' f' g' h' : UInt64) :
    (SHS.Equiv.SHA512.Compress.Impl.implRoundStep w t
        #v[a', b', c', d', e', f', g', h'])[1] = a' := rfl

private theorem implRoundStep_get_2 (w : SHS.SHA512.Impl.Schedule) (t : Nat)
    (a' b' c' d' e' f' g' h' : UInt64) :
    (SHS.Equiv.SHA512.Compress.Impl.implRoundStep w t
        #v[a', b', c', d', e', f', g', h'])[2] = b' := rfl

private theorem implRoundStep_get_3 (w : SHS.SHA512.Impl.Schedule) (t : Nat)
    (a' b' c' d' e' f' g' h' : UInt64) :
    (SHS.Equiv.SHA512.Compress.Impl.implRoundStep w t
        #v[a', b', c', d', e', f', g', h'])[3] = c' := rfl

private theorem implRoundStep_get_5 (w : SHS.SHA512.Impl.Schedule) (t : Nat)
    (a' b' c' d' e' f' g' h' : UInt64) :
    (SHS.Equiv.SHA512.Compress.Impl.implRoundStep w t
        #v[a', b', c', d', e', f', g', h'])[5] = e' := rfl

private theorem implRoundStep_get_6 (w : SHS.SHA512.Impl.Schedule) (t : Nat)
    (a' b' c' d' e' f' g' h' : UInt64) :
    (SHS.Equiv.SHA512.Compress.Impl.implRoundStep w t
        #v[a', b', c', d', e', f', g', h'])[6] = f' := rfl

private theorem implRoundStep_get_7 (w : SHS.SHA512.Impl.Schedule) (t : Nat)
    (a' b' c' d' e' f' g' h' : UInt64) :
    (SHS.Equiv.SHA512.Compress.Impl.implRoundStep w t
        #v[a', b', c', d', e', f', g', h'])[7] = g' := rfl

set_option maxHeartbeats 1000000 in
theorem compress_u64_loop1_body_spec
    (w : Array U64 80#usize) (iter : core.ops.range.Range Usize)
    (a b c d e f g h : U64)
    (hhi : iter.start.val < 80) (hend : iter.«end».val = 80) :
    Extraction.sha512.soft_compact.compress_u64_loop1.body w iter a b c d e f g h
    ⦃ r => ∃ (start' : Usize) (a' b' c' d' e' f' g' h' : U64),
        start'.val = iter.start.val + 1 ∧
        r = .cont ({ start := start', «end» := iter.«end» },
                   a', b', c', d', e', f', g', h') ∧
        let s : UInt64 × _ :=
          (toUInt64 a, toUInt64 b, toUInt64 c, toUInt64 d,
           toUInt64 e, toUInt64 f, toUInt64 g, toUInt64 h)
        let s' := tupledRoundStep64 (arrayU64ToVec w) iter.start.val s
        toUInt64 a' = s'.1 ∧ toUInt64 b' = s'.2.1 ∧
        toUInt64 c' = s'.2.2.1 ∧ toUInt64 d' = s'.2.2.2.1 ∧
        toUInt64 e' = s'.2.2.2.2.1 ∧ toUInt64 f' = s'.2.2.2.2.2.1 ∧
        toUInt64 g' = s'.2.2.2.2.2.2.1 ∧ toUInt64 h' = s'.2.2.2.2.2.2.2 ⦄ := by
  unfold Extraction.sha512.soft_compact.compress_u64_loop1.body
  /- Reduce the 28-bind chain of pure `lift` operations to a single `ok` with
     the substituted U64-tree, leaving only 3 effectful binds (the iterator
     successor + 2 `Array.index_usize` calls).  This is the key step that
     keeps the kernel happy: with the 28 `let i_k ← ok (...)` collapsed, the
     proof term carries only a small bind chain. -/
  simp only [core.iter.range.IteratorRange.next_Usize_def,
             hend, show iter.start.val < 80 from hhi, ↓reduceIte,
             Aeneas.Std.lift, bind_tc_ok]
  step
  step
  step
  refine ⟨r, _, a, b, c, _, e, f, g, r_post, rfl, ?_⟩
  /- 8 conjuncts.  Six are register copies (close by `rfl` after unfolding
     `tupledRoundStep64`); two non-trivial (a' and e') use the bridges. -/
  have hK : toUInt64 i9 = SHS.SHA512.Impl.K64[iter.start.val]! := by
    rw [vector_getElem!_eq_getElem _ _ (by simpa using hhi)]
    rw [i9_post]; exact K64_eq iter.start.val hhi
  have hw : toUInt64 i11 = (arrayU64ToVec w)[iter.start.val]! := by
    rw [vector_getElem!_eq_getElem _ _ (by simpa using hhi)]
    rw [arrayU64ToVec_getElem w iter.start.val hhi, i11_post,
        getElem!_pos _ _ (by simp [w.property]; scalar_tac)]
  simp only [tupledRoundStep64,
             implRoundStep_get_0, implRoundStep_get_1, implRoundStep_get_2,
             implRoundStep_get_3, implRoundStep_get_4, implRoundStep_get_5,
             implRoundStep_get_6, implRoundStep_get_7]
  refine ⟨?_, trivial, trivial, trivial, ?_, trivial, trivial, trivial⟩
  · /- a' conjunct -/
    simp only [show core.num.U64.wrapping_add = UScalar.wrapping_add from rfl,
               show core.num.U64.rotate_right = @UScalar.rotate_right .U64 from rfl,
               toUInt64_wrapping_add, toUInt64_xor, toUInt64_and, toUInt64_not,
               rotr64_bridge_14, rotr64_bridge_18, rotr64_bridge_28,
               rotr64_bridge_34, rotr64_bridge_39, rotr64_bridge_41,
               hK, hw]
    rfl
  · /- e' conjunct -/
    simp only [show core.num.U64.wrapping_add = UScalar.wrapping_add from rfl,
               show core.num.U64.rotate_right = @UScalar.rotate_right .U64 from rfl,
               toUInt64_wrapping_add, toUInt64_xor, toUInt64_and, toUInt64_not,
               rotr64_bridge_14, rotr64_bridge_18, rotr64_bridge_41,
               hK, hw]
    rfl

/-! ## Tupled foldl bridges -/

/-- Projection bridge for the round-step fold: `Fin.foldl 80 implRoundStep`
over an `Impl.State` projected to the 8-tuple equals
`Fin.foldl 80 tupledRoundStep64` over the corresponding tuple. -/
theorem finFoldl_roundStep64_eq_tupled
    (w : SHS.SHA512.Impl.Schedule)
    (init_st : SHS.SHA512.Impl.State)
    (init_tup : UInt64 × UInt64 × UInt64 × UInt64 ×
                UInt64 × UInt64 × UInt64 × UInt64)
    (h0 : (init_st[0], init_st[1], init_st[2], init_st[3],
           init_st[4], init_st[5], init_st[6], init_st[7]) = init_tup) :
    let final_st := Fin.foldl 80
      (fun s (i : Fin 80) => SHS.Equiv.SHA512.Compress.Impl.implRoundStep w i.val s)
      init_st
    let final_tup := Fin.foldl 80
      (fun s (i : Fin 80) => tupledRoundStep64 w i.val s) init_tup
    (final_st[0], final_st[1], final_st[2], final_st[3],
     final_st[4], final_st[5], final_st[6], final_st[7]) = final_tup := by
  set proj : SHS.SHA512.Impl.State →
      UInt64 × UInt64 × UInt64 × UInt64 ×
      UInt64 × UInt64 × UInt64 × UInt64 :=
    fun s => (s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7])
  have hfold_eq :
    ∀ (n : Nat) (_ : n ≤ 80),
      proj (partialFinFoldl 80
        (fun s (i : Fin 80) =>
          SHS.Equiv.SHA512.Compress.Impl.implRoundStep w i.val s) n init_st) =
      partialFinFoldl 80
        (fun (s : UInt64 × UInt64 × UInt64 × UInt64 ×
                  UInt64 × UInt64 × UInt64 × UInt64) (i : Fin 80) =>
          tupledRoundStep64 w i.val s) n init_tup := by
    intro n hn
    induction n with
    | zero =>
      simp only [partialFinFoldl_zero]
      exact h0
    | succ k ih =>
      have hk : k < 80 := hn
      have hk' : k ≤ 80 := Nat.le_of_lt hk
      have ih' := ih hk'
      rw [partialFinFoldl_succ 80 _ k hk,
          partialFinFoldl_succ 80 _ k hk]
      rw [← ih']
      exact proj_implRoundStep_eq_tupled w k _
  have hbridge := hfold_eq 80 (le_refl _)
  rw [partialFinFoldl_full, partialFinFoldl_full] at hbridge
  exact hbridge

/-- `Fin.foldl 80 implScheduleStep` over a schedule equals the same
fold of `extScheduleStep` once we restrict to indices ≥ 16.  Stated
here only at the full-fold level, which is what `Compress.lean` needs
after we have already bridged the `[0, 16)` copy phase separately. -/
theorem finFoldl_extScheduleStep_eq_implScheduleStep
    (block : SHS.SHA512.Impl.Block) (init : SHS.SHA512.Impl.Schedule)
    (n : Nat) (hn : n ≤ 80 - 16) :
    Fin.foldl n
      (fun w (i : Fin n) => extScheduleStep (16 + i.val) w) init =
    Fin.foldl n
      (fun w (i : Fin n) =>
        SHS.Equiv.SHA512.Compress.Impl.implScheduleStep block (16 + i.val) w) init := by
  -- Pointwise congruence of `Fin.foldl` over the same length, proved by
  -- induction on `n` using `partialFinFoldl`.
  have key : ∀ (k : Nat) (hk : k ≤ n),
      partialFinFoldl n
        (fun w (i : Fin n) => extScheduleStep (16 + i.val) w) k init =
      partialFinFoldl n
        (fun w (i : Fin n) =>
          SHS.Equiv.SHA512.Compress.Impl.implScheduleStep block (16 + i.val) w) k init := by
    intro k hk
    induction k with
    | zero => simp [partialFinFoldl_zero]
    | succ j ih =>
      have hj : j < n := hk
      have hj' : j ≤ n := Nat.le_of_lt hj
      rw [partialFinFoldl_succ n _ j hj, partialFinFoldl_succ n _ j hj, ih hj']
      have hbound : 16 + j < 80 := by omega
      have heq := implScheduleStep_eq_extScheduleStep block (16 + j) (by omega)
        (partialFinFoldl n
          (fun w (i : Fin n) =>
            SHS.Equiv.SHA512.Compress.Impl.implScheduleStep block (16 + i.val) w) j init)
      exact heq.symm
  have := key n (le_refl _)
  rw [partialFinFoldl_full, partialFinFoldl_full] at this
  exact this
