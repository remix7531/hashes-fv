import Word.U64
import Sha512.FinalBlock
import Aeneas

/-!
# Refinement of `sha512_inner_loop1` against the spec's BE-emit step

The Aeneas extraction's final loop walks `state : Array U64 8` and emits
big-endian bytes into `out : Array U8 64`.  The FIPS-spec final step is
a single `Vector.ofFn (Fin 64 → UInt8)` doing the same thing.
64-bit analogue of `Sha256/Loop1.lean`; the byte cascade is 8 wide
instead of 4.
-/

open Aeneas Aeneas.Std Result WP SHS.SHA512

/-- Consumer-facing form of `toUInt8_be_byte`: indexing
`to_be_bytes x` directly. -/
private theorem toUInt8_to_be_bytes_get (x : U64) (k : Nat) (hk : k < 8) :
    toUInt8 ((core.num.U64.to_be_bytes x).val[k]!) =
      ((toUInt64 x >>> (UInt64.ofNat ((7 - k) * 8))) &&& 0xff).toUInt8 := by
  show toUInt8 ((x.bv.toBEBytes.map (UScalar.mk (ty := .U8)) : List U8)[k]!) = _
  exact toUInt8_be_byte x k hk

/-! ## Loop-level spec via `loop.spec_decr_nat`

The invariant tracks the partial fill: for every byte slot `j < 64`, the
output's `j`-th byte equals the spec byte if its word-index `j / 8` has
already been processed (`j / 8 < iter.start.val`), else the original
input byte. -/

private def specByte (state : Array U64 8#usize) (out0 : Array U8 64#usize)
    (k : Nat) (j : Nat) : UInt8 :=
  if j / 8 < k
  then ((toUInt64 (state.val[j / 8]!) >>>
            UInt64.ofNat ((7 - (j % 8)) * 8)) &&& 0xff).toUInt8
  else toUInt8 (out0.val[j]!)

-- NOTE: takes ~90-120s to elaborate; bump build timeout accordingly.
set_option maxHeartbeats 16000000 in
theorem sha512_inner_loop1_spec
    (state : Array U64 8#usize) (out : Array U8 64#usize) :
    Extraction.sha512_inner_loop1 ⟨0#usize, 8#usize⟩ state out
    ⦃ result => arrayU8ToVec result =
        Vector.ofFn (fun (j : Fin 64) =>
          let wordIdx : Fin 8 := ⟨j.val / 8, by omega⟩
          let byteIdx := j.val % 8
          (((arrayU64ToVec state)[wordIdx] >>>
              UInt64.ofNat ((7 - byteIdx) * 8)) &&& 0xff).toUInt8) ⦄ := by
  unfold Extraction.sha512_inner_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × Array U8 64#usize) =>
      8 - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Usize × Array U8 64#usize) =>
      p.1.«end».val = 8 ∧ p.1.start.val ≤ 8 ∧
      ∀ j, j < 64 →
        toUInt8 (p.2.val[j]!) = specByte state out p.1.start.val j)
  · -- step / done
    rintro ⟨iter, out'⟩ ⟨hend, hle, hinv⟩
    simp only at hend hle hinv
    show Extraction.sha512_inner_loop1.body state iter out' ⦃ _ ⦄
    unfold Extraction.sha512_inner_loop1.body
    rw [core.iter.range.IteratorRange.next_Usize_def, hend]
    by_cases hlt : iter.start.val < 8
    · simp only [hlt, ↓reduceIte]
      have hadd := @UScalar.add_spec _ iter.start 1#usize (by scalar_tac)
      simp only [spec, theta] at hadd
      revert hadd
      cases hadd_eval : iter.start + 1#usize with
      | ok next =>
        intro hadd
        simp only [wp_return] at hadd
        simp only [bind_tc_ok]
        step
        revert r r_post
        intro i1 i1_post
        simp only [lift, bind_tc_ok]
        -- 8-byte cascade: 24 more steps (8 byte writes × 3 ops each: getElem + add + update)
        step; step; step; step; step; step; step; step
        step; step; step; step; step; step; step; step
        step; step; step; step; step; step; step; step
        refine ⟨hend,
          by rw [hadd]; show iter.start.val + 1 ≤ 8; omega,
          ?_,
          by rw [hadd]; show 8 - (iter.start.val + 1) < 8 - iter.start.val; omega⟩
        intro j hj
        have hns : next.val = iter.start.val + 1 := by rw [hadd]; rfl
        have hi3v : i3.val = 8 * iter.start.val := by have := i3_post; omega
        have hi5v : i5.val = 8 * iter.start.val + 1 := by
          have h5 := i5_post; have h3 := i3_post; omega
        have hi7v : i7.val = 8 * iter.start.val + 2 := by
          have h7 := i7_post; have h3 := i3_post; omega
        have hi9v : i9.val = 8 * iter.start.val + 3 := by
          have h9 := i9_post; have h3 := i3_post; omega
        have hi11v : i11.val = 8 * iter.start.val + 4 := by
          have h11 := i11_post; have h3 := i3_post; omega
        have hi13v : i13.val = 8 * iter.start.val + 5 := by
          have h13 := i13_post; have h3 := i3_post; omega
        have hi15v : i15.val = 8 * iter.start.val + 6 := by
          have h15 := i15_post; have h3 := i3_post; omega
        have hi17v : i17.val = 8 * iter.start.val + 7 := by
          have h17 := i17_post; have h3 := i3_post; omega
        have hout'_len : out'.val.length = 64 := out'.property
        have ha_val : a.val =
            ((((((((out'.val.set (8*iter.start.val) i2).set
              (8*iter.start.val+1) i4).set
              (8*iter.start.val+2) i6).set
              (8*iter.start.val+3) i8).set
              (8*iter.start.val+4) i10).set
              (8*iter.start.val+5) i12).set
              (8*iter.start.val+6) i14).set
              (8*iter.start.val+7) i16) := by
          rw [a_post, out7_post, out6_post, out5_post, out4_post, out3_post,
              out2_post, out1_post]
          simp [Array.set_val_eq, hi3v, hi5v, hi7v, hi9v, hi11v, hi13v, hi15v, hi17v]
        have key_at : ∀ (k : Nat), k < 8 → a.val[8*iter.start.val + k]! =
            if k = 7 then i16 else if k = 6 then i14 else if k = 5 then i12
            else if k = 4 then i10 else if k = 3 then i8 else if k = 2 then i6
            else if k = 1 then i4 else i2 := by
          intro k hk
          rw [ha_val]
          simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set,
            List.length_set, hout'_len]
          split_ifs <;> first | rfl | omega
        have key_out : ∀ (k : Nat), (k < 8*iter.start.val ∨ 8*iter.start.val + 8 ≤ k) →
            k < 64 → a.val[k]! = out'.val[k]! := by
          intro k hk hklt
          rw [ha_val]
          simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set,
            List.length_set, hout'_len]
          split_ifs <;> first | rfl | omega
        have hinv_j := hinv j hj
        unfold specByte at hinv_j ⊢
        rw [hns]
        by_cases hjblock : j / 8 = iter.start.val
        · have hj_lt_next : j / 8 < iter.start.val + 1 := by omega
          simp only [hj_lt_next, ↓reduceIte]
          have hstate_j : state.val[j / 8]! = i1 := by rw [hjblock, ← i1_post]
          rw [hstate_j]
          have hjmod : j % 8 < 8 := Nat.mod_lt j (by norm_num)
          have hj_eq : j = 8 * iter.start.val + j % 8 := by
            have := Nat.div_add_mod j 8; omega
          have hkey := key_at (j % 8) hjmod
          rw [← hj_eq] at hkey
          rw [hkey]
          interval_cases (j % 8) <;> norm_num only <;>
            first
              | (rw [i2_post]; exact toUInt8_to_be_bytes_get i1 0 (by norm_num))
              | (rw [i4_post]; exact toUInt8_to_be_bytes_get i1 1 (by norm_num))
              | (rw [i6_post]; exact toUInt8_to_be_bytes_get i1 2 (by norm_num))
              | (rw [i8_post]; exact toUInt8_to_be_bytes_get i1 3 (by norm_num))
              | (rw [i10_post]; exact toUInt8_to_be_bytes_get i1 4 (by norm_num))
              | (rw [i12_post]; exact toUInt8_to_be_bytes_get i1 5 (by norm_num))
              | (rw [i14_post]; exact toUInt8_to_be_bytes_get i1 6 (by norm_num))
              | (rw [i16_post]; exact toUInt8_to_be_bytes_get i1 7 (by norm_num))
        · have hk_outside : j < 8*iter.start.val ∨ 8*iter.start.val + 8 ≤ j := by
            by_contra hc; push Not at hc; apply hjblock; omega
          rw [key_out j hk_outside hj]
          by_cases h_lt : j / 8 < iter.start.val <;>
            simp only [show j / 8 < iter.start.val + 1 ↔ j / 8 < iter.start.val from
              by constructor <;> omega, h_lt, ↓reduceIte] at hinv_j ⊢
          all_goals exact hinv_j
      | fail e => intro h; exact h.elim
      | div => intro h; exact h.elim
    · simp only [hlt, ↓reduceIte, bind_tc_ok]
      have hstart : iter.start.val = 8 := by omega
      apply Vector.ext
      intro j hj
      have hjlt : j < 64 := by simpa using hj
      have hjwi : j / 8 < 8 := by omega
      have hjk : j / 8 < iter.start.val := by rw [hstart]; exact hjwi
      change (arrayU8ToVec out')[j]'hjlt =
        ((Vector.ofFn fun (k : Fin 64) =>
            let wordIdx : Fin 8 := ⟨k.val / 8, by omega⟩
            let byteIdx := k.val % 8
            (((arrayU64ToVec state)[wordIdx] >>>
                UInt64.ofNat ((7 - byteIdx) * 8)) &&& 0xff).toUInt8) : Vector UInt8 64)[j]'hjlt
      rw [Vector.getElem_ofFn (h := hjlt)]
      rw [show (arrayU8ToVec out')[j]'hjlt = toUInt8 (out'.val[j]'(by simpa [out'.property] using hjlt))
          from arrayU8ToVec_getElem out' j hjlt]
      rw [show toUInt8 (out'.val[j]'(by rw [out'.property]; omega)) =
              toUInt8 (out'.val[j]!) by
            rw [getElem!_pos _ _ (by rw [out'.property]; omega)]]
      rw [hinv j hjlt]
      unfold specByte
      simp only [hjk, ↓reduceIte]
      have hgs : ((arrayU64ToVec state)[(⟨j/8, hjwi⟩ : Fin 8)]) =
          toUInt64 (state.val[j / 8]!) := by
        show ((arrayU64ToVec state)[j/8]'(by simpa [arrayU64ToVec] using hjwi)) = _
        rw [arrayU64ToVec_getElem state (j / 8) (by simp; exact hjwi)]
        congr 1
        rw [getElem!_pos _ _ (by rw [state.property]; exact hjwi)]
      rw [show ((arrayU64ToVec state)[(⟨j/8, by omega⟩ : Fin 8)]) =
            toUInt64 (state.val[j / 8]!) from hgs]
  · refine ⟨rfl, by simp, ?_⟩
    intro j _; simp [specByte]
