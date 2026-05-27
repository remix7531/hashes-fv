import Word.U32
import Sha256.FinalBlock
import Aeneas

/-!
# Refinement of `sha256_inner_loop1` against the spec's BE-emit step

The Aeneas extraction's final loop walks `state : Array U32 8` and emits
big-endian bytes into `out : Array U8 32`. The FIPS-spec `Impl.sha256`'s
final step is a single `Vector.ofFn (Fin 32 → UInt8)` doing the same
thing. We bridge the two.
-/

open Aeneas Aeneas.Std Result WP SHS.SHA256

/-! ## Big-endian byte split for U32

Width-32 specialization of the shared shift-and-mask identity
`BitVec.toBEBytes_getElem!_eq_shift_mask` (upstream Aeneas, in
`Aeneas.Data.BitVec`); the width-64 sibling `toUInt8_be_byte` lives in
`FinalBlock.lean`. -/

/-- Byte `i` (`i < 4`) of the BE-encoding of a `U32` equals the
shift-and-mask form `((toUInt32 x >>> ((3-i)*8)) &&& 0xff).toUInt8`. -/
/- Strategy: chain three bridges to land on the upstream Aeneas identity.
   First normalise the LHS to `UScalar.mk (x.bv.toBEBytes[i]!)` via
   `List.getElem_map` (`hmap`), then apply
   `BitVec.toBEBytes_getElem!_eq_shift_mask` at width 32 to rewrite into
   a `>>>`/`&&&` form on `BitVec 32`. The remaining task is to identify
   the U32-domain shift `(UInt32.ofNat ((3-i)*8)).toBitVec % 32` with
   the BitVec-domain shift `BitVec.ofNat 32 ((3-i)*8)`: this needs
   `BitVec.eq_of_toNat_eq` plus `Nat.mod_eq_of_lt` (`hk_lt`).
   The two `fcongr 1` steps push the equality inward through the
   `&&& 0xff` and the `>>>` so each leaf can close by `rfl`/`omega`. -/
theorem toUInt8_be_byte_U32 (x : U32) (i : Nat) (hi : i < 4) :
    toUInt8 ((x.bv.toBEBytes.map (UScalar.mk (ty := .U8)) : List U8)[i]!) =
      ((toUInt32 x >>> (UInt32.ofNat ((3 - i) * 8))) &&& 0xff).toUInt8 := by
  have hlen_be : x.bv.toBEBytes.length = 4 := BitVec.toBEBytes_length x.bv (by decide)
  have hmap : (x.bv.toBEBytes.map (UScalar.mk (ty := .U8)) : List U8)[i]! =
              UScalar.mk (ty := .U8) (x.bv.toBEBytes[i]!) := by
    simp [getElem!_pos, hlen_be, hi, List.getElem_map]
  rw [hmap]; apply UInt8.toBitVec_inj.mp
  show x.bv.toBEBytes[i]! = _
  rw [BitVec.toBEBytes_getElem!_eq_shift_mask (n := 32) (by decide) x.bv i
        (by simpa using hi), show (32 / 8 - 1 - i) = (3 - i) from by omega]
  show _ = ((((toUInt32 x >>> (UInt32.ofNat ((3 - i) * 8))) &&& 0xff)).toBitVec).setWidth 8
  fcongr 1
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_shiftRight,
    show (toUInt32 x).toBitVec = x.bv from rfl,
    show UInt32.toBitVec 255 = (BitVec.ofNat 32 0xff) from rfl]
  have hk_lt : (3 - i) * 8 < 32 := by scalar_tac +nonLin
  have h2 : ((UInt32.ofNat ((3 - i) * 8)).toBitVec % 32 : BitVec 32) =
            BitVec.ofNat 32 ((3 - i) * 8) := by
    rw [show (UInt32.ofNat ((3 - i) * 8)).toBitVec = BitVec.ofNat 32 ((3 - i) * 8) from rfl]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_umod, BitVec.toNat_ofNat]
    rw [show (32 : BitVec 32).toNat = 32 from rfl]; omega
  rw [h2]
  fcongr 1
  show _ = x.bv >>> (BitVec.ofNat 32 ((3 - i) * 8)).toNat
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- Consumer-facing form: indexing `to_be_bytes x` directly. -/
private theorem toUInt8_to_be_bytes_get (x : U32) (k : Nat) (hk : k < 4) :
    toUInt8 ((core.num.U32.to_be_bytes x).val[k]!) =
      ((toUInt32 x >>> UInt32.ofNat ((3 - k) * 8)) &&& 0xff).toUInt8 := by
  show toUInt8 ((x.bv.toBEBytes.map (UScalar.mk (ty := .U8)) : List U8)[k]!) = _
  exact toUInt8_be_byte_U32 x k hk

/-! ## Loop-level spec via `loop.spec_decr_nat`

The invariant tracks the partial fill: for every byte slot `j < 32`, the
output's `j`-th byte equals the spec byte if its word-index `j / 4` has
already been processed (`j / 4 < iter.start.val`), else the original
input byte. -/

/-- Spec byte at output slot `j` after `k` words processed. Indexes via
`getElem!` to avoid threading bounds through proof terms. -/
private def specByte (state : Array U32 8#usize) (out0 : Array U8 32#usize)
    (k : Nat) (j : Nat) : UInt8 :=
  if j / 4 < k
  then ((toUInt32 (state.val[j / 4]!) >>>
            UInt32.ofNat ((3 - (j % 4)) * 8)) &&& 0xff).toUInt8
  else toUInt8 (out0.val[j]!)

/-- **Main spec**: `sha256_inner_loop1` from `0..8` produces an output whose
`arrayU8ToVec` view equals the spec's final BE-emit `Vector.ofFn`. -/
/- Strategy: `loop.spec_decr_nat` with measure `8 - iter.start.val` and the
   `specByte`-flavoured invariant above. The proof then splits on the
   `by_cases hlt : iter.start.val < 8` step/done dichotomy.

   Step branch. `UScalar.add_spec` discharges the `iter.start + 1#usize`
   bind via `cases hadd_eval` so the success case carries `next.val =
   iter.start.val + 1`. The body's 4-byte cascade (read state word `i1`,
   then four `to_be_bytes`-byte / `Array.update_usize` pairs) consumes
   one `step as ⟨i1, i1_post⟩` plus `iterate 12 step`. The
   updated array `a.val` is then characterised by two named keys:
   `key_at` (the four written slots `4s..4s+3` get `i2,i4,i6,i8`) and
   `key_out` (every other slot is unchanged from `out'`). Reasoning on
   `j` splits on `by_cases hjblock : j / 4 = iter.start.val`. The
   in-block branch combines `key_at` with `interval_cases (j % 4)` and
   closes each of four cases via the `toUInt8_to_be_bytes_get` lemma
   above. The out-of-block branch uses `key_out` and reduces to the
   prior invariant `hinv_j` (the `j / 4 < iter.start.val + 1 ↔
   j / 4 < iter.start.val` rewrite holds because `j / 4 ≠
   iter.start.val`).

   Done branch. `hlt = false` forces `iter.start.val = 8`, so
   `j / 4 < iter.start.val` holds for every `j < 32`. The goal becomes
   pointwise equality of two 32-vectors, discharged by `Vector.ext`,
   `Vector.getElem_ofFn`, `arrayU8ToVec_getElem`, and `getElem!_pos`
   bridges, ending in a single rewrite via `hinv j hjlt` and the
   `arrayU32ToVec_getElem` view on the state.

   Sibling: `Sha512/Loop1.lean::sha512_inner_loop1_spec` mirrors this
   proof at width 64 with an 8-byte cascade (`iterate 24 step`, eight
   `interval_cases` arms) and a 16M-heartbeat budget; the SHA-256 proof
   stays within the default. -/
theorem sha256_inner_loop1_spec
    (state : Array U32 8#usize) (out : Array U8 32#usize) :
    Extraction.sha256_inner_loop1 ⟨0#usize, 8#usize⟩ state out
    ⦃ result => arrayU8ToVec result =
        Vector.ofFn (fun (j : Fin 32) =>
          let wordIdx : Fin 8 := ⟨j.val / 4, by omega⟩
          let byteIdx := j.val % 4
          (((arrayU32ToVec state)[wordIdx] >>>
              UInt32.ofNat ((3 - byteIdx) * 8)) &&& 0xff).toUInt8) ⦄ := by
  unfold Extraction.sha256_inner_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × Array U8 32#usize) =>
      8 - p.1.start.val)
    (inv := fun (p : core.ops.range.Range Usize × Array U8 32#usize) =>
      p.1.«end».val = 8 ∧ p.1.start.val ≤ 8 ∧
      ∀ j, j < 32 →
        toUInt8 (p.2.val[j]!) = specByte state out p.1.start.val j)
  · -- step / done
    rintro ⟨iter, out'⟩ ⟨hend, hle, hinv⟩
    simp only at hend hle hinv
    show Extraction.sha256_inner_loop1.body state iter out' ⦃ _ ⦄
    unfold Extraction.sha256_inner_loop1.body
    rw [core.iter.range.IteratorRange.next_Usize_def, hend]
    by_cases hlt : iter.start.val < 8
    · simp only [hlt, ↓reduceIte]
      have hadd := @UScalar.add_spec _ iter.start 1#usize (by scalar_tac)
      simp only [spec, theta] at hadd; revert hadd
      cases hadd_eval : iter.start + 1#usize with
      | ok next =>
        intro hadd; simp only [wp_return] at hadd; simp only [bind_tc_ok]
        -- The first inner `step` consumes `let i1 ← Array.index_usize state i`;
        -- using `step as` to bind the post-name directly avoids the rename dance.
        step as ⟨i1, i1_post⟩
        simp only [lift, bind_tc_ok]
        iterate 12 step
        refine ⟨hend, by rw [hadd]; scalar_tac, ?_, by rw [hadd]; scalar_tac⟩
        intro j hj
        have hns : next.val = iter.start.val + 1 := by rw [hadd]; rfl
        have hi3v : i3.val = 4 * iter.start.val := by scalar_tac
        have hi5v : i5.val = 4 * iter.start.val + 1 := by scalar_tac
        have hi7v : i7.val = 4 * iter.start.val + 2 := by scalar_tac
        have hi9v : i9.val = 4 * iter.start.val + 3 := by scalar_tac
        have hout'_len : out'.val.length = 32 := out'.property
        have ha_val : a.val = (((out'.val.set (4*iter.start.val) i2).set
            (4*iter.start.val+1) i4).set (4*iter.start.val+2) i6).set
            (4*iter.start.val+3) i8 := by
          simp [a_post, out3_post, out2_post, out1_post, Array.set_val_eq, hi3v, hi5v, hi7v, hi9v]
        -- `a.val[4s+k]!` for k ∈ {0,1,2,3}.
        have key_at : ∀ (k : Nat), k < 4 → a.val[4*iter.start.val + k]! =
            if k = 3 then i8 else if k = 2 then i6 else if k = 1 then i4 else i2 := by
          intro k _; rw [ha_val]
          simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set,
            List.length_set, hout'_len]; split_ifs <;> first | rfl | omega
        -- `a.val[k]! = out'.val[k]!` for k outside [4s, 4s+3].
        have key_out : ∀ (k : Nat), (k < 4*iter.start.val ∨ 4*iter.start.val + 4 ≤ k) →
            k < 32 → a.val[k]! = out'.val[k]! := by
          intro k _ _; rw [ha_val]
          simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set,
            List.length_set, hout'_len]; split_ifs <;> first | rfl | omega
        have hinv_j := hinv j hj
        unfold specByte at hinv_j ⊢
        rw [hns]
        by_cases hjblock : j / 4 = iter.start.val
        · -- j ∈ [4s, 4s+3]: a.val[j]! is the corresponding `to_be_bytes` byte.
          have hj_lt_next : j / 4 < iter.start.val + 1 := by omega
          simp only [hj_lt_next, ↓reduceIte]
          have hstate_j : state.val[j / 4]! = i1 := by rw [hjblock, ← i1_post]
          have hjmod : j % 4 < 4 := Nat.mod_lt j (by norm_num)
          have hj_eq : j = 4 * iter.start.val + j % 4 := by
            have := Nat.div_add_mod j 4; omega
          have hkey := key_at (j % 4) hjmod
          rw [← hj_eq] at hkey
          rw [hstate_j, hkey]
          interval_cases (j % 4) <;> norm_num only <;> first
            | (rw [i2_post]; exact toUInt8_to_be_bytes_get i1 0 (by norm_num))
            | (rw [i4_post]; exact toUInt8_to_be_bytes_get i1 1 (by norm_num))
            | (rw [i6_post]; exact toUInt8_to_be_bytes_get i1 2 (by norm_num))
            | (rw [i8_post]; exact toUInt8_to_be_bytes_get i1 3 (by norm_num))
        · -- j ∉ [4s, 4s+3]: a.val[j]! is unchanged from out'.val[j]!,
          -- and hinv_j gives the matching invariant on out'.
          have hk_outside : j < 4*iter.start.val ∨ 4*iter.start.val + 4 ≤ j := by omega
          rw [key_out j hk_outside hj]
          have hsuc_iff : j / 4 < iter.start.val + 1 ↔ j / 4 < iter.start.val :=
            by omega
          by_cases h_lt : j / 4 < iter.start.val
          · -- j / 4 < iter.start.val: invariant survives the iteration bump.
            simp only [hsuc_iff, h_lt, ↓reduceIte] at hinv_j ⊢
            exact hinv_j
          · -- j / 4 ≥ iter.start.val (and ≠ iter.start.val since hjblock fails):
            -- invariant is the trivial else-branch on both sides.
            simp only [hsuc_iff, h_lt, ↓reduceIte] at hinv_j ⊢
            exact hinv_j
      | fail _ => intro h; exact h.elim
      | div => intro h; exact h.elim
    · -- done
      simp only [hlt, ↓reduceIte, bind_tc_ok]
      have hstart : iter.start.val = 8 := by omega
      apply Vector.ext; intro j hj
      have hjlt : j < 32 := by simpa using hj
      have hjwi : j / 4 < 8 := by omega
      have hjk : j / 4 < iter.start.val := by omega
      change (arrayU8ToVec out')[j]'hjlt =
        ((Vector.ofFn fun (k : Fin 32) =>
            let wordIdx : Fin 8 := ⟨k.val / 4, by omega⟩
            let byteIdx := k.val % 4
            (((arrayU32ToVec state)[wordIdx] >>>
                UInt32.ofNat ((3 - byteIdx) * 8)) &&& 0xff).toUInt8) : Vector UInt8 32)[j]'hjlt
      rw [Vector.getElem_ofFn (h := hjlt),
          show (arrayU8ToVec out')[j]'hjlt =
              toUInt8 (out'.val[j]'(by simpa [out'.property] using hjlt))
            from arrayU8ToVec_getElem out' j hjlt,
          show toUInt8 (out'.val[j]'(by rw [out'.property]; omega)) =
              toUInt8 (out'.val[j]!) by
            rw [getElem!_pos _ _ (by rw [out'.property]; omega)],
          hinv j hjlt]
      unfold specByte
      simp only [hjk, ↓reduceIte]
      have hgs : ((arrayU32ToVec state)[(⟨j/4, hjwi⟩ : Fin 8)]) =
          toUInt32 (state.val[j / 4]!) := by
        show ((arrayU32ToVec state)[j/4]'(by simpa [arrayU32ToVec] using hjwi)) = _
        rw [arrayU32ToVec_getElem state (j / 4) (by simpa using hjwi)]
        fcongr 1; rw [getElem!_pos _ _ (by rw [state.property]; exact hjwi)]
      rw [show ((arrayU32ToVec state)[(⟨j/4, by omega⟩ : Fin 8)]) =
            toUInt32 (state.val[j / 4]!) from hgs]
  · -- initial invariant
    refine ⟨rfl, by simp, ?_⟩
    intro j _; simp [specByte]
