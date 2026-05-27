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
      ((toUInt64 x >>> (UInt64.ofNat ((7 - k) * 8))) &&& 0xff).toUInt8 :=
  toUInt8_be_byte x k hk

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

/-
Strategy:

The proof is shaped around `loop.spec_decr_nat`, with measure
`8 - iter.start.val` and an invariant (`hinv`) saying that every byte
slot `j < 64` is either already a `specByte` (if `j / 8 < iter.start`)
or still the input byte. The proof has two arms:

* **Step arm** (`iter.start.val < 8`): the loop body emits 8 bytes from
  state word `i1 = state[iter.start.val]`. After `cases (iter.start + 1)`
  to get a usable carry result, `iterate 24 step` walks the eight-byte
  cascade (8 byte writes, 3 monadic ops each: shift+getElem, index+1,
  array set). Two helper `have`s drive the invariant rebuild:
  * `key_at k hk` resolves `a.val[8*iter.start.val + k]!` in the eight-
    deep nested `.set` chain to the right `i{2,4,...,16}` literal;
  * `key_out k hk hklt` resolves indices outside the just-written
    block to the previous `out'.val[k]!`.
  Then `by_cases hjblock : j / 8 = iter.start.val` separates the
  freshly-written block (closed by `interval_cases (j % 8)` plus an
  eight-way `first | ...` cascade dispatching on
  `toUInt8_to_be_bytes_get`) from earlier blocks (closed via `hinv_j`
  and `key_out`).

* **Done arm** (`8 ≤ iter.start.val`): the invariant gives a pointwise
  byte equality; `Vector.ext` reduces vector equality to per-index, and
  the `arrayU{8,64}ToVec_getElem` bridges + `getElem!_pos` reconcile
  the `Vector.ofFn` projection against the `.val[j]!` form `hinv`
  produces.

Mirrors `Sha256/Loop1.lean::sha256_inner_loop1_spec` at width 32 / 64
(8 state words of 8 bytes each, vs SHA-256's 8 words of 4 bytes).
-/
/-
The `maxHeartbeats 16000000` budget below is load-bearing: each
iteration of the byte-extraction loop unfolds dozens of monadic calls,
and the invariant rebuild splits on `j / 8` against `iter.start.val`,
pushing elaboration ~80× past the 200K default. 16M is the smallest
power-of-two budget that closes; lowering it produces a deterministic
timeout. NOTE: this proof takes ~90-120s wall-clock — bump the build
timeout accordingly.
-/
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
    · -- Step arm: emit 8 bytes from state word `iter.start.val`.
      simp only [hlt, ↓reduceIte]
      have hadd := @UScalar.add_spec _ iter.start 1#usize (by scalar_tac)
      simp only [spec, theta] at hadd
      revert hadd
      cases hadd_eval : iter.start + 1#usize with
      | ok next =>
        intro hadd
        simp only [wp_return, bind_tc_ok] at hadd ⊢
        step as ⟨i1, i1_post⟩
        simp only [lift, bind_tc_ok]
        -- 8-byte cascade: 24 more steps (8 byte writes × 3 ops each: getElem + add + update)
        iterate 24 step
        refine ⟨hend, by rw [hadd]; agrind, ?_, by rw [hadd]; agrind⟩
        intro j hj
        have hns : next.val = iter.start.val + 1 := hadd
        have hi3v : i3.val = 8 * iter.start.val := by agrind
        have hi5v : i5.val = 8 * iter.start.val + 1 := by agrind
        have hi7v : i7.val = 8 * iter.start.val + 2 := by agrind
        have hi9v : i9.val = 8 * iter.start.val + 3 := by agrind
        have hi11v : i11.val = 8 * iter.start.val + 4 := by agrind
        have hi13v : i13.val = 8 * iter.start.val + 5 := by agrind
        have hi15v : i15.val = 8 * iter.start.val + 6 := by agrind
        have hi17v : i17.val = 8 * iter.start.val + 7 := by agrind
        have hout'_len : out'.val.length = 64 := out'.property
        have ha_val : a.val =
            ((((((((out'.val.set (8*iter.start.val) i2).set (8*iter.start.val+1) i4).set
              (8*iter.start.val+2) i6).set (8*iter.start.val+3) i8).set
              (8*iter.start.val+4) i10).set (8*iter.start.val+5) i12).set
              (8*iter.start.val+6) i14).set (8*iter.start.val+7) i16) := by
          rw [a_post, out7_post, out6_post, out5_post, out4_post, out3_post, out2_post, out1_post]
          simp [Array.set_val_eq, hi3v, hi5v, hi7v, hi9v, hi11v, hi13v, hi15v, hi17v]
        have key_at : ∀ (k : Nat), k < 8 → a.val[8*iter.start.val + k]! =
            if k = 7 then i16 else if k = 6 then i14 else if k = 5 then i12
            else if k = 4 then i10 else if k = 3 then i8 else if k = 2 then i6
            else if k = 1 then i4 else i2 := by
          intro k hk; rw [ha_val]
          simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set, List.length_set, hout'_len]
          split_ifs <;> first | rfl | agrind
        have key_out : ∀ (k : Nat), (k < 8*iter.start.val ∨ 8*iter.start.val + 8 ≤ k) →
            k < 64 → a.val[k]! = out'.val[k]! := by
          intro k hk hklt; rw [ha_val]
          simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set, List.length_set, hout'_len]
          split_ifs <;> first | rfl | agrind
        have hinv_j := hinv j hj
        unfold specByte at hinv_j ⊢; rw [hns]
        by_cases hjblock : j / 8 = iter.start.val
        · simp only [show j / 8 < iter.start.val + 1 from by agrind, ↓reduceIte]
          rw [show state.val[j / 8]! = i1 from by rw [hjblock, ← i1_post]]
          have hjmod : j % 8 < 8 := by agrind
          have hkey := key_at (j % 8) hjmod
          rw [← show j = 8 * iter.start.val + j % 8 from by agrind] at hkey; rw [hkey]
          /- The eight `i{2,4,…,16}_post` postconditions are not
             syntactically uniform (each names a different shift
             constant), so a single `simp [*]` will not close all
             branches. `interval_cases (j % 8)` produces the 8 byte
             positions; for each, the `first | ...` cascade picks the
             matching post-hypothesis and closes via
             `toUInt8_to_be_bytes_get` at the right byte index. -/
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
        · rw [key_out j (by agrind) hj]
          simp only [show j / 8 < iter.start.val + 1 ↔ j / 8 < iter.start.val
            from by agrind] at hinv_j ⊢; exact hinv_j
      | fail _ | div => intro h; exact h.elim
    · -- Done arm: invariant already covers every byte; reconcile shapes.
      simp only [hlt, ↓reduceIte, bind_tc_ok]
      apply Vector.ext
      intro j hj
      have hjlt : j < 64 := by agrind
      have hjk : j / 8 < iter.start.val := by agrind
      change (arrayU8ToVec out')[j]'hjlt =
        ((Vector.ofFn fun (k : Fin 64) =>
            let wordIdx : Fin 8 := ⟨k.val / 8, by omega⟩
            let byteIdx := k.val % 8
            (((arrayU64ToVec state)[wordIdx] >>>
                UInt64.ofNat ((7 - byteIdx) * 8)) &&& 0xff).toUInt8) : Vector UInt8 64)[j]'hjlt
      rw [Vector.getElem_ofFn (h := hjlt)]
      rw [show (arrayU8ToVec out')[j]'hjlt = toUInt8 (out'.val[j]'(by agrind))
          from arrayU8ToVec_getElem out' j hjlt]
      rw [show toUInt8 (out'.val[j]'(by agrind)) = toUInt8 (out'.val[j]!) by
            rw [getElem!_pos _ _ (by agrind)]]
      rw [hinv j hjlt]
      unfold specByte
      simp only [hjk, ↓reduceIte]
      have hgs : ((arrayU64ToVec state)[(⟨j/8, by omega⟩ : Fin 8)]) =
          toUInt64 (state.val[j / 8]!) := by
        show ((arrayU64ToVec state)[j/8]'(by agrind)) = _
        rw [arrayU64ToVec_getElem state (j / 8) (by agrind)]; fcongr 1
        rw [getElem!_pos _ _ (by agrind)]
      rw [hgs]
  · exact ⟨rfl, by simp, fun _ _ => by simp [specByte]⟩
