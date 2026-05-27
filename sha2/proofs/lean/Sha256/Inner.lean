import Word.U32
import Common.Vec

/-!
# IV-parameterized SHA-256 Impl bridge

The fips-180-4-lean dependency now exposes both `SHS.SHA256.Impl.sha256`
and `SHS.SHA256.Impl.sha224` as thin wrappers around the IV-parameterized
core `SHS.SHA256.Impl.sha256State`. This module bridges between the
upstream wrappers and an IV-parameterized digest-level engine
`Local.sha2Inner256` used by the IV-generic refinement spec
(`Sha2InnerSpec.lean`).

Declarations placed under `Local` (rather than injected into the upstream
`SHS.SHA256.Impl` namespace):

* `Local.sha2Inner256` — IV-parameterized SHA-256 digest engine (no panic).
* `Local.sha256_eq_sha2Inner256` — `Impl.sha256 = sha2Inner256 H256_256` (1).
* `Local.sha224_eq_sha2Inner256_take` — `Impl.sha224 = take 28 of sha2Inner256 H256_224` (1).
* `Local.sha2_H256_224_val` / `Local.H256_224_eq` — Aeneas IV constant bridges.

(1) under the FIPS 180-4 §5.1.1 length cap `data.size < 2^61`.
-/

open Aeneas Aeneas.Std
open SHS.SHA256
open SHS.SHA256.Impl
  (State Block compress toU32s toU32sFromBytes
   H256_256 H256_224 sha256 sha224 sha256State)

namespace Local

/-- IV-parameterized SHA-256 digest engine (no 2^61 panic).  Built on top
of upstream's `Impl.sha256State` so this module needs no per-block-fold
proofs of its own; `sha2Inner256 H256_256` coincides with `Impl.sha256`
on valid inputs (`sha256_eq_sha2Inner256`), and `take 28` of
`sha2Inner256 H256_224` coincides with `Impl.sha224`
(`sha224_eq_sha2Inner256_take`). -/
def sha2Inner256 (iv : Vector UInt32 8) (data : ByteArray) : Vector UInt8 32 :=
  let state := sha256State data iv
  Vector.ofFn fun i : Fin 32 =>
    let wordIdx : Fin 8 := ⟨i.val / 4, by omega⟩
    let byteIdx := i.val % 4
    ((state[wordIdx] >>> (UInt32.ofNat ((3 - byteIdx) * 8))) &&& 0xff).toUInt8

/-- `Impl.sha256` agrees with the IV-parameterized core at `H256_256`,
provided the FIPS 180-4 §5.1.1 length cap holds. -/
theorem sha256_eq_sha2Inner256 (data : ByteArray) (h : data.size < 2 ^ 61) :
    sha256 data = sha2Inner256 H256_256 data := by
  unfold sha256 sha2Inner256
  rw [if_neg (by omega : ¬ 2 ^ 61 ≤ data.size)]

/-- `Impl.sha224` agrees with the first 28 bytes of the IV-parameterized
core at `H256_224`, provided the FIPS 180-4 §5.1.1 length cap holds.
Both sides BE-emit the same `sha256State data H256_224`; the SHA-256
emit produces 32 bytes (truncated to 28) and the SHA-224 emit produces
28 bytes directly — they agree byte-for-byte for the first 28. -/
theorem sha224_eq_sha2Inner256_take (data : ByteArray) (h : data.size < 2 ^ 61) :
    (sha224 data).toList = (sha2Inner256 H256_224 data).toList.take 28 := by
  unfold sha224 sha2Inner256
  rw [if_neg (by omega : ¬ 2 ^ 61 ≤ data.size)]
  exact vector_ofFn_take_of_agree (K := 28) (M := 32) (by decide) _ _ (fun _ _ => rfl)

/-- Unfold the Aeneas-extracted `H256_224` constants table to a literal list.
The Aeneas definition is marked `@[irreducible]`, so we expose its body
behind a non-irreducible name. -/
theorem sha2_H256_224_val :
    (Extraction.consts.H256_224 : Array U32 8#usize).val =
      [3238371032#u32, 914150663#u32, 812702999#u32, 4144912697#u32,
       4290775857#u32, 1750603025#u32, 1694076839#u32, 3204075428#u32] := by
  unfold Extraction.consts.H256_224; rfl

/-- The Aeneas-extracted SHA-224 IV bridges to the upstream `Impl.H256_224`. -/
theorem H256_224_eq :
    arrayU32ToVec Extraction.consts.H256_224 = H256_224 := by
  apply Vector.toList_inj.mp; rw [arrayU32ToVec_toList]
  show (Extraction.consts.H256_224 : Array U32 8#usize).val.map toUInt32 = H256_224.toList
  rw [sha2_H256_224_val]; decide

end Local
