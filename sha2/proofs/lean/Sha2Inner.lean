import U32

/-!
# IV-parameterized SHA-256 Impl-layer core, and SHA-224

The fips-180-4-lean dependency exposes `SHS.SHA256.Impl.sha256` with the
`H256_256` IV baked in.  SHA-224 is the same engine with `H256_224` and a
28-byte truncation (FIPS 180-4 §6.3).  Rather than refactor upstream
`Impl.sha256` or inject new declarations into upstream namespaces, this
module places all downstream additions under a fresh `Local` namespace:

* `Local.sha2Inner256` — IV-parameterized SHA-256 core (no `2^61` panic).
* `Local.H256_224` — the SHA-224 initial hash value (FIPS §5.3.2).
* `Local.sha224` — `(sha2Inner256 H256_224 _).take 28` (FIPS §6.3).
* `Local.sha256_eq_sha2Inner256` — `Impl.sha256 _ = sha2Inner256 H256_256 _`
  under the `2^61` precondition; lets the IV-generic refinement bridge
  apply to SHA-256.
* `Local.sha2_H256_224_val` / `Local.H256_224_eq` — Aeneas IV constant
  bridges for SHA-224.

The Aeneas-extracted refinement proof in `Sha224.lean` bridges
`Extraction.sha224` to `Local.sha224` by reusing the SHA-256 inner-spec
machinery (`Sha2InnerSpec.lean`) on a swapped IV.
-/

open Aeneas Aeneas.Std
open SHS.SHA256
open SHS.SHA256.Impl
  (State Block compress toU32s toU32sFromBytes H256_256 sha256)

namespace Local

/-- SHA-224 initial hash value (FIPS 180-4 §5.3.2): first 32 bits of the
fractional parts of the square roots of the 9th through 16th primes. -/
def H256_224 : Vector UInt32 8 :=
  #v[ 0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939,
      0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4 ]

/-- IV-parameterized SHA-256 core (no 2^61 panic).  The body is identical
to `Impl.sha256` with `H256_256` replaced by `iv`; padding, the per-block
fold, and the BE byte emit are unchanged.  This is the shared engine
between `Impl.sha256` and `Local.sha224`. -/
def sha2Inner256 (iv : Vector UInt32 8) (data : ByteArray) : Vector UInt8 32 :=
  let blocks    := data.size / 64
  let remaining := data.size % 64
  let totalBits : UInt64 := data.size.toUInt64 <<< 3
  let state : State := Fin.foldl blocks (fun state (i : Fin blocks) =>
    compress state (toU32sFromBytes data (i.val * 64))) iv
  let finalBlockA : Vector UInt8 64 := Vector.ofFn fun i : Fin 64 =>
    if i.val < remaining then data.get! (blocks * 64 + i.val)
    else if i.val = remaining then 0x80
    else 0
  let (state, finalBlockB) :=
    if remaining < 56 then (state, finalBlockA)
    else
      (compress state (toU32s finalBlockA),
       Vector.ofFn (fun _ : Fin 64 => (0 : UInt8)))
  let finalBlockC : Vector UInt8 64 := Vector.ofFn fun i : Fin 64 =>
    if i.val < 56 then finalBlockB[i]
    else ((totalBits >>> (((63 - i.val) * 8).toUInt64)) &&& 0xff).toUInt8
  let state := compress state (toU32s finalBlockC)
  Vector.ofFn fun i : Fin 32 =>
    let wordIdx : Fin 8 := ⟨i.val / 4, by omega⟩
    let byteIdx := i.val % 4
    ((state[wordIdx] >>> (UInt32.ofNat ((3 - byteIdx) * 8))) &&& 0xff).toUInt8

/-- `Impl.sha256` agrees with the IV-parameterized core at `H256_256`,
provided the FIPS 180-4 §5.1.1 length cap holds.  This lets us reuse the
generic refinement bridge for SHA-256 with no proof rework. -/
theorem sha256_eq_sha2Inner256 (data : ByteArray) (h : data.size < 2 ^ 61) :
    sha256 data = sha2Inner256 H256_256 data := by
  unfold sha256 sha2Inner256
  rw [if_neg (by omega : ¬ 2 ^ 61 ≤ data.size)]

/-- FIPS 180-4 §6.3: SHA-224 is SHA-256 with `H256_224` IV, truncated to
28 bytes (the leftmost seven 32-bit words). -/
def sha224 (data : ByteArray) : Vector UInt8 28 :=
  Vector.cast (by decide) ((sha2Inner256 H256_224 data).take 28)

theorem sha224_toList (data : ByteArray) :
    (sha224 data).toList = (sha2Inner256 H256_224 data).toList.take 28 := by
  unfold sha224
  rw [Vector.toList_cast, Vector.toList_take]

/-- Unfold the Aeneas-extracted `H256_224` constants table to a literal list.
The Aeneas definition is marked `@[irreducible]`, so we expose its body
behind a non-irreducible name. -/
theorem sha2_H256_224_val :
    (Extraction.consts.H256_224 : Array U32 8#usize).val =
      [3238371032#u32, 914150663#u32, 812702999#u32, 4144912697#u32,
       4290775857#u32, 1750603025#u32, 1694076839#u32, 3204075428#u32] := by
  unfold Extraction.consts.H256_224
  rfl

/-- The Aeneas-extracted SHA-224 IV bridges to the local-Impl `H256_224`. -/
theorem H256_224_eq :
    arrayU32ToVec Extraction.consts.H256_224 = H256_224 := by
  apply Vector.toList_inj.mp
  rw [arrayU32ToVec_toList]
  show (Extraction.consts.H256_224 : Array U32 8#usize).val.map toUInt32 =
    H256_224.toList
  rw [sha2_H256_224_val]
  decide

end Local
