import Word.U64
import Common.Vec

/-!
# IV-parameterized SHA-512 Impl bridge

64-bit analogue of `Sha256/Inner.lean`.  The fips-180-4-lean dependency
exposes `Impl.sha512`, `Impl.sha384`, `Impl.sha512_256`, `Impl.sha512_224`
as thin wrappers around the IV-parameterized core `Impl.sha512State`.
This module bridges between the upstream wrappers and an IV-parameterized
digest-level engine `Local.sha2Inner512` used by `Sha512/InnerSpec.lean`.
-/

open Aeneas Aeneas.Std
open SHS.SHA512
open SHS.SHA512.Impl
  (State Block compress toU64s toU64sFromBytes
   H0_512 H0_384 H0_512_256 H0_512_224
   sha512 sha384 sha512_256 sha512_224 sha512State)

namespace Local

/-- IV-parameterized SHA-512 digest engine (no 2^61 panic). -/
def sha2Inner512 (iv : Vector UInt64 8) (data : ByteArray) : Vector UInt8 64 :=
  let state := sha512State data iv
  Vector.ofFn fun i : Fin 64 =>
    let wordIdx : Fin 8 := ⟨i.val / 8, by omega⟩
    let byteIdx := i.val % 8
    ((state[wordIdx] >>> (UInt64.ofNat ((7 - byteIdx) * 8))) &&& 0xff).toUInt8

/-- `Impl.sha512` agrees with the IV-parameterized core at `H0_512`. -/
theorem sha512_eq_sha2Inner512 (data : ByteArray) (h : data.size < 2 ^ 61) :
    sha512 data = sha2Inner512 H0_512 data := by
  unfold sha512 sha2Inner512
  rw [if_neg (by omega : ¬ 2 ^ 61 ≤ data.size)]

/-- `Impl.sha384` is the first 48 bytes of the IV-parameterized core at `H0_384`. -/
theorem sha384_eq_sha2Inner512_take (data : ByteArray) (h : data.size < 2 ^ 61) :
    (sha384 data).toList = (sha2Inner512 H0_384 data).toList.take 48 := by
  unfold sha384 sha2Inner512
  rw [if_neg (by omega : ¬ 2 ^ 61 ≤ data.size)]
  exact vector_ofFn_take_of_agree (K := 48) (M := 64) (by decide) _ _ (fun _ _ => rfl)

/-- `Impl.sha512_256` is the first 32 bytes of the IV-parameterized core at `H0_512_256`. -/
theorem sha512_256_eq_sha2Inner512_take (data : ByteArray) (h : data.size < 2 ^ 61) :
    (sha512_256 data).toList = (sha2Inner512 H0_512_256 data).toList.take 32 := by
  unfold sha512_256 sha2Inner512
  rw [if_neg (by omega : ¬ 2 ^ 61 ≤ data.size)]
  exact vector_ofFn_take_of_agree (K := 32) (M := 64) (by decide) _ _ (fun _ _ => rfl)

/-- `Impl.sha512_224` is the first 28 bytes of the IV-parameterized core at `H0_512_224`. -/
theorem sha512_224_eq_sha2Inner512_take (data : ByteArray) (h : data.size < 2 ^ 61) :
    (sha512_224 data).toList = (sha2Inner512 H0_512_224 data).toList.take 28 := by
  unfold sha512_224 sha2Inner512
  rw [if_neg (by omega : ¬ 2 ^ 61 ≤ data.size)]
  exact vector_ofFn_take_of_agree (K := 28) (M := 64) (by decide) _ _ (fun _ _ => rfl)

end Local
