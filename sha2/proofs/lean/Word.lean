import Word.U32
import Word.U64
import Word.ToU32s
import Word.ToU64s

/-!
# Word — width-specific helpers (SHA-256 at U32, SHA-512 at U64)

Word-size-specific helpers used by the SHA-2 refinement proofs:

* `Word.U32`     — Aeneas `Std.U32` ↔ Lean `UInt32` bridge plus the 10
                   SHA-256 literal rotation bridges
                   (`rotr_bridge_{2,6,7,11,13,17,18,19,22,25}`),
                   `arrayU32ToVec` view-level lemmas, the BE 4-byte decode
                   bridge, and the SHA-256 `K32` / `H256_256` constant
                   table equivalences.
* `Word.U64`     — Aeneas `Std.U64` ↔ Lean `UInt64` bridge plus the 10
                   SHA-512 literal rotation bridges
                   (`rotr64_bridge_{1,8,14,18,19,28,34,39,41,61}`),
                   `arrayU64ToVec` view-level lemmas, the BE 8-byte decode
                   bridge, and the SHA-512 `K64` / `H0_512*` IV
                   constant table equivalences.
* `Word.ToU32s` — refinement of the Aeneas `to_u32s` schedule-fill
                   closure against `Impl.toU32sFromBytes`.
* `Word.ToU64s` — 64-bit analogue: `to_u64s` ↔ `Impl.toU64sFromBytes`.

Width-agnostic helpers (used by both SHA-256 and SHA-512) live in
`Common/`.
-/
