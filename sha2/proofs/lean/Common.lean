import Common.U8
import Common.U64
import Common.Vec
import Common.Wp
import Common.Truncate
import Common.Digest

/-!
# Common — word-size-agnostic helpers

Helpers shared between the SHA-256 and SHA-512 refinement proofs:

* `Common.U8`  — byte/slice plumbing (`toUInt8`, `arrayU8ToVec`,
                 `sliceToByteArray`, `arrayU8ToVec_eq_chunk_view`)
* `Common.U64` — 64-bit scalar bridge (`toUInt64`, `fromUInt64`) plus
                 `toUInt8_be_byte`, the BE-byte extraction lemma used by
                 both SHA-256's length-tag emit and SHA-512's digest emit
* `Common.Vec` — `Vector` bridge lemmas (`vector_set_eq_set!`,
                 `vector_getElem!_eq_getElem`) plus
                 `vector_ofFn_take_of_agree` (used by the four
                 truncated-digest family bridges)
* `Common.Wp`  — weakest-precondition utilities (`ok_of_spec`)
* `Common.Truncate` — generic 28/32/48-byte truncation chain plus
                 `inner_truncate_digest_spec`, the one-shot wrapper
                 used by SHA-224 / SHA-384 / SHA-512/256 / SHA-512/224
* `Common.Digest` — `bytesToBits` primitive + length / `digestBitVec...`
                 bridges to the upstream per-namespace and per-width forms

Word-size-specific helpers live in `Word.U32` (SHA-256 / SHA-224) and
`Word.U64` (SHA-512 / SHA-384 / SHA-512-256 / SHA-512-224).
-/
