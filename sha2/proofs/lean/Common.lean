import Common.U8
import Common.U64

/-!
# Common — word-size-agnostic helpers

Helpers shared between the SHA-256 and (future) SHA-512 refinement
proofs: byte/slice plumbing (`Common.U8`) and the 64-bit scalar
bridge used by the padding length tag (`Common.U64`). Word-size-
specific helpers tied to SHA-256's 32-bit state stay in `U32.lean`.
-/
