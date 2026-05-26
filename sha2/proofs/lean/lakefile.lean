import Lake
open Lake DSL

-- Aeneas backend (Lean library). Pinned to the immutable `sha2-fv-pin`
-- tag on our fork (commit 3212a5fe) so the Lean library stays locked to
-- the same Aeneas revision as the binary in flake.nix. The fork carries
-- upstream-candidate lemmas from earlier staging in
-- `proof/lean/AeneasUpstream.lean` (now merged upstream via per-feature
-- PRs).
require aeneas from git
  "https://github.com/remix7531/aeneas.git" @ "sha2-fv-pin" / "backends" / "lean"

-- FIPS 180-4 spec + impl + Impl↔spec equivalence lives in the sibling
-- repo `fips-180-4-lean`. We bridge the Aeneas extraction to its `Impl`
-- layer, and then chain through that project's `compress_correct` /
-- `sha256_correct` for spec-layer refinement.
require «fips-pub-180-4» from git
  "https://github.com/remix7531/fips-180-4-lean.git" @ "main"

package «sha2-proofs» {}

-- Single library covering:
--
--   * Extraction.lean + Extraction/Funs.lean + Extraction/Types.lean
--     + Extraction/FunsExternal.lean — Aeneas-generated extraction
--     (regenerated on each extraction; not hand-edited)
--   * top-level proof modules (U32, ToU32s, Compress, RoundStep, Loop0,
--     Loop1, FinalBlock, SetChain, Sha256, Spec, AxiomCheck) —
--     hand-written refinement proof
--
-- `srcDir := "."` makes Lake resolve module names relative to this lakefile.
@[default_target]
lean_lib Sha2 where
  srcDir := "."
  globs := #[
    .andSubmodules `Extraction,
    .andSubmodules `Common,
    .one `U32, .one `U64,
    .one `ToU32s, .one `ToU64s,
    .one `SetChain, .one `RoundStep,
    .one `Compress, .one `Loop0, .one `Loop1, .one `FinalBlock,
    .one `Sha2Inner, .one `Sha2InnerSpec,
    .one `Sha256, .one `Sha224,
    .one `Sha512, .one `Sha384, .one `Sha512_256, .one `Sha512_224,
    .one `Spec, .one `AxiomCheck
    -- SHA-512 family proof modules (RoundStep512, Compress512, Loop0_512,
    -- Loop1_512, FinalBlock512, SetChain512, Sha2Inner512, Sha2InnerSpec512)
    -- will be re-added once the per-round bridge and compress refinement
    -- are in place. The top-level `Sha{384,512,512_224,512_256}_spec`
    -- statements are kept as `sorry` so the spec-layer corollaries in
    -- `Spec.lean` still type-check.
  ]
