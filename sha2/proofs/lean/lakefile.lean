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
    .andSubmodules `Word,
    .andSubmodules `Sha256,
    .andSubmodules `Sha512,
    .one `Spec, .one `AxiomCheck
  ]
