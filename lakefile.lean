import Lake

open Lake DSL

package «critical2dkpz» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0-rc2"

private def projectLeanOptions : Array LeanOption := #[
  ⟨`autoImplicit, false⟩,
  ⟨`relaxedAutoImplicit, false⟩,
  ⟨`linter.unusedVariables, true⟩,
  ⟨`linter.unusedSectionVars, true⟩,
  ⟨`linter.unusedSimpArgs, true⟩,
  ⟨`linter.unnecessarySimpa, true⟩,
  ⟨`linter.deprecated, true⟩
]

/-- Formalization of *The Critical 2D KPZ Process* (arXiv:2610.31614), with the Gaussian, random-walk, renewal, polymer and stochastic heat-flow results used in its proofs. -/
@[default_target]
lean_lib «Critical2DKPZ» where
  globs := #[.andSubmodules `Critical2DKPZ]
  leanOptions := projectLeanOptions

/-- The 22 theorem statements listed in docs/main-results.md, one per module. -/
lean_lib «Critical2DKPZStatements» where
  globs := #[.submodules `Critical2DKPZStatements]
  leanOptions := projectLeanOptions

/-- Independent statement comparison for Theorem 1.2, with a proof supplied by the library. -/
lean_lib «Critical2DKPZAudit» where
  globs := #[.submodules `Critical2DKPZAudit]
  leanOptions := projectLeanOptions
