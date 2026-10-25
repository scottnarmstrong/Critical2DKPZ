/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordPotentialDomination
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitFromFirstLetterConvergence
import Critical2DKPZ.SHF.Moments.TerminalWordLimitFromCutoffEstimates
import Critical2DKPZ.SHF.Moments.TerminalWordFirstLetterLimit
import Critical2DKPZ.SHF.Moments.TerminalWordLimitSpatialExhaustion
import Critical2DKPZ.SHF.Moments.TerminalWordLimitTimeBoundary
import Critical2DKPZ.SHF.Moments.TerminalWordLimitContinuumAction

/-! # Moving-start terminal limits under potential domination

Potential domination implies terminal-test convergence for fixed collision words satisfying the stated parity and initial-pair separation conditions. -/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped BigOperators CompactlySupported Topology ENNReal
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- Potential domination yields the moving-start terminal limit for a fixed collision word with the stated parity and initial-pair separation. -/
theorem tendsto_wordTerminalTest_of_potentialDomination (ϑ : ℝ) {h : ℕ}
    (hD : WordPotentialDomination ϑ h) (w : List (CollisionPair h)) (hw : w.IsChain (· ≠ ·))
    {τ : ℝ} (hτ : 0 < τ) (nN : ℕ → ℕ)
    (hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ))
    (xN : ℕ → Fin h → Site) (x : Configuration h)
    (hx : ∀ i, Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (x i)))
    (hphase : ∀ i, ∀ᶠ N : ℕ in atTop, Even (xN N i 0 + xN N i 1 + (nN N : ℤ)))
    (hsep : ∀ α ∈ w.head?, x α.1.1 ≠ x α.1.2)
    (ψ : Fin h → C_c(Plane, ℝ)) :
    Tendsto (fun N => wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) w (nN N) (xN N)
      (fun y => ∏ i, ψ i (y i))) atTop
      (𝓝 (∫ y : Configuration h, (∏ i, ψ i (y i)) *
        (diagramKernel (ϑ - Real.eulerMascheroniConstant) w τ x y).toReal)) :=
  tendsto_wordTerminalTest_of_potentialDomination_of_inputs
    wordFirstLetter_time_boundary_small_of_potentialDomination
    wordFirstLetter_spatial_cutoff_small_of_potentialDomination
    integrable_integral_diagramKernel_cons_tensor_action
    tendsto_wordTerminalTest_cons_of_cutoff_inputs ϑ hD w hw hτ nN hn xN x hx hphase hsep ψ

end Critical2DKPZ.SHF.Moments
