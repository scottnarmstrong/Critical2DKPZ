/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordPotentialDomination
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitFromFirstLetterConvergence
import Critical2DKPZ.MomentBounds.CCR25GaussianMoments
import Mathlib.Tactic

/-! # Terminal-profile bounds from the shared word potential domination -/

@[expose] public noncomputable section

open Filter
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- Potential domination bounds signed terminal tests uniformly over starting configurations, microscopic horizons below `T * N` and tests with a fixed supremum bound, at sufficiently large lattice scales. -/
theorem eventually_abs_wordTerminalTest_le_potential
    (ϑ : ℝ) {h : ℕ} (hD : WordPotentialDomination ϑ h)
    {T : ℝ} (hT : 0 < T) (α : CollisionPair h) (w : List (CollisionPair h))
    (hw : (α :: w).IsChain (· ≠ ·)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, (n : ℝ) ≤ T * N →
      ∀ (x : Fin h → Site) (Ψ : Configuration h → ℝ) (M : ℝ), 0 ≤ M →
      (∀ y, |Ψ y| ≤ M) →
      |wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) (α :: w) n x Ψ| ≤
        M * C * Real.sqrt (N : ℝ) * wordGapPotential n (x α.1.2 - x α.1.1) := by
  obtain ⟨C, hC, hbound⟩ := hD hT α w hw
  refine ⟨C, hC, hbound.mono fun N hN n hn x Ψ M hM hΨ => ?_⟩
  calc
    _ ≤ M * wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) (α :: w) n x (fun _ => 1) :=
      abs_wordTerminalTest_le_mass N (sigmaSq_nonneg _) (α :: w) n x Ψ hΨ
    _ ≤ M * (C * Real.sqrt (N : ℝ) * wordGapPotential n (x α.1.2 - x α.1.1)) :=
      mul_le_mul_of_nonneg_left (hN n hn x) hM
    _ = _ := by ring


end Critical2DKPZ.SHF.Moments
