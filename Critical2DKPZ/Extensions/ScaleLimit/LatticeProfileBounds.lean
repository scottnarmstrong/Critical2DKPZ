/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.FutureProfiles.ProfileEstimates
public import Critical2DKPZ.Definitions.CriticalBeta
public import Critical2DKPZ.Definitions.BlockTime
public import Critical2DKPZ.Definitions.SmoothedP2Plane
import Critical2DKPZ.Provider.BlockMoments
import Critical2DKPZ.Blocks.OpenDiscrepancyStringBounds
import Critical2DKPZ.OnePoint.BlockRatioOriginalLawEstimates
import Critical2DKPZ.LogNormality.LatticeInputs

/-! # Closed uniform lattice profile and remaining-interval bounds

The profile estimates quantify over arbitrary initial and terminal block
indices after the constants have been chosen. Their energy estimate therefore
applies with initial index `K-n+1` and terminal index `K-ℓ`, uniformly in `n`.
The remaining-interval tail theorem uses the smoothed endpoint profile and
its exact Chapman–Kolmogorov identity, not an origin-start profile.
-/

@[expose] public section

open MeasureTheory Filter

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The full uniform lattice profile estimates with all external inputs proved. -/
theorem lattice_profile_estimates : FutureProfiles.ProfileEstimatesBound := by
  have hC6 : OnePoint.BlockMomentsBound := Provider.blockMoments
  have hOpen : FutureProfiles.OpenStringBound := Blocks.openDiscrepancyMass_sq_integral_le
  have hRatio : FutureProfiles.RatioBoundP :=
    OnePoint.blockGoodSet_compl_and_ratio_bound_of hC6
  exact FutureProfiles.profile_estimates_of hOpen hRatio

/-- Uniform two-sided logarithmic tails for the remaining lattice interval. -/
theorem lattice_lastInterval_log_tail (A : ℝ) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ₁ : ℝ, ∃ (C : ℝ) (ℓ₀ : ℕ),
      ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop,
        ∀ ϑ ∈ Set.Icc (-A) A, ∀ a ℓ : ℕ, ℓ₀ ≤ ℓ →
          a + ℓ + 1 ≤ blockCount N ρ → ∀ r : ℝ, 0 ≤ r →
            (disorderLaw {ω | Real.log
                (smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ a) N 0 ω /
                  smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ a)
                    (blockTime N ρ (blockCount N ρ - ℓ)) 0 ω) < -r}).toReal ≤
              C / ℓ + C * ℓ * Real.exp (-r) ∧
            (disorderLaw {ω | r < Real.log
                (smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ a) N 0 ω /
                  smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ a)
                    (blockTime N ρ (blockCount N ρ - ℓ)) 0 ω)}).toReal ≤ Real.exp (-r) :=
  LogNormality.lastInterval_log_tail_of lattice_profile_estimates A

end Critical2DKPZ.Extensions.ScaleLimit
