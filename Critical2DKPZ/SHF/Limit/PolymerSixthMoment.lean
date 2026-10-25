/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Limit.SixthMoment
public import Critical2DKPZ.MomentBounds.CCR25MomentBoundSix

/-! # Uniform sixth moments of flat polymer pairings -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators CompactlySupported

namespace Critical2DKPZ.SHF.Limit

/-- The sixth moments of compact flat pairings are eventually uniformly bounded on bounded time windows with interval lengths bounded away from zero. Integrability is supplied by `integrable_flat_polymerMeasure_pow`. -/
theorem polymerMeasure_flat_sixth_moment_le (ϑ : ℝ) (χ : C_c(Plane, ℝ))
    {τ T : ℝ} (hτ : 0 < τ) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, ∀ s t : ℝ, 0 ≤ s → τ ≤ t - s → t ≤ T →
      ∫ ω, (∫ x, |χ x| ∂((polymerMeasure ϑ N s t ω).map Prod.fst)) ^ 6
        ∂disorderLaw ≤ C := by
  exact polymerMeasure_flat_sixth_moment_le_of_ccr
    MomentBounds.ccrMomentBound_six ϑ χ hτ

end Critical2DKPZ.SHF.Limit

end
