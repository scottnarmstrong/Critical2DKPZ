/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.BlockRatioOriginalLawMomentBounds
public import Critical2DKPZ.OnePoint.BlockRatioPairEstimate
import Mathlib.Tactic

/-! # Block-ratio bounds under the disorder law -/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators

namespace Critical2DKPZ.OnePoint

open Critical2DKPZ.Blocks

/-- The original-law good-set ratio estimate from the pair bound and block moments. -/
theorem blockGoodSet_compl_and_ratio_bound_of (hC6 : BlockMomentsBound) (A : ℝ) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ₁ : ℝ, ∃ C : ℝ,
      ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop,
        ∀ ϑ ∈ Set.Icc (-A) A, ∀ r s : ℕ, 1 ≤ r → r ≤ s →
          s + 1 ≤ blockCount N ρ →
            (disorderLaw (blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s)ᶜ).toReal ≤
              C / ((blockCount N ρ : ℝ) - s) ∧
            ∫ ω in blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s,
                (blockRatio (criticalBeta ϑ N) (blockTime N ρ) r s ω - 1) ^ 2
                  ∂disorderLaw ≤ C / ((blockCount N ρ : ℝ) - s) := by
  exact blockGoodSet_compl_and_ratio_bound_pair_of hC6 A
    (abs_setIntegral_familyTerm_mul_le A)

end Critical2DKPZ.OnePoint

end
