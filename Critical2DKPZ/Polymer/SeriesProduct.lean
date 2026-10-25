/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.Series
public import Critical2DKPZ.Polymer.Orthogonality
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic

/-! Two series whose L² norms are summable admit termwise integration of their product. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Critical2DKPZ.Polymer

/-- If two countable families have summable L² norms, the double series of L¹ norms of their pairwise products is finite. -/
theorem product_series_norms_ne_top {ι κ : Type*} [Countable ι] [Countable κ]
    (f : ι → Disorder → ℝ) (g : κ → Disorder → ℝ)
    (hf : ∀ i, MemLp (f i) 2 disorderLaw) (hg : ∀ j, MemLp (g j) 2 disorderLaw)
    (hsf : ∑' i, eLpNorm (f i) 2 disorderLaw ≠ ∞)
    (hsg : ∑' j, eLpNorm (g j) 2 disorderLaw ≠ ∞) :
    (∑' ij : ι × κ, eLpNorm (fun ω => f ij.1 ω * g ij.2 ω) 1 disorderLaw) ≠ ∞ := by
  apply ne_top_of_le_ne_top (ENNReal.mul_ne_top hsf hsg)
  calc
    _ ≤ ∑' ij : ι × κ, eLpNorm (f ij.1) 2 disorderLaw * eLpNorm (g ij.2) 2 disorderLaw := by
      apply ENNReal.tsum_le_tsum
      intro ij
      exact eLpNorm_smul_le_mul_eLpNorm
        (hf ij.1).aestronglyMeasurable (hg ij.2).aestronglyMeasurable
    _ = _ := by
      rw [ENNReal.tsum_prod' (f := fun ij : ι × κ =>
        eLpNorm (f ij.1) 2 disorderLaw * eLpNorm (g ij.2) 2 disorderLaw)]
      simp_rw [ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_mul_right]

/-- For two countable families with summable L² norms, the integral of the product of their pointwise sums equals the sum of the pairwise integrals. -/
theorem integral_mul_series {ι κ : Type*} [Countable ι] [Countable κ]
    (f : ι → Disorder → ℝ) (g : κ → Disorder → ℝ)
    (hf : ∀ i, MemLp (f i) 2 disorderLaw) (hg : ∀ j, MemLp (g j) 2 disorderLaw)
    (hsf : ∑' i, eLpNorm (f i) 2 disorderLaw ≠ ∞)
    (hsg : ∑' j, eLpNorm (g j) 2 disorderLaw ≠ ∞) :
    (∫ ω, (∑' i, f i ω) * (∑' j, g j ω) ∂disorderLaw) =
      ∑' ij : ι × κ, ∫ ω, f ij.1 ω * g ij.2 ω ∂disorderLaw := by
  let H (ij : ι × κ) (ω : Disorder) := f ij.1 ω * g ij.2 ω
  have hH (ij : ι × κ) : Integrable (H ij) disorderLaw :=
    memLp_one_iff_integrable.mp ((hf ij.1).fun_mul (hg ij.2))
  have hs := product_series_norms_ne_top f g hf hg hsf hsg
  have hnorms : Summable (fun ij : ι × κ => ∫ ω, ‖H ij ω‖ ∂disorderLaw) := by
    have h := ENNReal.summable_toReal hs
    have heq (ij : ι × κ) :
        ∫ ω, ‖H ij ω‖ ∂disorderLaw =
          (eLpNorm (H ij) 1 disorderLaw).toReal := by
      rw [integral_norm_eq_lintegral_enorm (hH ij).aestronglyMeasurable,
        eLpNorm_one_eq_lintegral_enorm (hH ij).aestronglyMeasurable]
    simpa only [heq, H] using h
  have haef := summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1 : ℝ≥0∞) ≤ 2) hsf
  have haeg := summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1 : ℝ≥0∞) ≤ 2) hsg
  have heq : (fun ω => (∑' i, f i ω) * (∑' j, g j ω)) =ᵐ[disorderLaw]
      fun ω => ∑' ij : ι × κ, H ij ω := by
    filter_upwards [haef, haeg] with ω hωf hωg
    exact tsum_mul_tsum_of_summable_norm hωf hωg
  rw [integral_congr_ae heq]
  have hh := hasSum_integral_of_summable_integral_norm hH hnorms
  exact hh.tsum_eq.symm

end Critical2DKPZ.Polymer
