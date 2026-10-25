/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.GaussianConvexity.CumulantConvexity
public import Critical2DKPZ.NonGaussian.EhrhardNormalization
public import Critical2DKPZ.Analysis.Heat.Semigroup
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-! # Exponential normalization and heat-test scaling -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.Errata

/-- A nonconstant exponentially normalized Gaussian violates the stated endpoint mean bound at order one under total real division. -/
theorem lx26_order_one_mean_bound_counterexample :
    let μ := gaussianReal (-(1 / 2 : ℝ)) 1
    IsEhrhardType μ ∧ Integrable id μ ∧ Integrable (fun x : ℝ => Real.exp x) μ ∧
      (∫ x : ℝ, Real.exp x ∂μ) = 1 ∧
      ¬ -(Real.log (∫ x : ℝ, Real.exp x ∂μ)) / ((1 : ℝ) * (1 - 1)) ≤
        ∫ x : ℝ, x ∂μ := by
  dsimp only
  have hi : Integrable (fun x : ℝ => Real.exp x)
      (gaussianReal (-(1 / 2 : ℝ)) 1) := by
    simpa using (integrable_exp_mul_gaussianReal
      (μ := -(1 / 2 : ℝ)) (v := 1) 1)
  have hm : (∫ x : ℝ, Real.exp x ∂gaussianReal (-(1 / 2 : ℝ)) 1) = 1 := by
    have h := congrFun (mgf_id_gaussianReal (μ := -(1 / 2 : ℝ)) (v := 1)) 1
    simpa [mgf] using h
  have hE : IsEhrhardType (gaussianReal (-(1 / 2 : ℝ)) 1) := by
    have h := NonGaussian.isEhrhardType_map_add_const
      EhrhardType.isEhrhardType_standardGaussian (-(1 / 2 : ℝ))
    simpa only [gaussianReal_map_add_const, zero_add] using h
  refine ⟨hE, IsGaussian.integrable_id, hi, hm, ?_⟩
  simp

/-- Rescaling planar space by `sqrt t` changes heat variance from `ε` to `ε/t` with the planar Jacobian factor. -/
theorem lx26_heat_test_rescale {t : ℝ} (ht : 0 < t) (ε : ℝ) (x : Plane) :
    heatKernel ε (Real.sqrt t • x) = t⁻¹ * heatKernel (ε / t) x := by
  have hm : t * (ε / t) = ε := by field_simp
  have h := heatKernel_scaling (a := Real.sqrt t) (u := ε / t)
    (Real.sqrt_pos.mpr ht) x
  simpa only [Real.sq_sqrt ht.le, hm] using h

end Critical2DKPZ.Errata

end
