/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.HeatEnergy
public import Critical2DKPZ.Analysis.Sobolev.GammaMixture

/-! At positive Sobolev order, the localized negative Sobolev energy of a locally integrable function is a Gamma mixture of spatial heat quadratic forms. -/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ

open Analysis.Sobolev

/-- Heat-damped Fourier energy of a function is its spatial heat quadratic form. -/
theorem heatDampedFourierEnergy_ofFun {u : ℝ} (hu : 0 < u) {f : Plane → ℝ}
    (hf : LocallyIntegrable f volume) (χ : TestFn) :
    heatDampedFourierEnergy u (Distribution.ofFun (⊤ : TopologicalSpace.Opens Plane) f volume ⊤) χ =
      ENNReal.ofReal (∫ y : Plane, (χ y * f y) *
        ∫ x : Plane, heatKernel (2 * u) (y - x) * (χ x * f x)) := by
  have hi : Integrable (fun x => χ x * f x) := by
    simpa only [smul_eq_mul] using hf.integrable_smul_left_of_hasCompactSupport
      χ.continuous χ.hasCompactSupport
  unfold heatDampedFourierEnergy
  simp_rw [localizedFourier_ofFun hf,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gaussian_fourier_energy hu hi)
    (Filter.Eventually.of_forall fun ξ => mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)),
    ← ENNReal.ofReal_mul (sq_nonneg _), integral_gaussian_fourier_energy hu hi]


end Critical2DKPZ

end
