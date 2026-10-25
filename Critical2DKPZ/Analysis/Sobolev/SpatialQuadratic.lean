/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.HeatRepresentation
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The spatial heat quadratic form

This product-measure formulation is convenient for averaging a random field. Its value is
nonnegative even when the field changes sign, by the proved Fourier representation.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Critical2DKPZ

/-- Spatial quadratic form of the positive heat semigroup at time `2u`. -/
def spatialHeatQuadratic (u : ℝ) (f : Plane → ℝ) : ℝ :=
  ∫ p : Plane × Plane, heatKernel (2 * u) (p.1 - p.2) * (f p.1 * f p.2)
    ∂volume.prod volume

/-- The heat-kernel quadratic integrand of an integrable function is integrable at positive time. -/
theorem integrable_spatialHeatQuadratic {u : ℝ} (hu : 0 < u) {f : Plane → ℝ}
    (hf : Integrable f) :
    Integrable (fun p : Plane × Plane => heatKernel (2 * u) (p.1 - p.2) * (f p.1 * f p.2))
      (volume.prod volume) := by
  apply (hf.mul_prod hf).bdd_mul (c := (2 * Real.pi * (2 * u))⁻¹)
    (((continuous_heatKernel (2 * u)).comp
      (continuous_fst.sub continuous_snd)).aestronglyMeasurable)
  filter_upwards [] with p
  change ‖heatKernel (2 * u) (p.1 - p.2)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg (mul_nonneg (by norm_num) hu.le) _)]
  exact heatKernel_le_at_zero (u := 2 * u) (mul_nonneg (by norm_num) hu.le) _

/-- The spatial heat quadratic form equals the corresponding iterated convolution integral. -/
theorem spatialHeatQuadratic_eq_iterated {u : ℝ} (hu : 0 < u) {f : Plane → ℝ}
    (hf : Integrable f) :
    spatialHeatQuadratic u f =
      ∫ y : Plane, f y * ∫ x : Plane, heatKernel (2 * u) (y - x) * f x := by
  rw [spatialHeatQuadratic, integral_prod _ (integrable_spatialHeatQuadratic hu hf)]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

/-- The spatial heat quadratic form of an integrable real function is nonnegative. -/
theorem spatialHeatQuadratic_nonneg {u : ℝ} (hu : 0 < u) {f : Plane → ℝ}
    (hf : Integrable f) : 0 ≤ spatialHeatQuadratic u f := by
  rw [spatialHeatQuadratic_eq_iterated hu hf, ← integral_gaussian_fourier_energy hu hf]
  exact mul_nonneg (sq_nonneg _) (integral_nonneg fun ξ =>
    mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))

/-- The spatial heat quadratic form gives the fixed-time local Sobolev heat representation. -/
theorem heatDampedFourierEnergy_ofFun_eq_spatialHeatQuadratic {u : ℝ} (hu : 0 < u)
    {f : Plane → ℝ} (hf : LocallyIntegrable f volume) (χ : TestFn) :
    heatDampedFourierEnergy u (Distribution.ofFun (⊤ : TopologicalSpace.Opens Plane) f volume ⊤) χ =
      ENNReal.ofReal (spatialHeatQuadratic u (fun x => χ x * f x)) := by
  have hi : Integrable (fun x => χ x * f x) := by
    simpa only [smul_eq_mul] using hf.integrable_smul_left_of_hasCompactSupport
      χ.continuous χ.hasCompactSupport
  rw [heatDampedFourierEnergy_ofFun hu hf, spatialHeatQuadratic_eq_iterated hu hi]

end Critical2DKPZ

end
