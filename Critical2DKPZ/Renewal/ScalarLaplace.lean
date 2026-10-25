/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.ScalarDensity
import Critical2DKPZ.SHF.DeltaBose.Measurability
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Laplace transform of the scalar renewal density

The positive Gamma integral from delta-Bose moment kernels has the exact Laplace transform
`∫ exp(-bt) j_θ(t) dt = 1 / (log b - θ)` for `log b > θ`. This fixes the
continuum normalization for the critical renewal limit, including its Euler shift.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Critical2DKPZ.Renewal

/-- The positive two-variable integrand in the Laplace transform of the scalar density. -/
def scalarLaplaceJoint (θ b : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-(b * p.2)) * DeltaBose.scalarIntegrand θ p.2 p.1

/-- The joint scalar Laplace integrand is measurable. -/
theorem measurable_scalarLaplaceJoint (θ b : ℝ) : Measurable (scalarLaplaceJoint θ b) := by
  have hp : Measurable (fun p : ℝ × ℝ => ((θ, p.2), p.1)) := by fun_prop
  exact (by fun_prop : Measurable (fun p : ℝ × ℝ => Real.exp (-(b * p.2)))).mul
    (DeltaBose.measurable_scalarIntegrand.comp hp)

/-- The joint scalar Laplace integrand is strictly positive. -/
theorem scalarLaplaceJoint_pos (θ b : ℝ) {u t : ℝ} (hu : 0 < u) (ht : 0 < t) :
    0 < scalarLaplaceJoint θ b (u, t) :=
  mul_pos (Real.exp_pos _) (div_pos
    (mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)) (Real.Gamma_pos_of_pos hu))

/-- Each positive shape gives an integrable Gamma density in the time variable. -/
theorem integrableOn_scalarLaplaceJoint_time (θ : ℝ) {b u : ℝ} (hb : 0 < b) (hu : 0 < u) :
    IntegrableOn (fun t => scalarLaplaceJoint θ b (u, t)) (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ => t ^ (u - 1) * Real.exp (-(b * t))) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := u - 1) (by linarith)
        (by norm_num) hb)
  exact (hi.const_mul (Real.exp (θ * u) / Real.Gamma u)).congr
    (Filter.Eventually.of_forall fun t => by
      unfold scalarLaplaceJoint DeltaBose.scalarIntegrand
      ring)

/-- The inner Gamma integral gives a pure exponential in the shape parameter. -/
theorem integral_scalarLaplaceJoint_time (θ : ℝ) {b u : ℝ} (hb : 0 < b) (hu : 0 < u) :
    (∫ t in Ioi 0, scalarLaplaceJoint θ b (u, t)) = Real.exp ((θ - Real.log b) * u) := by
  calc
    _ = Real.exp (θ * u) / Real.Gamma u *
        ∫ t in Ioi 0, t ^ (u - 1) * Real.exp (-(b * t)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        unfold scalarLaplaceJoint DeltaBose.scalarIntegrand
        ring
    _ = Real.exp (θ * u) / Real.Gamma u * ((1 / b) ^ u * Real.Gamma u) := by
      rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hu hb]
    _ = Real.exp (θ * u) * Real.exp (-(Real.log b * u)) := by
      rw [Real.rpow_def_of_pos (one_div_pos.mpr hb), one_div, Real.log_inv, neg_mul]
      field_simp [(Real.Gamma_pos_of_pos hu).ne']
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- The double Gamma-Laplace integral is absolutely integrable in its natural domain. -/
theorem integrable_scalarLaplaceJoint (θ : ℝ) {b : ℝ} (hb : 0 < b) (hθ : θ < Real.log b) :
    Integrable (scalarLaplaceJoint θ b)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  apply (integrable_prod_iff (measurable_scalarLaplaceJoint θ b).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact integrableOn_scalarLaplaceJoint_time θ hb hu
  · apply (integrableOn_exp_mul_Ioi (sub_neg.mpr hθ) 0).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hn : (∫ t in Ioi 0, ‖scalarLaplaceJoint θ b (u, t)‖) =
        ∫ t in Ioi 0, scalarLaplaceJoint θ b (u, t) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact Real.norm_of_nonneg (scalarLaplaceJoint_pos θ b hu ht).le
    rw [hn, integral_scalarLaplaceJoint_time θ hb hu]

/-- Integrating in the shape parameter recovers the scalar density under exponential damping. -/
theorem integral_scalarLaplaceJoint_shape (θ b t : ℝ) :
    (∫ u in Ioi 0, scalarLaplaceJoint θ b (u, t)) =
      Real.exp (-(b * t)) * DeltaBose.scalarDensity θ t := by
  simpa only [scalarLaplaceJoint, DeltaBose.scalarDensity] using!
    (integral_const_mul (Real.exp (-(b * t))) (DeltaBose.scalarIntegrand θ t)
      (μ := volume.restrict (Ioi 0)))

/-- The exponentially damped scalar renewal density is integrable on positive times. -/
theorem integrableOn_damped_scalarDensity (θ : ℝ) {b : ℝ} (hb : 0 < b) (hθ : θ < Real.log b) :
    IntegrableOn (fun t => Real.exp (-(b * t)) * DeltaBose.scalarDensity θ t) (Ioi 0) :=
  (integrable_scalarLaplaceJoint θ hb hθ).integral_prod_right.congr
    (Filter.Eventually.of_forall (integral_scalarLaplaceJoint_shape θ b))

/-- Exact Laplace transform of the continuum scalar renewal density. -/
theorem integral_damped_scalarDensity (θ : ℝ) {b : ℝ} (hb : 0 < b) (hθ : θ < Real.log b) :
    (∫ t in Ioi 0, Real.exp (-(b * t)) * DeltaBose.scalarDensity θ t) =
      1 / (Real.log b - θ) := by
  calc
    _ = ∫ t in Ioi 0, ∫ u in Ioi 0, scalarLaplaceJoint θ b (u, t) := by
      simp only [integral_scalarLaplaceJoint_shape]
    _ = ∫ u in Ioi 0, ∫ t in Ioi 0, scalarLaplaceJoint θ b (u, t) :=
      (integral_integral_swap (f := fun u t => scalarLaplaceJoint θ b (u, t))
        (by simpa only [Function.uncurry] using! integrable_scalarLaplaceJoint θ hb hθ)).symm
    _ = ∫ u in Ioi 0, Real.exp ((θ - Real.log b) * u) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact integral_scalarLaplaceJoint_time θ hb hu
    _ = _ := by
      rw [integral_exp_mul_Ioi (sub_neg.mpr hθ) 0]
      simp only [mul_zero, Real.exp_zero]
      rw [neg_div, ← div_neg, neg_sub]

end Critical2DKPZ.Renewal

end
