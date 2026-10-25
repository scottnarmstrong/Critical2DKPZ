/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.GammaBounds
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! The Gamma-integral collision density in Tsai’s equation (2.4) and Gu–Quastel–Tsai’s Lemma 8.4 is positive and jointly continuous at positive times and satisfies an exact scaling identity. -/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace Critical2DKPZ.DeltaBose

/-- The Laplace variable form of the scalar collision integrand. -/
noncomputable def gammaLaplaceIntegrand (s u : ℝ) : ℝ := Real.exp (s * u) / Real.Gamma u

/-- Nonnegativity on the integration domain. -/
theorem gammaLaplaceIntegrand_pos (s : ℝ) {u : ℝ} (hu : 0 < u) :
    0 < gammaLaplaceIntegrand s u :=
  div_pos (Real.exp_pos _) (Real.Gamma_pos_of_pos hu)

/-- The Gamma-Laplace integrand has an integrable majorant uniform over every half-line of parameters bounded above. -/
theorem gammaLaplaceIntegrand_le {s B r u : ℝ} (hs : s ≤ B) (hu : 0 < u) :
    gammaLaplaceIntegrand s u ≤
      Real.exp (Real.exp (B + r) + 1) * (u * Real.exp (-(r * u))) := by
  have h := inv_gamma_le_exp_mul hu (Real.exp_pos (B + r))
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp] at h
  unfold gammaLaplaceIntegrand
  rw [div_eq_mul_inv]
  calc Real.exp (s * u) * (Real.Gamma u)⁻¹
      ≤ Real.exp (s * u) * (Real.exp (Real.exp (B + r) + 1) * u *
          Real.exp ((B + r) * -u)) :=
        mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
    _ = Real.exp (Real.exp (B + r) + 1) * u *
          Real.exp ((s - B - r) * u) := by
      have he : Real.exp ((s - B - r) * u) =
          Real.exp (s * u) * Real.exp ((B + r) * -u) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he]
      ring
    _ ≤ Real.exp (Real.exp (B + r) + 1) * u * Real.exp (-(r * u)) := by
      apply mul_le_mul_of_nonneg_left
      · apply Real.exp_le_exp.mpr
        nlinarith only [mul_nonneg (sub_nonneg.mpr hs) hu.le]
      · positivity
    _ = _ := mul_assoc _ _ _

/-- Absolute convergence of the scalar Gamma integral in Laplace variables. -/
theorem integrableOn_gammaLaplaceIntegrand (s : ℝ) :
    IntegrableOn (gammaLaplaceIntegrand s) (Ioi 0) := by
  apply ((integrableOn_mul_exp_neg (r := 1) zero_lt_one).const_mul
    (Real.exp (Real.exp (s + 1) + 1))).mono'
  · apply ContinuousOn.aestronglyMeasurable
    · apply ContinuousOn.div
      · fun_prop
      · exact Real.differentiableOn_Gamma_Ioi.continuousOn
      · intro u hu
        exact (Real.Gamma_pos_of_pos hu).ne'
    · exact measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_pos (gammaLaplaceIntegrand_pos s hu)]
    exact gammaLaplaceIntegrand_le le_rfl hu

/-- The Gamma-Laplace transform is continuous on its entire parameter line. -/
theorem continuous_gammaLaplaceIntegral :
    Continuous (fun s : ℝ => ∫ u in Ioi 0, gammaLaplaceIntegrand s u) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  apply continuousAt_of_dominated
    (bound := fun u : ℝ => Real.exp (Real.exp (s + 2) + 1) * (u * Real.exp (-u)))
  · exact Filter.Eventually.of_forall fun x => (integrableOn_gammaLaplaceIntegrand x).aestronglyMeasurable
  · filter_upwards [gt_mem_nhds (show s < s + 1 by linarith)] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_pos (gammaLaplaceIntegrand_pos x hu)]
    simpa only [add_assoc, one_add_one_eq_two, one_mul] using
      (gammaLaplaceIntegrand_le (r := 1) hx.le hu)
  · simpa only [one_mul] using
      (integrableOn_mul_exp_neg (r := 1) zero_lt_one).const_mul
        (Real.exp (Real.exp (s + 2) + 1))
  · filter_upwards with u
    unfold gammaLaplaceIntegrand
    fun_prop

/-- The scalar collision integrand in positive-time variables. -/
noncomputable def scalarIntegrand (θ t u : ℝ) : ℝ :=
  t ^ (u - 1) * Real.exp (θ * u) / Real.Gamma u

/-- Factoring out the time identifies the natural Laplace parameter. -/
theorem scalarIntegrand_eq {t : ℝ} (ht : 0 < t) (θ u : ℝ) :
    scalarIntegrand θ t u = t⁻¹ * gammaLaplaceIntegrand (θ + Real.log t) u := by
  unfold scalarIntegrand gammaLaplaceIntegrand
  rw [Real.rpow_sub ht, Real.rpow_one, div_eq_mul_inv]
  rw [Real.rpow_def_of_pos ht]
  rw [show (θ + Real.log t) * u = Real.log t * u + θ * u by ring, Real.exp_add]
  ring


/-- The scalar collision density of Tsai (2024), equation (2.4), and Gu–Quastel–Tsai (2021), Lemma 8.4. -/
noncomputable def scalarDensity (θ t : ℝ) : ℝ := ∫ u in Ioi 0, scalarIntegrand θ t u

/-- The Gamma-integral formula for the scalar collision density. -/
theorem scalarDensity_eq_integral (θ t : ℝ) :
    scalarDensity θ t = ∫ u in Ioi 0, t ^ (u - 1) * Real.exp (θ * u) / Real.Gamma u := rfl

/-- The equivalent Gamma-Laplace representation. -/
theorem scalarDensity_eq_laplace (θ : ℝ) {t : ℝ} (ht : 0 < t) :
    scalarDensity θ t = t⁻¹ * ∫ u in Ioi 0, gammaLaplaceIntegrand (θ + Real.log t) u := by
  unfold scalarDensity
  simp_rw [scalarIntegrand_eq ht]
  exact integral_const_mul _ _

/-- Strict positivity at every positive time. -/
theorem scalarDensity_pos (θ : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < scalarDensity θ t := by
  rw [scalarDensity_eq_laplace θ ht]
  apply mul_pos (inv_pos.mpr ht)
  have hs : Function.support (gammaLaplaceIntegrand (θ + Real.log t)) ∩ Ioi 0 = Ioi 0 := by
    rw [inter_eq_right]
    intro u hu
    exact (gammaLaplaceIntegrand_pos _ hu).ne'
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · rw [hs, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (gammaLaplaceIntegrand_pos _ hu).le
  · exact integrableOn_gammaLaplaceIntegrand _

/-- Joint continuity in the parameter and in positive time. -/
theorem continuousOn_scalarDensity :
    ContinuousOn (fun p : ℝ × ℝ => scalarDensity p.1 p.2) {p | 0 < p.2} := by
  have h : ContinuousOn (fun p : ℝ × ℝ => p.2⁻¹ *
      ∫ u in Ioi 0, gammaLaplaceIntegrand (p.1 + Real.log p.2) u) {p | 0 < p.2} := by
    apply ContinuousOn.mul
    · apply continuous_snd.continuousOn.inv₀
      exact fun p hp => hp.ne'
    · apply continuous_gammaLaplaceIntegral.comp_continuousOn
      apply continuous_fst.continuousOn.add
      apply continuous_snd.continuousOn.log
      exact fun p hp => hp.ne'
  exact h.congr fun p hp => scalarDensity_eq_laplace p.1 hp

/-- Exact parameter transport under a time dilation. -/
theorem scalarDensity_scale (θ : ℝ) {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    a * scalarDensity θ (a * t) = scalarDensity (θ + Real.log a) t := by
  rw [scalarDensity_eq_laplace θ (mul_pos ha ht), scalarDensity_eq_laplace _ ht,
    Real.log_mul ha.ne' ht.ne']
  rw [show θ + (Real.log a + Real.log t) = θ + Real.log a + Real.log t by ring]
  rw [mul_inv, ← mul_assoc, mul_inv_cancel_left₀ ha.ne']

end Critical2DKPZ.DeltaBose
