/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.HalfTimeBounds
public import Critical2DKPZ.SHF.DeltaBose.FreeMass
import Mathlib.Tactic

/-!
# A heat-potential auxiliary weight

The potential is kept as a positive heat integral. Its heat convolution is
uniformly bounded by a constant times `t^(-1/2)`. In particular it is finite
almost everywhere, without an appeal to a pointwise Riesz-kernel formula.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- A translated planar heat kernel has total mass one at every positive time. -/
theorem lintegral_heatKernel_sub {t : ℝ} (ht : 0 < t) (a : Plane) :
    (∫⁻ y : Plane, ENNReal.ofReal (heatKernel t (y - a))) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_heatKernel ht).comp_sub_right a)
    (Filter.Eventually.of_forall fun y => (Critical2DKPZ.heatKernel_pos ht _).le),
    integral_heatKernel_sub ht a, ENNReal.ofReal_one]

/-- The semigroup identity for the nonnegative heat kernels. -/
theorem lintegral_heatKernel_mul_sub {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x : Plane) :
    (∫⁻ y : Plane, ENNReal.ofReal (heatKernel s y) * ENNReal.ofReal (heatKernel t (x - y))) =
      ENNReal.ofReal (heatKernel (s + t) x) := by
  have he (y : Plane) : ENNReal.ofReal (heatKernel s y) * ENNReal.ofReal (heatKernel t (x - y)) =
      ENNReal.ofReal (heatKernel (s + t) x) *
        ENNReal.ofReal (heatKernel (s * t / (s + t)) (y - (s / (s + t)) • x)) := by
    rw [← ENNReal.ofReal_mul (Critical2DKPZ.heatKernel_pos hs _).le, heatKernel_mul_sub hs ht,
      ENNReal.ofReal_mul (Critical2DKPZ.heatKernel_pos (add_pos hs ht) _).le]
  simp_rw [he]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_heatKernel_sub (div_pos (mul_pos hs ht) (add_pos hs ht)), mul_one]

/-- The positive heat-potential integrand on its original free-coordinate measure. -/
noncomputable def heatPotentialIntegrand (s : ℝ) (x : Plane) : ℝ≥0∞ :=
  ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) * ENNReal.ofReal (heatKernel s x)

/-- The heat-potential integrand is jointly measurable in time and position. -/
theorem measurable_heatPotentialIntegrand : Measurable (Function.uncurry heatPotentialIntegrand) := by
  unfold heatPotentialIntegrand heatKernel
  fun_prop

/-- The auxiliary Schur weight. -/
noncomputable def heatPotential (x : Plane) : ℝ≥0∞ :=
  ∫⁻ s in Ioi 0, heatPotentialIntegrand s x

/-- The heat potential is a measurable function of position. -/
theorem measurable_heatPotential : Measurable heatPotential := by
  have hm : Measurable (fun p : Plane × ℝ => heatPotentialIntegrand p.2 p.1) :=
    measurable_heatPotentialIntegrand.comp measurable_swap
  exact hm.lintegral_prod_right' (ν := volume.restrict (Ioi 0))

/-- The heat potential is invariant under spatial reflection. -/
theorem heatPotential_neg (x : Plane) : heatPotential (-x) = heatPotential x := by
  simp only [heatPotential, heatPotentialIntegrand, heatKernel_neg]

/-- The potential is strictly positive at every spatial point. -/
theorem heatPotential_pos (x : Plane) : 0 < heatPotential x := by
  have hm : Measurable (fun s : ℝ => heatPotentialIntegrand s x) :=
    measurable_heatPotentialIntegrand.comp (measurable_id.prodMk measurable_const)
  apply (setLIntegral_pos_iff hm).mpr
  have hs : Ioo (1 : ℝ) 2 ⊆ Function.support (fun s => heatPotentialIntegrand s x) ∩ Ioi 0 := by
    intro s hs
    have hs0 : 0 < s := lt_trans zero_lt_one hs.1
    refine ⟨?_, hs0⟩
    exact mul_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hs0 _)))
      (ne_of_gt (ENNReal.ofReal_pos.mpr (Critical2DKPZ.heatKernel_pos hs0 x)))
  have hp : 0 < volume (Ioo (1 : ℝ) 2) := by rw [Real.volume_Ioo]; norm_num
  exact hp.trans_le (measure_mono hs)

/-- Heat convolution moves the clock inside the positive potential integral. -/
theorem lintegral_heatKernel_mul_heatPotential {t : ℝ} (ht : 0 < t) (x : Plane) :
    (∫⁻ y : Plane, ENNReal.ofReal (heatKernel t (x - y)) * heatPotential y) =
      ∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) *
        ENNReal.ofReal (heatKernel (t + s) x) := by
  have hH : Measurable (fun p : Plane × ℝ =>
      ENNReal.ofReal (heatKernel t (x - p.1)) * heatPotentialIntegrand p.2 p.1) := by
    have h1 : Measurable (fun p : Plane × ℝ => ENNReal.ofReal (heatKernel t (x - p.1))) := by
      unfold heatKernel
      fun_prop
    exact h1.mul (measurable_heatPotentialIntegrand.comp measurable_swap)
  calc (∫⁻ y : Plane, ENNReal.ofReal (heatKernel t (x - y)) * heatPotential y)
      = ∫⁻ y : Plane, ∫⁻ s in Ioi 0,
          ENNReal.ofReal (heatKernel t (x - y)) * heatPotentialIntegrand s y := by
        apply lintegral_congr
        intro y
        exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ s in Ioi 0, ∫⁻ y : Plane,
          ENNReal.ofReal (heatKernel t (x - y)) * heatPotentialIntegrand s y :=
        lintegral_lintegral_swap hH.aemeasurable
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      unfold heatPotentialIntegrand
      have he (y : Plane) : ENNReal.ofReal (heatKernel t (x - y)) *
          (ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) * ENNReal.ofReal (heatKernel s y)) =
          ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) *
            (ENNReal.ofReal (heatKernel s y) * ENNReal.ofReal (heatKernel t (x - y))) := by ac_rfl
      simp_rw [he]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_heatKernel_mul_sub hs ht, add_comm s t]

/-- The smoothed potential is bounded uniformly in space at the half-time rate. -/
theorem lintegral_heatKernel_mul_heatPotential_le {t : ℝ} (ht : 0 < t) (x : Plane) :
    (∫⁻ y : Plane, ENNReal.ofReal (heatKernel t (x - y)) * heatPotential y) ≤
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * t ^ (-(1 / 2 : ℝ))) * halfTimeResolventConstant := by
  rw [lintegral_heatKernel_mul_heatPotential ht]
  calc (∫⁻ s in Ioi 0, ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) *
        ENNReal.ofReal (heatKernel (t + s) x))
      ≤ ∫⁻ s in Ioi 0, ENNReal.ofReal ((2 * Real.pi)⁻¹) *
          ENNReal.ofReal (s ^ (-(1 / 2 : ℝ)) / (t + s)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have h := ENNReal.ofReal_le_ofReal (heatKernel_le_at_zero (add_pos ht hs).le x)
        have he : ENNReal.ofReal (s ^ (-(1 / 2 : ℝ))) * ENNReal.ofReal (2 * Real.pi * (t + s))⁻¹ =
            ENNReal.ofReal ((2 * Real.pi)⁻¹) * ENNReal.ofReal (s ^ (-(1 / 2 : ℝ)) / (t + s)) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _),
            ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * Real.pi)⁻¹)]
          congr 1
          field_simp
        exact (mul_le_mul' le_rfl h).trans_eq he
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_halfTime_div_add ht,
        ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * Real.pi)⁻¹)]

/-- The auxiliary weight is finite almost everywhere in planar volume. -/
theorem heatPotential_ne_top_ae : ∀ᵐ x : Plane, heatPotential x ≠ ⊤ := by
  have hm : Measurable (fun y : Plane => ENNReal.ofReal (heatKernel 1 (0 - y)) * heatPotential y) := by
    have hh : Measurable (fun y : Plane => ENNReal.ofReal (heatKernel 1 (0 - y))) := by
      unfold heatKernel
      fun_prop
    exact hh.mul measurable_heatPotential
  have hC : ENNReal.ofReal ((2 * Real.pi)⁻¹ * (1 : ℝ) ^ (-(1 / 2 : ℝ))) *
      halfTimeResolventConstant ≠ ⊤ := by
    have hc := halfTimeResolventConstant_ne_top
    finiteness
  have hi : (∫⁻ y : Plane, ENNReal.ofReal (heatKernel 1 (0 - y)) * heatPotential y) ≠ ⊤ :=
    ne_of_lt ((lintegral_heatKernel_mul_heatPotential_le zero_lt_one 0).trans_lt (lt_top_iff_ne_top.mpr hC))
  filter_upwards [ae_lt_top hm hi] with y hy
  intro he
  have hh : ENNReal.ofReal (heatKernel 1 (0 - y)) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Critical2DKPZ.heatKernel_pos zero_lt_one _))
  rw [he, ENNReal.mul_top hh] at hy
  exact (lt_irrefl _ hy)

/-- The companion half-time integral appearing in the swapping Schur row estimate. -/
theorem lintegral_halfTime_heatKernel_double (x : Plane) :
    (∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) * ENNReal.ofReal (heatKernel (2 * t) x)) =
      ENNReal.ofReal ((2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹) * heatPotential x := by
  let H := ∫⁻ t in Ioi 0, ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) * ENNReal.ofReal (heatKernel (2 * t) x)
  have h : heatPotential x = ENNReal.ofReal (2 * (2 : ℝ) ^ (-(1 / 2 : ℝ))) * H := by
    rw [heatPotential, lintegral_Ioi_mul (show (0 : ℝ) < 2 by norm_num)]
    have he : (∫⁻ u in Ioi 0, heatPotentialIntegrand (2 * u) x) =
        ENNReal.ofReal ((2 : ℝ) ^ (-(1 / 2 : ℝ))) * H := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [heatPotentialIntegrand, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hu.le,
        ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ))), mul_assoc]
    rw [he, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hc : 0 < 2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
  have hi : ENNReal.ofReal ((2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹) *
      ENNReal.ofReal (2 * (2 : ℝ) ^ (-(1 / 2 : ℝ))) = 1 := by
    rw [← ENNReal.ofReal_mul (inv_pos.mpr hc).le, inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one]
  change H = _
  rw [h, ← mul_assoc, hi, one_mul]

end Critical2DKPZ.DeltaBose
