/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.PowerComparison
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Integrability of the scalar weighted shell kernel

Splitting at any positive radius gives explicit near-zero and tail estimates.
The radial exponent satisfies `-1 < γ < 1`, including the denominator-power endpoint `r = 1` needed by LZ21.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Critical2DKPZ.MomentBounds

/-- The scalar radial summand used after counting the sup-norm shells. -/
def radialIntegrand (L γ x : ℝ) : ℝ := x ^ γ / (L + x ^ 2)

/-- The radial integrand is measurable. -/
theorem measurable_radialIntegrand (L γ : ℝ) : Measurable (radialIntegrand L γ) := by
  unfold radialIntegrand
  fun_prop

/-- The radial integrand is nonnegative. -/
theorem radialIntegrand_nonneg {L x : ℝ} (hL : 0 ≤ L) (hx : 0 ≤ x) (γ : ℝ) :
    0 ≤ radialIntegrand L γ x := div_nonneg (Real.rpow_nonneg hx _) (by positivity)

/-- The radial integrand satisfies the stated bound near the origin. -/
theorem radialIntegrand_le_near {L x γ : ℝ} (hL : 0 < L) (hx : 0 ≤ x) :
    radialIntegrand L γ x ≤ x ^ γ / L := by
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx _) hL (le_add_of_nonneg_right (sq_nonneg _))

/-- The radial integrand satisfies the stated bound at infinity. -/
theorem radialIntegrand_le_tail {L x γ : ℝ} (hL : 0 ≤ L) (hx : 0 < x) :
    radialIntegrand L γ x ≤ x ^ (γ - 2) := by
  have he : x ^ (γ - 2) = x ^ γ / x ^ 2 := by
    rw [Real.rpow_sub hx, Real.rpow_two]
  rw [he]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) (sq_pos_of_pos hx)
    (le_add_of_nonneg_left hL)

/-- The radial integrand is integrable on the near-origin interval. -/
theorem integrableOn_radialIntegrand_near {L γ R : ℝ} (hL : 0 < L) (hγ : -1 < γ) :
    IntegrableOn (radialIntegrand L γ) (Ioc 0 R) := by
  have hp : IntegrableOn (fun x : ℝ => x ^ γ / L) (Ioc 0 R) :=
    (intervalIntegral.intervalIntegrable_rpow' hγ).1.div_const L
  apply hp.mono' (measurable_radialIntegrand L γ).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (radialIntegrand_nonneg hL.le hx.1.le γ)]
  exact radialIntegrand_le_near hL hx.1.le

/-- The radial integrand is integrable on the tail interval. -/
theorem integrableOn_radialIntegrand_tail {L γ R : ℝ} (hL : 0 ≤ L) (hγ : γ < 1)
    (hR : 0 < R) : IntegrableOn (radialIntegrand L γ) (Ioi R) := by
  have hp : IntegrableOn (fun x : ℝ => x ^ (γ - 2)) (Ioi R) :=
    integrableOn_Ioi_rpow_of_lt (by linarith only [hγ]) hR
  apply hp.mono' (measurable_radialIntegrand L γ).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (radialIntegrand_nonneg hL (hR.trans hx).le γ)]
  exact radialIntegrand_le_tail hL (hR.trans hx)

/-- Integrability on the full positive half-line. -/
theorem integrableOn_radialIntegrand {L γ : ℝ} (hL : 0 < L) (hγlo : -1 < γ)
    (hγhi : γ < 1) : IntegrableOn (radialIntegrand L γ) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
  exact (integrableOn_radialIntegrand_near hL hγlo).union
    (integrableOn_radialIntegrand_tail hL.le hγhi (by norm_num))

/-- The integral of the radial integrand near the origin satisfies the stated bound. -/
theorem integral_radialIntegrand_near_le {L γ R : ℝ} (hL : 0 < L) (hγ : -1 < γ)
    (hR : 0 < R) :
    (∫ x in Ioc 0 R, radialIntegrand L γ x) ≤ R ^ (γ + 1) / (L * (γ + 1)) := by
  calc
    _ ≤ ∫ x in Ioc 0 R, x ^ γ / L := setIntegral_mono_on
      (integrableOn_radialIntegrand_near hL hγ)
      ((intervalIntegral.intervalIntegrable_rpow' hγ).1.div_const L)
      measurableSet_Ioc (fun x hx => radialIntegrand_le_near hL hx.1.le)
    _ = _ := by
      simp only [div_eq_mul_inv]
      rw [integral_mul_const, ← intervalIntegral.integral_of_le hR.le,
        integral_rpow (Or.inl hγ), Real.zero_rpow (by linarith only [hγ] : γ + 1 ≠ 0), sub_zero]
      field_simp

/-- The integral of the radial integrand on the tail satisfies the stated bound. -/
theorem integral_radialIntegrand_tail_le {L γ R : ℝ} (hL : 0 ≤ L) (hγ : γ < 1)
    (hR : 0 < R) :
    (∫ x in Ioi R, radialIntegrand L γ x) ≤ R ^ (γ - 1) / (1 - γ) := by
  calc
    _ ≤ ∫ x in Ioi R, x ^ (γ - 2) := setIntegral_mono_on
      (integrableOn_radialIntegrand_tail hL hγ hR)
      (integrableOn_Ioi_rpow_of_lt (by linarith only [hγ]) hR)
      measurableSet_Ioi (fun x hx => radialIntegrand_le_tail hL (hR.trans hx))
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt (by linarith only [hγ]) hR,
        show γ - 2 + 1 = γ - 1 by ring,
        show γ - 1 = -(1 - γ) by ring, div_neg, neg_div, neg_neg]

/-- Explicit two-piece bound; choosing R = sqrt L gives the required reciprocal exponent factors. -/
theorem integral_radialIntegrand_le {L γ R : ℝ} (hL : 0 < L) (hγlo : -1 < γ)
    (hγhi : γ < 1) (hR : 0 < R) :
    (∫ x in Ioi 0, radialIntegrand L γ x) ≤
      R ^ (γ + 1) / (L * (γ + 1)) + R ^ (γ - 1) / (1 - γ) := by
  have hd : Disjoint (Ioc (0 : ℝ) R) (Ioi R) :=
    disjoint_left.mpr (fun _ hx hy => (not_lt_of_ge hx.2) hy)
  rw [← Ioc_union_Ioi_eq_Ioi hR.le, setIntegral_union hd measurableSet_Ioi
    (integrableOn_radialIntegrand_near hL hγlo)
    (integrableOn_radialIntegrand_tail hL.le hγhi hR)]
  exact add_le_add (integral_radialIntegrand_near_le hL hγlo hR)
    (integral_radialIntegrand_tail_le hL.le hγhi hR)

end Critical2DKPZ.MomentBounds
