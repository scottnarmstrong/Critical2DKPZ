/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Heat.Basic
public import Critical2DKPZ.Analysis.Heat.Semigroup
public import Critical2DKPZ.SHF.DeltaBose.ScalarEnvelope
public import Critical2DKPZ.SHF.DeltaBose.ScalarLaplace
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! # Gaussian pair factorization for the head estimate -/

@[expose] public section

namespace Critical2DKPZ.SHF.Tsai

open MeasureTheory Set Critical2DKPZ.DeltaBose
open scoped ENNReal




/-- Convolving two translated planar heat kernels adds their elapsed times. -/
theorem lintegral_heatKernel_shifted_mul {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (x y : Plane) :
    (∫⁻ z : Plane, ENNReal.ofReal (Critical2DKPZ.heatKernel s (z - x)) *
      ENNReal.ofReal (Critical2DKPZ.heatKernel t (y - z))) =
        ENNReal.ofReal (Critical2DKPZ.heatKernel (s + t) (y - x)) := by
  have hfirst : Integrable (fun z : Plane => Critical2DKPZ.heatKernel s (z - x)) := by
    have hmap : MeasurePreserving (fun z : Plane => z - x) volume volume := by
      change MeasurePreserving (fun z : Plane => z + -x) volume volume
      exact MeasurePreserving.add_right (volume : Measure Plane) (-x)
        (MeasurePreserving.id (volume : Measure Plane))
    have hemb : MeasurableEmbedding (fun z : Plane => z - x) :=
      (MeasurableEquiv.addRight (-x)).measurableEmbedding
    exact hmap.integrable_comp_emb hemb |>.mpr (Critical2DKPZ.integrable_heatKernel hs)
  have hmeas : AEStronglyMeasurable
      (fun z : Plane => Critical2DKPZ.heatKernel t (y - z)) volume :=
    (Critical2DKPZ.measurable_heatKernel t).comp
      (measurable_const.sub measurable_id) |>.aestronglyMeasurable
  have hbound : ∀ᵐ z : Plane ∂volume,
      ‖Critical2DKPZ.heatKernel t (y - z)‖ ≤ (2 * Real.pi * t)⁻¹ := by
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg
      (Critical2DKPZ.heatKernel_nonneg ht.le (y - z))]
    exact Critical2DKPZ.heatKernel_le_at_zero ht.le (y - z)
  have hint : Integrable
      (fun z : Plane => Critical2DKPZ.heatKernel s (z - x) *
        Critical2DKPZ.heatKernel t (y - z)) := hfirst.mul_bdd hmeas hbound
  have hnonneg : ∀ᵐ z : Plane ∂volume,
      0 ≤ Critical2DKPZ.heatKernel s (z - x) *
        Critical2DKPZ.heatKernel t (y - z) :=
    Filter.Eventually.of_forall fun z => mul_nonneg
      (Critical2DKPZ.heatKernel_nonneg hs.le (z - x))
      (Critical2DKPZ.heatKernel_nonneg ht.le (y - z))
  have htranslate :
      (fun z : Plane => Critical2DKPZ.heatKernel s (z - x) *
        Critical2DKPZ.heatKernel t (y - z)) =
      (fun z : Plane => Critical2DKPZ.heatKernel s z *
        Critical2DKPZ.heatKernel t ((y - x) - z)) ∘ fun z => z - x := by
    funext z
    simp only [Function.comp_apply]
    congr 1
    abel
  have hreal :
      (∫ z : Plane, Critical2DKPZ.heatKernel s (z - x) *
        Critical2DKPZ.heatKernel t (y - z)) =
      Critical2DKPZ.heatKernel (s + t) (y - x) := by
    rw [htranslate]
    simpa only [Function.comp_def] using
      (integral_sub_right_eq_self
        (fun z : Plane => Critical2DKPZ.heatKernel s z *
          Critical2DKPZ.heatKernel t ((y - x) - z)) x).trans
        (Critical2DKPZ.integral_heatKernel_mul_sub hs ht (y - x))
  calc
    _ = ∫⁻ z : Plane,
        ENNReal.ofReal (Critical2DKPZ.heatKernel s (z - x) *
          Critical2DKPZ.heatKernel t (y - z)) := by
          apply lintegral_congr
          intro z
          rw [← ENNReal.ofReal_mul
            (Critical2DKPZ.heatKernel_nonneg hs.le (z - x))]
    _ = ENNReal.ofReal (∫ z : Plane,
        Critical2DKPZ.heatKernel s (z - x) *
          Critical2DKPZ.heatKernel t (y - z)) :=
          (ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm
    _ = _ := by rw [hreal]

/-- Three positive ENNReal heat strands integrate to the heat kernel at their
total elapsed time. -/
theorem lintegral_heatKernel_three_shifted {r u v : ℝ}
    (hr : 0 < r) (hu : 0 < u) (hv : 0 < v) (x y : Plane) :
    (∫⁻ z : Plane, ENNReal.ofReal (Critical2DKPZ.heatKernel r (z - x)) *
      (∫⁻ z' : Plane,
        ENNReal.ofReal (Critical2DKPZ.heatKernel u (z' - z)) *
          ENNReal.ofReal (Critical2DKPZ.heatKernel v (y - z')))) =
      ENNReal.ofReal (Critical2DKPZ.heatKernel (r + u + v) (y - x)) := by
  calc
    _ = ∫⁻ z : Plane, ENNReal.ofReal (Critical2DKPZ.heatKernel r (z - x)) *
        ENNReal.ofReal (Critical2DKPZ.heatKernel (u + v) (y - z)) := by
          apply lintegral_congr
          intro z
          rw [lintegral_heatKernel_shifted_mul hu hv z y]
    _ = ENNReal.ofReal (Critical2DKPZ.heatKernel (r + (u + v)) (y - x)) :=
      lintegral_heatKernel_shifted_mul hr (add_pos hu hv) x y
    _ = _ := by ring_nf

/-- For `t ≤ T` and `r > t / 2`, the collision envelope at `r` is at most a constant
times `t⁻¹`. -/
theorem collisionTimeEnvelope_le_div {T t r : ℝ} (hT : 0 < T)
    (ht : 0 < t) (htT : t ≤ T) (hr : t / 2 < r) :
    collisionTimeEnvelope r ≤
      (4 * max T 1 / (Real.log (1 / 2 : ℝ)) ^ 2) / t := by
  let x : ℝ := min r (1 / 2)
  have hx : 0 < x := by
    dsimp [x]
    exact lt_min (lt_trans (by positivity) hr) (by norm_num)
  have hxhalf : x ≤ (1 / 2 : ℝ) := by
    dsimp [x]
    exact min_le_right _ _
  have hxlower : t ≤ 4 * max T 1 * x := by
    by_cases hsmall : t ≤ 1 / 2
    · have htx : t / 2 ≤ x := by
        dsimp [x]
        apply le_min
        · linarith
        · linarith
      nlinarith [le_max_right T 1]
    · have hxquarter : 1 / 4 ≤ x := by
        dsimp [x]
        apply le_min
        · linarith
        · norm_num
      calc
        t ≤ T := htT
        _ ≤ max T 1 := le_max_left _ _
        _ ≤ 4 * max T 1 * x := by nlinarith [le_max_right T 1]
  have hlog : (Real.log (1 / 2 : ℝ)) ^ 2 ≤ (Real.log x) ^ 2 := by
    have hlogx : Real.log x ≤ Real.log (1 / 2 : ℝ) := Real.log_le_log hx hxhalf
    have hxneg : Real.log x < 0 :=
      Real.log_neg hx (lt_of_le_of_lt hxhalf (by norm_num))
    have hhalfneg : Real.log (1 / 2 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
    calc
      (Real.log (1 / 2 : ℝ)) ^ 2 ≤ Real.log x * Real.log (1 / 2 : ℝ) := by
        convert mul_le_mul_of_nonpos_right hlogx hhalfneg.le using 1
        ring
      _ ≤ (Real.log x) ^ 2 := by
        convert mul_le_mul_of_nonpos_left hlogx hxneg.le using 1
        ring
  have hden : 0 < (Real.log (1 / 2 : ℝ)) ^ 2 := sq_pos_of_ne_zero (by
    have : Real.log (1 / 2 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
    exact ne_of_lt this)
  have hinvX : x⁻¹ ≤ (4 * max T 1) / t := by
    have hfrac : 1 / x ≤ (4 * max T 1) / t :=
      (div_le_div_iff₀ hx ht).2 (by nlinarith [hxlower])
    simpa only [one_div] using hfrac
  have hinvLog : (Real.log x ^ 2)⁻¹ ≤ ((Real.log (1 / 2 : ℝ)) ^ 2)⁻¹ := by
    simpa only [one_div] using (one_div_le_one_div_of_le hden hlog)
  change (x * (Real.log x) ^ 2)⁻¹ ≤ _
  rw [mul_inv]
  calc
    x⁻¹ * (Real.log x ^ 2)⁻¹ ≤
        ((4 * max T 1) / t) * ((Real.log (1 / 2 : ℝ)) ^ 2)⁻¹ := by
          gcongr
    _ = (4 * max T 1 / (Real.log (1 / 2 : ℝ)) ^ 2) / t := by ring


end Critical2DKPZ.SHF.Tsai

end
