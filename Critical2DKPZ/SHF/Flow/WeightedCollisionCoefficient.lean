/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.WeightedCollisionSlice
public import Critical2DKPZ.SHF.Flow.SingleCollisionCoefficient

/-! # Uniform endpoint majorants for the weighted collision slice -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- The canonical exponential growth is monotone in elapsed time. -/
theorem weightGrowth_mono (n : ℕ) (a : ℝ) {s t : ℝ} (hst : s ≤ t) :
    weightGrowth n a s ≤ weightGrowth n a t := by
  unfold weightGrowth
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left hst (by positivity)

private theorem doubled_trace_coefficient_le {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (4 * Real.pi * (2 * t))⁻¹ ≤ ENNReal.ofReal (4 * Real.pi * t)⁻¹ := by
  apply ENNReal.ofReal_le_ofReal
  apply inv_anti₀ (by positivity)
  have h : 0 < 4 * Real.pi * t := by positivity
  linarith only [h]

/-- A common finite time window contributes only three bounded weight-growth factors. -/
theorem oneCollisionSpatialSlice_weighted_l2_majorant {n : ℕ} (α : CollisionPair n) (θ : ℝ)
    {a r s q T : ℝ} (ha : 0 ≤ a) (hr : 0 < r) (hs : 0 < s) (hq : 0 < q)
    (hrT : r ≤ T) (hsT : s ≤ T) (hqT : q ≤ T)
    {f : Configuration n → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x : Configuration n, (∫⁻ y : Configuration n,
      expConjugate (fun x => a * configurationOneNorm x) (fun y => a * configurationOneNorm y)
        (oneCollisionSpatialSlice α θ r s q) x y * f y) ^ 2) ≤
      (ENNReal.ofReal (weightGrowth n a T) ^ 3) ^ 2 *
        ENNReal.ofReal (scalarDensity θ s * r ^ (-(1 / 2 : ℝ)) * q ^ (-(1 / 2 : ℝ))) ^ 2 *
          ∫⁻ y : Configuration n, f y ^ 2 := by
  let W : ℝ≥0∞ := ENNReal.ofReal (weightGrowth n a T)
  have hwr : ENNReal.ofReal (weightGrowth n a r) ^ 2 ≤ W ^ 2 :=
    pow_le_pow_left' (ENNReal.ofReal_le_ofReal (weightGrowth_mono n a hrT)) 2
  have hwq : ENNReal.ofReal (weightGrowth n a q) ^ 2 ≤ W ^ 2 :=
    pow_le_pow_left' (ENNReal.ofReal_le_ofReal (weightGrowth_mono n a hqT)) 2
  have hwc : ENNReal.ofReal (weightGrowth n a s * (4 * Real.pi * scalarDensity θ s)) ^ 2 ≤
      W ^ 2 * ENNReal.ofReal (4 * Real.pi * scalarDensity θ s) ^ 2 := by
    rw [ENNReal.ofReal_mul (weightGrowth_pos n a s).le, mul_pow]
    exact mul_le_mul' (pow_le_pow_left'
      (ENNReal.ofReal_le_ofReal (weightGrowth_mono n a hsT)) 2) le_rfl
  have hcoef := mul_le_mul'
    (mul_le_mul' hwr (doubled_trace_coefficient_le hr))
    (mul_le_mul' hwc (mul_le_mul' hwq (doubled_trace_coefficient_le hq)))
  have he : (W ^ 2 * ENNReal.ofReal (4 * Real.pi * r)⁻¹) *
      (W ^ 2 * ENNReal.ofReal (4 * Real.pi * scalarDensity θ s) ^ 2 *
        (W ^ 2 * ENNReal.ofReal (4 * Real.pi * q)⁻¹)) =
      (W ^ 3) ^ 2 * ENNReal.ofReal
        (scalarDensity θ s * r ^ (-(1 / 2 : ℝ)) * q ^ (-(1 / 2 : ℝ))) ^ 2 := by
    rw [← singleCollisionCoefficient_eq hr hs hq]
    simp only [pow_succ, pow_zero]
    ac_rfl
  exact (oneCollisionSpatialSlice_weighted_l2_sq_le α θ ha hr hs hq hf).trans
    (mul_le_mul' (hcoef.trans_eq he) le_rfl)

end Critical2DKPZ.SHF.Flow

end
