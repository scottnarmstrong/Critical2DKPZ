/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SingleCollisionAction
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Cancellation of the single-collision norm coefficients -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

private theorem collision_coefficient_algebra (a j r q : ℝ)
    (ha : a ≠ 0) (hr : r ≠ 0) (hq : q ≠ 0) :
    (a * r)⁻¹ * (a * j) ^ 2 * (a * q)⁻¹ = j ^ 2 * r⁻¹ * q⁻¹ := by
  field_simp

private theorem half_power_sq {t : ℝ} (ht : 0 < t) :
    (t ^ (-(1 / 2 : ℝ))) ^ 2 = t⁻¹ := by
  rw [pow_two, ← Real.rpow_add ht]
  norm_num only [show -(1 / 2 : ℝ) + -(1 / 2 : ℝ) = -1 by ring, Real.rpow_neg_one]

/-- All `4π` factors cancel, leaving the endpoint half-powers and the collision density. -/
theorem singleCollisionCoefficient_eq {θ r s q : ℝ} (hr : 0 < r) (hs : 0 < s) (hq : 0 < q) :
    ENNReal.ofReal (4 * Real.pi * r)⁻¹ * ENNReal.ofReal (4 * Real.pi * scalarDensity θ s) ^ 2 *
      ENNReal.ofReal (4 * Real.pi * q)⁻¹ =
        ENNReal.ofReal (scalarDensity θ s * r ^ (-(1 / 2 : ℝ)) * q ^ (-(1 / 2 : ℝ))) ^ 2 := by
  have hj : 0 ≤ scalarDensity θ s := (scalarDensity_pos θ hs).le
  have hπ : 0 < 4 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hA : 0 ≤ (4 * Real.pi * r)⁻¹ := inv_nonneg.mpr (mul_nonneg hπ.le hr.le)
  have hB : 0 ≤ 4 * Real.pi * scalarDensity θ s := mul_nonneg hπ.le hj
  have hM : 0 ≤ scalarDensity θ s * r ^ (-(1 / 2 : ℝ)) * q ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg (mul_nonneg hj (Real.rpow_nonneg hr.le _)) (Real.rpow_nonneg hq.le _)
  have he : (4 * Real.pi * r)⁻¹ * (4 * Real.pi * scalarDensity θ s) ^ 2 *
      (4 * Real.pi * q)⁻¹ =
        (scalarDensity θ s * r ^ (-(1 / 2 : ℝ)) * q ^ (-(1 / 2 : ℝ))) ^ 2 := by
    rw [collision_coefficient_algebra (4 * Real.pi) (scalarDensity θ s) r q hπ.ne' hr.ne' hq.ne']
    simp only [mul_pow, half_power_sq hr, half_power_sq hq]
  rw [← ENNReal.ofReal_pow hB 2, ← ENNReal.ofReal_mul hA,
    ← ENNReal.ofReal_mul (mul_nonneg hA (sq_nonneg _)), he, ENNReal.ofReal_pow hM 2]


end Critical2DKPZ.SHF.Flow

end
