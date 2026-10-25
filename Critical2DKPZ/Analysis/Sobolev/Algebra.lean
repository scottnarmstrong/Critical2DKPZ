/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.MemLocalNegSobolev
public import Critical2DKPZ.Analysis.Sobolev.Weight
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic.Ring

/-! Localized negative Sobolev energy is homogeneous under scalar multiplication, invariant under negation, and decreasing in the Sobolev order. -/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ

/-- The localized negative Sobolev energy of the zero distribution is zero. -/
@[simp] theorem localNegSobolevSq_zero (a : ℝ) (χ : TestFn) :
    localNegSobolevSq a 0 χ = 0 := by
  simp only [localNegSobolevSq, zero_apply, zero_pow (by decide : 2 ≠ 0), add_zero,
    mul_zero, ENNReal.ofReal_zero, lintegral_zero]

/-- Scalar homogeneity of the extended squared seminorm. -/
theorem localNegSobolevSq_smul (a : ℝ) (T : Distr) (χ : TestFn) (c : ℝ) :
    localNegSobolevSq a (c • T) χ = ENNReal.ofReal (c ^ 2) * localNegSobolevSq a T χ := by
  simp only [localNegSobolevSq, smul_apply, smul_eq_mul]
  have hp (ξ : Plane) :
      ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-a) *
        ((c * T (χ.mulCos ξ)) ^ 2 + (c * T (χ.mulSin ξ)) ^ 2)) =
      ENNReal.ofReal (c ^ 2) * ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-a) *
        ((T (χ.mulCos ξ)) ^ 2 + (T (χ.mulSin ξ)) ^ 2)) := by
    rw [← ENNReal.ofReal_mul (sq_nonneg c)]
    congr 1
    ring
  simp_rw [hp]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  ac_rfl

/-- Negating a distribution leaves its localized negative Sobolev energy unchanged. -/
@[simp] theorem localNegSobolevSq_neg (a : ℝ) (T : Distr) (χ : TestFn) :
    localNegSobolevSq a (-T) χ = localNegSobolevSq a T χ := by
  simpa only [neg_one_smul, neg_one_sq, ENNReal.ofReal_one, one_mul] using
    localNegSobolevSq_smul a T χ (-1)

/-- Increasing the negative Sobolev order weakens the squared seminorm. -/
theorem localNegSobolevSq_antitone (T : Distr) (χ : TestFn) :
    Antitone (fun a : ℝ => localNegSobolevSq a T χ) := by
  intro a b hab
  unfold localNegSobolevSq
  apply mul_le_mul' le_rfl
  apply lintegral_mono
  intro ξ
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le (by linarith only [sq_nonneg ‖ξ‖]) (neg_le_neg hab))
    (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The zero distribution belongs to every local negative Sobolev space. -/
@[simp] theorem memLocalNegSobolev_zero (a : ℝ) : MemLocalNegSobolev a 0 := by
  intro χ
  rw [localNegSobolevSq_zero]
  exact ENNReal.zero_lt_top


/-- Local negative Sobolev regularity is preserved by negation. -/
theorem MemLocalNegSobolev.neg {a : ℝ} {T : Distr} (hT : MemLocalNegSobolev a T) :
    MemLocalNegSobolev a (-T) := by
  intro χ
  rw [localNegSobolevSq_neg]
  exact hT χ

/-- Local negative Sobolev regularity persists when the negative order increases. -/
theorem MemLocalNegSobolev.mono {a b : ℝ} (hab : a ≤ b) {T : Distr}
    (hT : MemLocalNegSobolev a T) : MemLocalNegSobolev b T := by
  intro χ
  exact (localNegSobolevSq_antitone T χ hab).trans_lt (hT χ)

end Critical2DKPZ

end
