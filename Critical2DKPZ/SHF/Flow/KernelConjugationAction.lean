/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.KernelConjugation

/-! # Actions of exponentially conjugated kernels -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- The action of a conjugated kernel multiplies the input and output by reciprocal exponential weights. -/
theorem expConjugate_action_eq {X Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (a : X → ℝ) (b : Y → ℝ) (K : X → Y → ℝ≥0∞)
    (f : Y → ℝ≥0∞) (x : X) :
    (∫⁻ y, expConjugate a b K x y * f y ∂μ) =
      ENNReal.ofReal (Real.exp (a x)) *
        ∫⁻ y, K x y * (ENNReal.ofReal (Real.exp (-b y)) * f y) ∂μ := by
  have he (y : Y) : expConjugate a b K x y * f y =
      ENNReal.ofReal (Real.exp (a x)) * (K x y * (ENNReal.ofReal (Real.exp (-b y)) * f y)) := by
    unfold expConjugate
    rw [sub_eq_add_neg, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    ac_rfl
  simp_rw [he]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end Critical2DKPZ.SHF.Flow

end
