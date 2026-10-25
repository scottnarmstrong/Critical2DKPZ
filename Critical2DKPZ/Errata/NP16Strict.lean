/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

/-! # A one-dimensional coercive matrix example

The example satisfies the symmetry, positivity, coercivity and epsilon conditions of NP16 Lemma 3.2 and tests the intermediate lower bound in its proof. -/

@[expose] public noncomputable section

namespace Critical2DKPZ.Errata

/-- The matrices `A = 0` and `B = id` satisfy the stated coercivity conditions while their quadratic form at `ε = 1/4` is below `3/4`. -/
theorem np16_lower_bound_strict_counterexample :
    let A : ℝ →L[ℝ] ℝ := 0
    let B : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ
    let δ : ℝ := 1
    let ε : ℝ := 1 / 4
    let u : ℝ := 1
    let v : ℝ := 0
    0 < δ ∧
      (∀ w : ℝ, 0 ≤ w * A w) ∧
      (∀ x y : ℝ, x * B y = B x * y) ∧
      (∀ w : ℝ, A w = 0 → δ * ‖w‖ ^ 2 ≤ w * B w) ∧
      (∀ w : ℝ, (∀ z : ℝ, A z = 0 → w * z = 0) →
        δ * ‖w‖ ^ 2 ≤ w * A w) ∧
      0 ≤ ε ∧ ε ≤ δ ^ 2 / (‖B‖ ^ 2 + δ * ‖B‖) ∧
      A u = 0 ∧ (∀ z : ℝ, A z = 0 → v * z = 0) ∧
      ¬ (δ * ‖u‖ ^ 2 - ε * ‖B‖ * ‖u‖ ^ 2 -
          2 * ε * ‖B‖ * ‖u‖ * ‖v‖ + ε * δ * ‖v‖ ^ 2 ≤
        (u + v) * (A + ε • B) (u + v)) := by
  dsimp only
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    simp only [zero_apply, mul_zero, le_refl]
  · intro x y
    simp only [ContinuousLinearMap.id_apply]
  · intro w _hw
    simp only [one_mul, ContinuousLinearMap.id_apply]
    rw [Real.norm_eq_abs, sq_abs, pow_two]
  · intro w hw
    have hz : w = 0 := by simpa using hw 1 rfl
    subst w
    norm_num
  · norm_num
  · norm_num
  · rfl
  · intro z _hz
    exact zero_mul z
  · norm_num

end Critical2DKPZ.Errata
