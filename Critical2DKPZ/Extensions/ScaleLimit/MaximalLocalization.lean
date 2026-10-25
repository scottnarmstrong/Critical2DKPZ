/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.HardyLittlewood
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Localization of maximal functions to a larger ball -/

public section

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A ball average depends only on the values within that ball. -/
theorem ballAverage_congr_on {f g : Plane → ℝ} {y : Plane} {r : ℝ}
    (h : EqOn f g (ball y r)) : ballAverage f y r = ballAverage g y r := by
  apply congrArg (fun t => (volume (ball y r))⁻¹ * t)
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  exact congrArg enorm (h hz)

/-- At centers in a ball, averages of radius at most `R ≤ k` only use the
field within the ball of radius `2k`. -/
theorem maximalFnLe_indicator_ball_le (g : Plane → ℝ) {R k : ℝ}
    (hRk : R ≤ k) {y : Plane} (hy : y ∈ ball (0 : Plane) k) :
    maximalFnLe R g y ≤ maximalFn ((ball (0 : Plane) (2 * k)).indicator g) y := by
  apply iSup_le
  intro r
  have hdist : dist y (0 : Plane) < k := mem_ball.mp hy
  have hsub : ball y r.1 ⊆ ball (0 : Plane) (2 * k) := by
    apply ball_subset_ball'
    linarith only [r.2.2, hRk, hdist]
  have heq : ballAverage g y r =
      ballAverage ((ball (0 : Plane) (2 * k)).indicator g) y r :=
    ballAverage_congr_on (fun z hz => (indicator_of_mem (hsub hz) g).symm)
  rw [heq]
  exact le_iSup_of_le ⟨r.1, r.2.1⟩ le_rfl

/-- Doubling the radius multiplies planar ball volume by four. -/
theorem volume_ball_two_mul (y : Plane) (r : ℝ) :
    volume (ball y (2 * r)) = 4 * volume (ball y r) := by
  rw [volume.addHaar_ball_mul_of_pos y (by norm_num : (0 : ℝ) < 2) r,
    volume.addHaar_ball_center y r]
  norm_num [Plane, finrank_euclideanSpace]

end Critical2DKPZ.Extensions.ScaleLimit

end
