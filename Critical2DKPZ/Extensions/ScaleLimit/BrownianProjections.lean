/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily
import Mathlib.Tactic

/-! # Scalar projections of the Brownian projective Gaussian family -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A scalar linear projection of a finite real vector. -/
def weightedCoordinate {I : Type*} [Fintype I] (v : I → ℝ) (x : I → ℝ) : ℝ :=
  ∑ i, x i * v i

/-- Every evaluation of the Brownian finite-dimensional family is square integrable. -/
theorem memLp_eval_projectiveFamily (I : Finset ℝ≥0) (i : I) :
    MemLp (fun x : I → ℝ => x i) 2 (BrownianReal.projectiveFamily I) := by
  let f : (I → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  convert! IsGaussian.memLp_dual (BrownianReal.projectiveFamily I) f 2 (by norm_num) using 1

/-- Every scalar projection is centered. -/
theorem integral_weightedCoordinate_projectiveFamily (I : Finset ℝ≥0) (v : I → ℝ) :
    (∫ x, weightedCoordinate v x ∂BrownianReal.projectiveFamily I) = 0 := by
  unfold weightedCoordinate
  rw [integral_finsetSum Finset.univ (fun i _ =>
    ((memLp_eval_projectiveFamily I i).integrable one_le_two).mul_const (v i))]
  simp only [integral_mul_const, BrownianReal.integral_eval_projectiveFamily, zero_mul,
    Finset.sum_const_zero]

/-- Its variance is the quadratic form of the Brownian minimum covariance. -/
theorem variance_weightedCoordinate_projectiveFamily (I : Finset ℝ≥0) (v : I → ℝ) :
    variance (weightedCoordinate v) (BrownianReal.projectiveFamily I) =
      ∑ i : I, ∑ j : I, v i * v j * ((min i.val j.val : ℝ≥0) : ℝ) := by
  unfold weightedCoordinate
  rw [variance_fun_sum (fun i => (memLp_eval_projectiveFamily I i).mul_const (v i))]
  simp only [covariance_mul_const_left, covariance_mul_const_right,
    BrownianReal.covariance_eval_projectiveFamily]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The exact Gaussian law of any finite-dimensional Brownian projection,
including degenerate projections with variance zero. -/
theorem map_weightedCoordinate_projectiveFamily (I : Finset ℝ≥0) (v : I → ℝ) :
    (BrownianReal.projectiveFamily I).map (weightedCoordinate v) = gaussianReal 0
      (variance (weightedCoordinate v) (BrownianReal.projectiveFamily I)).toNNReal := by
  let f : (I → ℝ) →L[ℝ] ℝ := ∑ i : I, v i • ContinuousLinearMap.proj i
  have heq : (f : (I → ℝ) → ℝ) = weightedCoordinate v := by
    funext x
    simp only [f, sum_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, weightedCoordinate]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have h := IsGaussian.map_eq_gaussianReal (μ := BrownianReal.projectiveFamily I) f
  rw [heq, integral_weightedCoordinate_projectiveFamily] at h
  exact h

end Critical2DKPZ.Extensions.ScaleLimit
