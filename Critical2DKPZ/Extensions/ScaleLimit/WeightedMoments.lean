/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BrownianProjections
import Mathlib.Tactic

/-! # Variances of scalar projections of finite random vectors -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A finite projected variance is the double sum of weighted covariances. -/
theorem variance_weightedCoordinate {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : I → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 P) (v : I → ℝ) :
    variance (fun ω => weightedCoordinate v (fun i => X i ω)) P =
      ∑ i, ∑ j, covariance (X i) (X j) P * v i * v j := by
  change variance (fun ω => ∑ i, X i ω * v i) P = _
  rw [variance_fun_sum (fun i => (hX i).mul_const (v i))]
  simp only [covariance_mul_const_left, covariance_mul_const_right]

end Critical2DKPZ.Extensions.ScaleLimit
