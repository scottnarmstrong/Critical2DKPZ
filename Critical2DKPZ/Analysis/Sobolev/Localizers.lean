/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.TestFn
public import Critical2DKPZ.Definitions.Plane
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# A countable exhaustion by smooth localizers

The localizer with index `n` is one on the ball of radius `n+1`, supported in the ball of radius
`n+2`, and takes values in `[0,1]`. Every fixed compact set is eventually in its one region.
-/

@[expose] public section

noncomputable section

open Set

namespace Critical2DKPZ

/-- The explicit bump underlying the countable cutoff exhaustion. -/
def localizerBump (n : ℕ) : ContDiffBump (0 : Plane) where
  rIn := (n : ℝ) + 1
  rOut := (n : ℝ) + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- A countable family of real smooth compactly supported test functions equal to one on increasing balls. -/
def localizer (n : ℕ) : TestFn where
  toFun := localizerBump n
  contDiff' := (localizerBump n).contDiff
  hasCompactSupport' := (localizerBump n).hasCompactSupport
  tsupport_subset' := subset_univ _

/-- Each localizer is nonnegative. -/
theorem localizer_nonneg (n : ℕ) (x : Plane) : 0 ≤ localizer n x :=
  (localizerBump n).nonneg

/-- Each localizer is bounded above by one. -/
theorem localizer_le_one (n : ℕ) (x : Plane) : localizer n x ≤ 1 :=
  (localizerBump n).le_one

/-- A localizer equals one on its inner closed ball. -/
theorem localizer_eq_one_of_mem_closedBall (n : ℕ) {x : Plane}
    (hx : x ∈ Metric.closedBall 0 ((n : ℝ) + 1)) : localizer n x = 1 :=
  (localizerBump n).one_of_mem_closedBall hx

/-- The support of a localizer is its outer closed ball. -/
theorem tsupport_localizer (n : ℕ) :
    tsupport (localizer n) = Metric.closedBall (0 : Plane) ((n : ℝ) + 2) :=
  (localizerBump n).tsupport_eq

/-- Every compact set is eventually contained in the region where the localizer is one. -/
theorem exists_localizer_eq_one_on_compact {K : Set Plane} (hK : IsCompact K) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ K, localizer n x = 1 := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Plane)
  obtain ⟨N, hN⟩ := exists_nat_gt R
  refine ⟨N, fun n hn x hx => localizer_eq_one_of_mem_closedBall n ?_⟩
  apply Metric.closedBall_subset_closedBall _ (hR hx)
  exact hN.le.trans ((Nat.cast_le.mpr hn).trans (le_add_of_nonneg_right zero_le_one))

/-- Every test function is eventually unchanged by multiplication with these cutoffs. -/
theorem exists_localizer_mul_testFn_eq (φ : TestFn) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x : Plane, localizer n x * φ x = φ x := by
  obtain ⟨N, hN⟩ := exists_localizer_eq_one_on_compact φ.hasCompactSupport.isCompact
  refine ⟨N, fun n hn x => ?_⟩
  by_cases hx : φ x = 0
  · rw [hx, mul_zero]
  · rw [hN n hn x (subset_tsupport φ hx), one_mul]

end Critical2DKPZ

end
