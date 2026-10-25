/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.CollisionRunExpansion
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # Positivity for collision-word kernels -/

@[expose] public section

noncomputable section

open scoped BigOperators CompactlySupported
open MeasureTheory

namespace Critical2DKPZ.SHF.Moments

open Polymer DeltaBose

/-- The cell test weight is nonnegative for a nonnegative test function. -/
theorem cellTestWeight_nonneg (N : ℕ) (φ : C_c(Plane × Plane, ℝ))
    (hφ : ∀ p, 0 ≤ φ p) (w z : Site) :
    0 ≤ cellTestWeight N φ w z := by
  unfold cellTestWeight
  apply mul_nonneg (by positivity)
  exact integral_nonneg (fun p => hφ p)

/-- The tested block word is nonnegative for nonnegative test functions. -/
theorem testedBlockWord_nonneg (ϑ : ℝ) (N : ℕ) (s t : ℝ) {h : ℕ}
    (φ : Fin h → C_c(Plane × Plane, ℝ))
    (hφ : ∀ i p, 0 ≤ φ i p) (w : List (CollisionPair h)) :
    0 ≤ testedBlockWord ϑ N s t φ w := by
  unfold testedBlockWord
  apply tsum_nonneg
  intro x
  apply tsum_nonneg
  intro y
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro i hi
    exact cellTestWeight_nonneg N (φ i) (hφ i) (x i) (y i)
  · have hσ : 0 ≤ Polymer.sigmaSq (criticalBeta ϑ N) := by
      unfold Polymer.sigmaSq
      exact sub_nonneg.mpr (Real.one_le_exp (sq_nonneg _))
    exact blockWordKernel_nonneg (Polymer.sigmaSq (criticalBeta ϑ N)) hσ w
      (evenCeil (N * t) - evenCeil (N * s)) x y

/-- The tested non-pair remainder is nonnegative for nonnegative test functions. -/
theorem testedNonpairRemainder_nonneg (ϑ : ℝ) (N : ℕ) (s t : ℝ) {h : ℕ}
    (φ : Fin h → C_c(Plane × Plane, ℝ)) (hφ : ∀ i p, 0 ≤ φ i p) :
    0 ≤ testedNonpairRemainder ϑ N s t φ := by
  unfold testedNonpairRemainder
  apply tsum_nonneg
  intro x
  apply tsum_nonneg
  intro y
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro i hi
    exact cellTestWeight_nonneg N (φ i) (hφ i) (x i) (y i)
  · exact nonpairCollisionRemainder_nonneg (criticalBeta ϑ N)
      (evenCeil (N * t) - evenCeil (N * s)) h x y

end Critical2DKPZ.SHF.Moments

end
