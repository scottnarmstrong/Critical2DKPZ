/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring

/-! # Linearity of the finite three-factor pairing -/

@[expose] public noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- A finite boundary followed by two finite transition kernels. -/
def finiteThreeFactorPairing {α : Type*} (s : Finset α) (A : α → ℝ)
    (K Q : α → α → ℝ) : ℝ :=
  ∑ x ∈ s, A x * ∑ y ∈ s, K x y * ∑ z ∈ s, Q y z

/-- Linearity in the boundary. -/
theorem finiteThreeFactorPairing_sum_left {α ι : Type*} (s : Finset α) (I : Finset ι)
    (A : ι → α → ℝ) (K Q : α → α → ℝ) :
    finiteThreeFactorPairing s (fun x => ∑ i ∈ I, A i x) K Q =
      ∑ i ∈ I, finiteThreeFactorPairing s (A i) K Q := by
  unfold finiteThreeFactorPairing
  simp_rw [Finset.sum_mul]
  exact Finset.sum_comm

/-- Linearity in the first transition kernel. -/
theorem finiteThreeFactorPairing_sum_middle {α ι : Type*} (s : Finset α) (I : Finset ι)
    (A : α → ℝ) (K : ι → α → α → ℝ) (Q : α → α → ℝ) :
    finiteThreeFactorPairing s A (fun x y => ∑ i ∈ I, K i x y) Q =
      ∑ i ∈ I, finiteThreeFactorPairing s A (K i) Q := by
  have he (x : α) :
      (∑ y ∈ s, (∑ i ∈ I, K i x y) * ∑ z ∈ s, Q y z) =
        ∑ i ∈ I, ∑ y ∈ s, K i x y * ∑ z ∈ s, Q y z := by
    simp_rw [Finset.sum_mul]
    exact Finset.sum_comm
  unfold finiteThreeFactorPairing
  simp_rw [he, Finset.mul_sum]
  exact Finset.sum_comm

/-- Linearity in the second transition kernel. -/
theorem finiteThreeFactorPairing_sum_right {α ι : Type*} (s : Finset α) (I : Finset ι)
    (A : α → ℝ) (K : α → α → ℝ) (Q : ι → α → α → ℝ) :
    finiteThreeFactorPairing s A K (fun y z => ∑ i ∈ I, Q i y z) =
      ∑ i ∈ I, finiteThreeFactorPairing s A K (Q i) := by
  have hi (y : α) : (∑ z ∈ s, ∑ i ∈ I, Q i y z) =
      ∑ i ∈ I, ∑ z ∈ s, Q i y z := Finset.sum_comm
  have he (x : α) :
      (∑ y ∈ s, K x y * ∑ i ∈ I, ∑ z ∈ s, Q i y z) =
        ∑ i ∈ I, ∑ y ∈ s, K x y * ∑ z ∈ s, Q i y z := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  unfold finiteThreeFactorPairing
  simp_rw [hi, he, Finset.mul_sum]
  exact Finset.sum_comm

end Critical2DKPZ.Extensions.GffTangent
