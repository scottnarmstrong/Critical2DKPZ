/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25FiniteOperators
import Mathlib.Tactic

/-! # Composition of finite-support lattice kernels -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

/-- Reassociate two kernel sums when the first kernel and the second kernel
have finite endpoint support. This is the finite-state Fubini step used to
group consecutive collision events into one interaction run. -/
theorem tsum_mul_tsum_eq_tsum_composed_of_finSupport {α : Type*}
    [DecidableEq α] (S : Finset α) (T : α → Finset α)
    (K : α → ℝ) (H : α → α → ℝ) (f : α → ℝ)
    (hK : ∀ y ∉ S, K y = 0)
    (hH : ∀ y ∈ S, ∀ x ∉ T y, H y x = 0) :
    (∑' y, K y * (∑' x, H y x * f x)) =
      ∑' x, (∑' y, K y * H y x) * f x := by
  classical
  let U : Finset α := S.biUnion T
  have hleft :
      (∑' y, K y * (∑' x, H y x * f x)) =
        ∑ y ∈ S, K y * (∑ x ∈ U, H y x * f x) := by
    rw [tsum_eq_sum (s := S) (fun y hy => by rw [hK y hy]; simp)]
    apply Finset.sum_congr rfl
    intro y hy
    rw [tsum_eq_sum (s := U) (fun x hx => by
      have hx' : x ∉ T y := by
        intro hxy
        exact hx (Finset.mem_biUnion.mpr ⟨y, hy, hxy⟩)
      rw [hH y hy x hx']; simp)]
  have hswap :
      (∑ y ∈ S, K y * (∑ x ∈ U, H y x * f x)) =
        ∑ x ∈ U, (∑ y ∈ S, K y * H y x) * f x := by
    calc
      _ = ∑ y ∈ S, ∑ x ∈ U, (K y * H y x) * f x := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = ∑ x ∈ U, ∑ y ∈ S, (K y * H y x) * f x := Finset.sum_comm
      _ = ∑ x ∈ U, (∑ y ∈ S, K y * H y x) * f x := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.sum_mul]
  have hcompose (x : α) :
      (∑' y, K y * H y x) = ∑ y ∈ S, K y * H y x :=
    tsum_eq_sum (s := S) (fun y hy => by rw [hK y hy]; simp)
  have hzero (x : α) (hx : x ∉ U) :
      (∑' y, K y * H y x) = 0 := by
    rw [hcompose]
    apply Finset.sum_eq_zero
    intro y hy
    have hx' : x ∉ T y := by
      intro hxy
      exact hx (Finset.mem_biUnion.mpr ⟨y, hy, hxy⟩)
    rw [hH y hy x hx']
    simp
  calc
    _ = ∑ x ∈ U, (∑ y ∈ S, K y * H y x) * f x := hleft.trans hswap
    _ = ∑ x ∈ U, (∑' y, K y * H y x) * f x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hcompose]
    _ = ∑' x, (∑' y, K y * H y x) * f x := by
      symm
      exact tsum_eq_sum (s := U) (fun x hx => by rw [hzero x hx]; simp)

end Critical2DKPZ.MomentBounds

end
