/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitTerminalRecursion
import Mathlib.Tactic

/-! # Terminal recursion for arbitrary profiles

The entire word has finite endpoint support, so the first-letter recursion
also applies to the constant profile used for total-mass estimates.
-/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

private theorem run_tail_endpoint_mem {h : ℕ} (β : ℝ) (α : CollisionPair h)
    (w : List (CollisionPair h)) (s r m : ℕ) (x u v y : LatticeConfiguration h)
    (hfree : (∏ i, srwKernel s (u i - x i)) ≠ 0)
    (hrun : collisionWordUndampedPairRunFactor β α r u v ≠ 0)
    (htail : blockWordKernel (sigmaSq β) w m v y ≠ 0) :
    y ∈ collisionWordConfigurationEndpointSet (s + r + m) x := by
  have hu : u ∈ collisionWordConfigurationEndpointSet s x := by
    by_contra hnot
    exact hfree (collisionWord_freeProduct_zero_of_not_endpoints s x u hnot)
  have hv : v ∈ collisionWordConfigurationEndpointSet r u := by
    by_contra hnot
    exact hrun (collisionWord_runFactor_zero_of_not_endpoints β α r u v hnot)
  have hy : y ∈ collisionWordConfigurationEndpointSet m v := by
    by_contra hnot
    exact htail (blockWordKernel_zero_of_endpoint_not_mem (sigmaSq β) w m v y hnot)
  apply Fintype.mem_piFinset.mpr
  intro i
  exact endpoints_compose_collisionRun
    (endpoints_compose_collisionRun (Fintype.mem_piFinset.mp hu i)
      (Fintype.mem_piFinset.mp hv i)) (Fintype.mem_piFinset.mp hy i)

/-- The first-letter terminal pairing identity holds for every terminal profile:
the finite reachable endpoint set supplies its truncation. -/
theorem blockWordKernel_cons_terminalPairing_eq_arbitrary {h : ℕ} (β : ℝ)
    (α : CollisionPair h) (w : List (CollisionPair h)) (n : ℕ)
    (x : LatticeConfiguration h) (P : LatticeConfiguration h → ℝ) :
    (∑' y : LatticeConfiguration h,
      blockWordKernel (sigmaSq β) (α :: w) n x y * P y) =
      ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
        ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
          ((∏ i, srwKernel s (u i - x i)) *
            collisionWordUndampedPairRunFactor β α r u v) *
            (∑' y : LatticeConfiguration h,
              blockWordKernel (sigmaSq β) w (n - s - r) v y * P y) := by
  classical
  let Z := collisionWordConfigurationEndpointSet n x
  let Q : LatticeConfiguration h → ℝ := fun y => if y ∈ Z then P y else 0
  have hQ : (Function.support Q).Finite := by
    apply Z.finite_toSet.subset
    intro y hy
    by_contra hnot
    exact hy (by simp [Q, show y ∉ Z from hnot])
  have hleft :
      (∑' y : LatticeConfiguration h,
        blockWordKernel (sigmaSq β) (α :: w) n x y * P y) =
      ∑' y : LatticeConfiguration h,
        blockWordKernel (sigmaSq β) (α :: w) n x y * Q y := by
    apply tsum_congr
    intro y
    by_cases hy : y ∈ Z
    · simp only [Q, ite_eq_left hy]
    · rw [blockWordKernel_zero_of_endpoint_not_mem (sigmaSq β) (α :: w) n x y hy]
      simp only [zero_mul]
  refine hleft.trans ((blockWordKernel_cons_terminalPairing_eq β α w n x Q hQ).trans ?_)
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro r hr
  have hduration : s + r + (n - s - r) = n := by
    have hs' := Finset.mem_Icc.mp hs
    have hr' := Finset.mem_range.mp hr
    omega
  apply tsum_congr
  intro u
  apply tsum_congr
  intro v
  by_cases hfree : (∏ i, srwKernel s (u i - x i)) = 0
  · simp only [hfree, zero_mul]
  by_cases hrun : collisionWordUndampedPairRunFactor β α r u v = 0
  · simp only [hrun, mul_zero, zero_mul]
  apply congrArg (fun z : ℝ =>
    ((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) * z)
  apply tsum_congr
  intro y
  by_cases htail : blockWordKernel (sigmaSq β) w (n - s - r) v y = 0
  · simp only [htail, zero_mul]
  have hy : y ∈ Z := by
    have hmem := run_tail_endpoint_mem β α w s r (n - s - r) x u v y hfree hrun htail
    simpa only [hduration] using hmem
  simp only [Q, ite_eq_left hy]

/-- Peeling a collision letter in the fixed-start terminal functional is exact,
including for the constant terminal profile. -/
theorem wordTerminalTest_cons {h : ℕ} (N : ℕ) (β : ℝ)
    (α : CollisionPair h) (w : List (CollisionPair h)) (n : ℕ)
    (x : LatticeConfiguration h) (Ψ : Configuration h → ℝ) :
    wordTerminalTest N (sigmaSq β) (α :: w) n x Ψ =
      ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
        ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
          ((∏ i, srwKernel s (u i - x i)) *
            collisionWordUndampedPairRunFactor β α r u v) *
            wordTerminalTest N (sigmaSq β) w (n - s - r) v Ψ :=
  blockWordKernel_cons_terminalPairing_eq_arbitrary β α w n x _

end Critical2DKPZ.SHF.Moments
