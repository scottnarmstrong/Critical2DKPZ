/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationBlockWordSupport
public import Critical2DKPZ.SHF.Moments.CollisionRunExpansion
import Critical2DKPZ.MomentBounds.CCR25IndependentDurationSum
import Critical2DKPZ.Polymer.Profiles
import Mathlib.Tactic

/-! # Terminal tests for the induction over collision words

The starting configuration is fixed. Only the terminal configuration is tested,
at its diffusive lattice representative. Every terminal sum has finite support.
-/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

/-- The terminally tested lattice word kernel at a fixed starting configuration. -/
def wordTerminalTest {h : ℕ} (N : ℕ) (σ : ℝ) (w : List (CollisionPair h))
    (n : ℕ) (x : Fin h → Site) (Ψ : Configuration h → ℝ) : ℝ :=
  ∑' y : Fin h → Site,
    blockWordKernel σ w n x y * Ψ (fun i => latticeRepresentative N (y i))


/-- The terminal test is exactly a sum over the reachable endpoint configurations. -/
theorem wordTerminalTest_eq_sum {h : ℕ} (N : ℕ) (σ : ℝ)
    (w : List (CollisionPair h)) (n : ℕ) (x : Fin h → Site)
    (Ψ : Configuration h → ℝ) :
    wordTerminalTest N σ w n x Ψ =
      ∑ y ∈ collisionWordConfigurationEndpointSet n x,
        blockWordKernel σ w n x y * Ψ (fun i => latticeRepresentative N (y i)) := by
  classical
  apply tsum_eq_sum
  intro y hy
  rw [blockWordKernel_zero_of_endpoint_not_mem σ w n x y hy, zero_mul]

/-- Nonnegative terminal profiles give nonnegative word tests. -/
theorem wordTerminalTest_nonneg {h : ℕ} (N : ℕ) {σ : ℝ} (hσ : 0 ≤ σ)
    (w : List (CollisionPair h)) (n : ℕ) (x : Fin h → Site)
    (Ψ : Configuration h → ℝ) (hΨ : ∀ y, 0 ≤ Ψ y) :
    0 ≤ wordTerminalTest N σ w n x Ψ := by
  apply tsum_nonneg
  intro y
  exact mul_nonneg (blockWordKernel_nonneg σ hσ w n x y) (hΨ _)

/-- The total row mass controls the terminal test of any uniformly bounded profile. -/
theorem abs_wordTerminalTest_le_mass {h : ℕ} (N : ℕ) {σ : ℝ} (hσ : 0 ≤ σ)
    (w : List (CollisionPair h)) (n : ℕ) (x : Fin h → Site)
    (Ψ : Configuration h → ℝ) {M : ℝ} (hΨ : ∀ y, |Ψ y| ≤ M) :
    |wordTerminalTest N σ w n x Ψ| ≤
      M * wordTerminalTest N σ w n x (fun _ => 1) := by
  classical
  rw [wordTerminalTest_eq_sum, wordTerminalTest_eq_sum]
  calc
    _ ≤ ∑ y ∈ collisionWordConfigurationEndpointSet n x,
        |blockWordKernel σ w n x y * Ψ (fun i => latticeRepresentative N (y i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ collisionWordConfigurationEndpointSet n x, M * blockWordKernel σ w n x y := by
      apply Finset.sum_le_sum
      intro y hy
      rw [abs_mul, abs_of_nonneg (blockWordKernel_nonneg σ hσ w n x y)]
      exact (mul_le_mul_of_nonneg_left (hΨ _)
        (blockWordKernel_nonneg σ hσ w n x y)).trans_eq (mul_comm _ _)
    _ = _ := by simp only [mul_one, Finset.mul_sum]

/-- At the empty word, tensor terminal tests factor into independent walk tests. -/
theorem wordTerminalTest_nil_tensor {h : ℕ} (N : ℕ) (σ : ℝ)
    (n : ℕ) (x : Fin h → Site) (ψ : Fin h → Plane → ℝ) :
    wordTerminalTest N σ [] n x (fun y => ∏ i, ψ i (y i)) =
      ∏ i : Fin h, ∑ z ∈ endpoints (x i) n,
        srwKernel n (z - x i) * ψ i (latticeRepresentative N z) := by
  classical
  rw [wordTerminalTest_eq_sum]
  simp only [collisionWordConfigurationEndpointSet, blockWordKernel]
  calc
    _ = ∑ y ∈ Fintype.piFinset (fun i => endpoints (x i) n),
          ∏ i, srwKernel n (y i - x i) * ψ i (latticeRepresentative N (y i)) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.prod_mul_distrib]
    _ = _ :=
      Critical2DKPZ.MomentBounds.finite_sum_product_over_piFinset_eq_product_sums
        (fun i => endpoints (x i) n)
        (fun i z => srwKernel n (z - x i) * ψ i (latticeRepresentative N z))

/-- The empty-word row has total mass one for every starting configuration. -/
theorem wordTerminalTest_nil_one {h : ℕ} (N : ℕ) (σ : ℝ)
    (n : ℕ) (x : Fin h → Site) :
    wordTerminalTest N σ [] n x (fun _ => 1) = 1 := by
  have h := wordTerminalTest_nil_tensor N σ n x (fun _ _ => 1)
  simpa only [Finset.prod_const_one, mul_one, sum_srwKernel_endpoints] using h

end Critical2DKPZ.SHF.Moments
