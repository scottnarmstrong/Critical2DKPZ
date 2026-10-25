/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitTerminalFirstBlock
public import Critical2DKPZ.SHF.Moments.WordLimitSubsetFirstBlock

/-! # The positive first-block endpoint kernel for word induction -/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- A first collision block with its entrance and run durations fixed. -/
def wordFirstBlockKernel {h : ℕ} (β : ℝ) (α : CollisionPair h) (s r : ℕ)
    (x v : LatticeConfiguration h) : ℝ :=
  ∑ u ∈ collisionWordConfigurationEndpointSet s x,
    (∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v

/-- The first-block endpoint kernel is nonnegative. -/
theorem wordFirstBlockKernel_nonneg {h : ℕ} (β : ℝ) (α : CollisionPair h)
    (s r : ℕ) (x v : LatticeConfiguration h) : 0 ≤ wordFirstBlockKernel β α s r x v := by
  apply Finset.sum_nonneg
  intro u hu
  have hrun : 0 ≤ collisionWordUndampedPairRunFactor β α r u v := by
    rw [collisionWordUndampedPairRunFactor, pairRunFactor_eq_sigmaSq_mul_interactingReplicaKernelAbs]
    exact mul_nonneg (sigmaSq_nonneg β)
      (interactingReplicaKernelAbs_nonneg β (pairPartition α) r u v)
  exact mul_nonneg (Finset.prod_nonneg (fun i _ => srwKernel_nonneg _ _)) hrun

/-- The mass of a fixed first block is exactly its entrance walk times
its scalar renewal mass. -/
theorem sum_wordFirstBlockKernel {h : ℕ} (β : ℝ) (α : CollisionPair h)
    (s r : ℕ) (x : LatticeConfiguration h) :
    (∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x, wordFirstBlockKernel β α s r x v) =
      srwKernel (2 * s) (x α.1.2 - x α.1.1) *
        (sigmaSq β * Renewal.renewalMass
          (fun k => sigmaSq β * Renewal.returnWeight k) r) :=
  sum_free_run_total_mass β α s r x

/-- The first-block kernel factors over any selected set containing its collision. -/
theorem wordFirstBlockKernel_subset_factor {h : ℕ} (S : Finset (Fin h))
    (β : ℝ) (α : CollisionPair h) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S)
    (s r : ℕ) (x v : LatticeConfiguration h) :
    wordFirstBlockKernel β α s r x v =
      wordFirstBlockKernel β (Tsai.collisionPairWithin S α h₁ h₂) s r
        (fun j => x (S.orderEmbOfFin rfl j)) (fun j => v (S.orderEmbOfFin rfl j)) *
      ∏ j : Fin Sᶜ.card, srwKernel (s + r)
        (v (Sᶜ.orderEmbOfFin rfl j) - x (Sᶜ.orderEmbOfFin rfl j)) :=
  sum_free_run_subset_factor S β α h₁ h₂ s r x v

/-- The word recursion is terminal testing of its first-block endpoint kernel. -/
theorem wordTerminalTest_cons_firstBlock {h : ℕ} (N : ℕ) (β : ℝ)
    (α : CollisionPair h) (w : List (CollisionPair h)) (n : ℕ)
    (x : LatticeConfiguration h) (Ψ : Configuration h → ℝ) :
    wordTerminalTest N (sigmaSq β) (α :: w) n x Ψ =
      ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
        ∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
          wordFirstBlockKernel β α s r x v *
            wordTerminalTest N (sigmaSq β) w (n - s - r) v Ψ :=
  wordTerminalTest_cons_total_endpoints N β α w n x Ψ

end Critical2DKPZ.SHF.Moments
