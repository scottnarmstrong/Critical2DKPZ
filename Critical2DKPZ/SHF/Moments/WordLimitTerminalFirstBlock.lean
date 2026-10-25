/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitFirstBlockTerminal

/-! # The terminal word recursion through its first-block endpoint kernel -/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- The unrestricted spatial recursion is a finite terminal test of the
first block on its total reachable endpoint set. -/
theorem tsum_free_run_terminal_eq {h : ℕ} (β : ℝ) (α : CollisionPair h)
    (s r : ℕ) (x : LatticeConfiguration h) (H : LatticeConfiguration h → ℝ) :
    (∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
      ((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) * H v) =
      ∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
        (∑ u ∈ collisionWordConfigurationEndpointSet s x,
          (∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) * H v := by
  have houter :
      (∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
        ((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) * H v) =
      ∑ u ∈ collisionWordConfigurationEndpointSet s x, ∑' v : LatticeConfiguration h,
        ((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) * H v := by
    apply tsum_eq_sum
    intro u hu
    simp only [collisionWord_freeProduct_zero_of_not_endpoints s x u hu, zero_mul, tsum_zero]
  calc
    _ = ∑ u ∈ collisionWordConfigurationEndpointSet s x,
        ∑ v ∈ collisionWordConfigurationEndpointSet r u,
          ((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) * H v := by
      rw [houter]
      apply Finset.sum_congr rfl
      intro u hu
      apply tsum_eq_sum
      intro v hv
      rw [collisionWord_runFactor_zero_of_not_endpoints β α r u v hv, mul_zero, zero_mul]
    _ = _ := sum_free_run_terminal_eq β α s r x H

/-- Peeling a word leaves its tail tested against the first-block endpoint
kernel. Its spectator factorization is available before summing durations. -/
theorem wordTerminalTest_cons_total_endpoints {h : ℕ} (N : ℕ) (β : ℝ)
    (α : CollisionPair h) (w : List (CollisionPair h)) (n : ℕ)
    (x : LatticeConfiguration h) (Ψ : Configuration h → ℝ) :
    wordTerminalTest N (sigmaSq β) (α :: w) n x Ψ =
      ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
        ∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
          (∑ u ∈ collisionWordConfigurationEndpointSet s x,
            (∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) *
              wordTerminalTest N (sigmaSq β) w (n - s - r) v Ψ := by
  rw [wordTerminalTest_cons]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro r hr
  exact tsum_free_run_terminal_eq β α s r x
    (fun v => wordTerminalTest N (sigmaSq β) w (n - s - r) v Ψ)

end Critical2DKPZ.SHF.Moments
