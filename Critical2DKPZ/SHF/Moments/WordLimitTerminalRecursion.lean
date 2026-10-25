/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitTerminal
public import Critical2DKPZ.SHF.Moments.WordDominationTerminalRecursion
import Mathlib.Tactic

/-! # First-letter recursion for terminal tests

The free and run endpoint cutoffs make the interchange of the three spatial
sums an interchange of an absolutely summable family.
-/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

private theorem summable_run_terminal_family {h : ℕ} (β : ℝ)
    (α : CollisionPair h) (w : List (CollisionPair h)) (s r m : ℕ)
    (x : LatticeConfiguration h) (P : LatticeConfiguration h → ℝ)
    (hP : (Function.support P).Finite) :
    Summable (fun p : LatticeConfiguration h ×
        (LatticeConfiguration h × LatticeConfiguration h) =>
      ((∏ i, srwKernel s (p.2.1 i - x i)) *
        collisionWordUndampedPairRunFactor β α r p.2.1 p.2.2) *
          (blockWordKernel (sigmaSq β) w m p.2.2 p.1 * P p.1)) := by
  classical
  let U := collisionWordConfigurationEndpointSet s x
  let V := U.biUnion (fun u => collisionWordConfigurationEndpointSet r u)
  let Z := hP.toFinset
  apply summable_of_ne_finset_zero (s := Z ×ˢ (U ×ˢ V))
  rintro ⟨z, u, v⟩ hp
  by_cases hz : z ∈ Z
  · by_cases hu : u ∈ U
    · have hv : v ∉ V := by simpa only [Finset.mem_product, hz, hu, true_and] using hp
      have hvr : v ∉ collisionWordConfigurationEndpointSet r u := by
        intro hmem
        exact hv (Finset.mem_biUnion.mpr ⟨u, hu, hmem⟩)
      rw [collisionWord_runFactor_zero_of_not_endpoints β α r u v hvr]
      simp only [mul_zero, zero_mul]
    · rw [collisionWord_freeProduct_zero_of_not_endpoints s x u hu]
      simp only [zero_mul]
  · have hzero : P z = 0 := by
      by_contra hne
      exact hz (hP.mem_toFinset.mpr hne)
    rw [hzero]
    simp only [mul_zero]

/-- A finitely supported terminal profile can be passed through the first collision block. -/
theorem blockWordKernel_cons_terminalPairing_eq {h : ℕ} (β : ℝ)
    (α : CollisionPair h) (w : List (CollisionPair h)) (n : ℕ)
    (x : LatticeConfiguration h) (P : LatticeConfiguration h → ℝ)
    (hP : (Function.support P).Finite) :
    (∑' y : LatticeConfiguration h,
      blockWordKernel (sigmaSq β) (α :: w) n x y * P y) =
      ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
        ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
          ((∏ i, srwKernel s (u i - x i)) *
            collisionWordUndampedPairRunFactor β α r u v) *
            (∑' y : LatticeConfiguration h,
              blockWordKernel (sigmaSq β) w (n - s - r) v y * P y) := by
  classical
  let Z := hP.toFinset
  let F : ℕ → ℕ → LatticeConfiguration h →
      (LatticeConfiguration h × LatticeConfiguration h) → ℝ := fun s r y uv =>
    ((∏ i, srwKernel s (uv.1 i - x i)) *
      collisionWordUndampedPairRunFactor β α r uv.1 uv.2) *
      (blockWordKernel (sigmaSq β) w (n - s - r) uv.2 y * P y)
  have hPzero (y : LatticeConfiguration h) (hy : y ∉ Z) : P y = 0 := by
    by_contra hne
    exact hy (hP.mem_toFinset.mpr hne)
  have hweighted (y : LatticeConfiguration h) :
      blockWordKernel (sigmaSq β) (α :: w) n x y * P y =
        ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
          ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
            F s r y (u, v) := by
    rw [blockWordKernel, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    rw [← tsum_mul_right]
    apply tsum_congr
    intro u
    rw [← tsum_mul_right]
    apply tsum_congr
    intro v
    dsimp only [F, collisionWordUndampedPairRunFactor]
    ring
  have hswap (s r : ℕ) :
      (∑' y : LatticeConfiguration h, ∑' u : LatticeConfiguration h,
        ∑' v : LatticeConfiguration h, F s r y (u, v)) =
        ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
          ∑' y : LatticeConfiguration h, F s r y (u, v) := by
    have hsum : Summable (Function.uncurry (F s r)) :=
      summable_run_terminal_family β α w s r (n - s - r) x P hP
    calc
      _ = ∑' y : LatticeConfiguration h,
          ∑' uv : LatticeConfiguration h × LatticeConfiguration h, F s r y uv := by
        apply tsum_congr
        intro y
        exact (hsum.prod_factor y).tsum_prod.symm
      _ = ∑' uv : LatticeConfiguration h × LatticeConfiguration h,
          ∑' y : LatticeConfiguration h, F s r y uv := hsum.tsum_comm.symm
      _ = _ := hsum.prod_symm.prod.tsum_prod
  calc
    _ = ∑ y ∈ Z, blockWordKernel (sigmaSq β) (α :: w) n x y * P y := by
      apply tsum_eq_sum
      intro y hy
      rw [hPzero y hy, mul_zero]
    _ = ∑ y ∈ Z, ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
          ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
            F s r y (u, v) := by
      apply Finset.sum_congr rfl
      intro y hy
      exact hweighted y
    _ = ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
          ∑ y ∈ Z, ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
            F s r y (u, v) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      exact Finset.sum_comm
    _ = ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
          ∑' y : LatticeConfiguration h, ∑' u : LatticeConfiguration h,
            ∑' v : LatticeConfiguration h, F s r y (u, v) := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro r hr
      symm
      apply tsum_eq_sum
      intro y hy
      simp only [F, hPzero y hy, mul_zero, tsum_zero]
    _ = ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
          ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
            ∑' y : LatticeConfiguration h, F s r y (u, v) := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro r hr
      exact hswap s r
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro r hr
      apply tsum_congr
      intro u
      apply tsum_congr
      intro v
      exact tsum_mul_left


end Critical2DKPZ.SHF.Moments
