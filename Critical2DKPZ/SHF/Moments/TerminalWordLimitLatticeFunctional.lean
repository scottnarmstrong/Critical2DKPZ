/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSpatialLattice
public import Critical2DKPZ.SHF.Moments.WordLimitTerminalFirstBlock
import Mathlib.Tactic

/-! # Finite cutoff functionals for first-letter limits -/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- Endpoint support makes a spatially weighted first block a finite sum,
even when its two-variable weight has no support or regularity assumptions. -/
theorem tsum_free_run_weighted_eq_sum {h : ℕ} (β : ℝ) (α : CollisionPair h)
    (s r : ℕ) (x : LatticeConfiguration h)
    (H : LatticeConfiguration h → LatticeConfiguration h → ℝ) :
    (∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
      ((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) * H u v) =
      ∑ u ∈ collisionWordConfigurationEndpointSet s x, ∑ v ∈ collisionWordConfigurationEndpointSet r u,
        ((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) * H u v := by
  have houter :
      (∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
        ((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) * H u v) =
      ∑ u ∈ collisionWordConfigurationEndpointSet s x, ∑' v : LatticeConfiguration h,
        ((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) * H u v := by
    apply tsum_eq_sum
    intro u hu
    simp only [collisionWord_freeProduct_zero_of_not_endpoints s x u hu, zero_mul, tsum_zero]
  rw [houter]
  apply Finset.sum_congr rfl
  intro u hu
  apply tsum_eq_sum
  intro v hv
  rw [collisionWord_runFactor_zero_of_not_endpoints β α r u v hv, mul_zero, zero_mul]

/-- The original first-letter expansion with a time weight and a spatial
weight. All sums use finite reachable supports. -/
def wordFirstLetterLatticeFunctional {h : ℕ} (N : ℕ) (β : ℝ) (α : CollisionPair h)
    (w : List (CollisionPair h)) (n : ℕ) (x : LatticeConfiguration h)
    (Ψ : Configuration h → ℝ) (κ : ℕ → ℕ → ℝ)
    (χ : (FusedConfiguration α × FusedConfiguration α) → ℝ) : ℝ :=
  ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1), κ s r *
    ∑ u ∈ collisionWordConfigurationEndpointSet s x, ∑ v ∈ collisionWordConfigurationEndpointSet r u,
      χ (wordFusedCoordinateRepresentative N α (wordFusedSiteProjection α u),
        wordFusedCoordinateRepresentative N α (wordFusedSiteProjection α v)) *
        (((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) *
          wordTerminalTest N (sigmaSq β) w (n - s - r) v Ψ)

/-- Unit weights recover the exact first-letter terminal test. -/
theorem wordFirstLetterLatticeFunctional_one_one {h : ℕ} (N : ℕ) (β : ℝ)
    (α : CollisionPair h) (w : List (CollisionPair h)) (n : ℕ)
    (x : LatticeConfiguration h) (Ψ : Configuration h → ℝ) :
    wordFirstLetterLatticeFunctional N β α w n x Ψ (fun _ _ => 1) (fun _ => 1) =
      wordTerminalTest N (sigmaSq β) (α :: w) n x Ψ := by
  rw [wordTerminalTest_cons]
  unfold wordFirstLetterLatticeFunctional
  simp only [one_mul]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro r hr
  exact (tsum_free_run_weighted_eq_sum β α s r x
    (fun _ v => wordTerminalTest N (sigmaSq β) w (n - s - r) v Ψ)).symm

/-- Terminal testing of a constant profile is that constant times row mass. -/
theorem wordTerminalTest_const {h : ℕ} (N : ℕ) (σ : ℝ) (w : List (CollisionPair h))
    (n : ℕ) (x : LatticeConfiguration h) (M : ℝ) :
    wordTerminalTest N σ w n x (fun _ => M) = M * wordTerminalTest N σ w n x (fun _ => 1) := by
  simp only [wordTerminalTest, mul_one, tsum_mul_right]
  ring

/-- A fitted first-letter spatial cutoff equals its finite endpoint sum
before any time weights are inserted. -/
theorem wordFirstLetterLatticeFunctional_eq_tsum {h : ℕ} (N : ℕ) (β : ℝ)
    (α : CollisionPair h) (w : List (CollisionPair h)) (n : ℕ)
    (x : LatticeConfiguration h) (Ψ : Configuration h → ℝ) (κ : ℕ → ℕ → ℝ)
    (χ : (FusedConfiguration α × FusedConfiguration α) → ℝ) :
    wordFirstLetterLatticeFunctional N β α w n x Ψ κ χ =
      ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1), κ s r *
        ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
          χ (wordFusedCoordinateRepresentative N α (wordFusedSiteProjection α u),
            wordFusedCoordinateRepresentative N α (wordFusedSiteProjection α v)) *
            (((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) *
              wordTerminalTest N (sigmaSq β) w (n - s - r) v Ψ) := by
  unfold wordFirstLetterLatticeFunctional
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro r hr
  apply congrArg (fun z : ℝ => κ s r * z)
  have heq := tsum_free_run_weighted_eq_sum β α s r x (fun u v =>
    χ (wordFusedCoordinateRepresentative N α (wordFusedSiteProjection α u),
      wordFusedCoordinateRepresentative N α (wordFusedSiteProjection α v)) *
        wordTerminalTest N (sigmaSq β) w (n - s - r) v Ψ)
  have hcomm (u v : LatticeConfiguration h) :
      ((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) *
        (χ (wordFusedCoordinateRepresentative N α (wordFusedSiteProjection α u),
          wordFusedCoordinateRepresentative N α (wordFusedSiteProjection α v)) *
            wordTerminalTest N (sigmaSq β) w (n - s - r) v Ψ) =
      χ (wordFusedCoordinateRepresentative N α (wordFusedSiteProjection α u),
        wordFusedCoordinateRepresentative N α (wordFusedSiteProjection α v)) *
        (((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) *
          wordTerminalTest N (sigmaSq β) w (n - s - r) v Ψ) := by ring
  simp_rw [hcomm] at heq
  exact heq.symm

end Critical2DKPZ.SHF.Moments
