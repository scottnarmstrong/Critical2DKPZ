/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitLatticeFunctional
public import Critical2DKPZ.SHF.Moments.WordLimitFirstBlock
import Critical2DKPZ.SHF.Moments.WordDominationPairRunCCR
import Critical2DKPZ.MomentBounds.CCR25AbsolutePositivity
import Mathlib.Tactic

/-! # Positivity and constant-profile bounds for cutoff functionals -/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- The individual unweighted run factor is nonnegative before summing any
of its collision endpoints. -/
theorem collisionWordUndampedPairRunFactor_nonneg {h : ℕ} (β : ℝ) (α : CollisionPair h)
    (r : ℕ) (u v : LatticeConfiguration h) : 0 ≤ collisionWordUndampedPairRunFactor β α r u v := by
  rw [collisionWordUndampedPairRunFactor, pairRunFactor_eq_sigmaSq_mul_interactingReplicaKernelAbs]
  exact mul_nonneg (sigmaSq_nonneg β)
    (interactingReplicaKernelAbs_nonneg β (pairPartition α) r u v)

private theorem free_run_nonneg {h : ℕ} (β : ℝ) (α : CollisionPair h)
    (s r : ℕ) (x u v : LatticeConfiguration h) :
    0 ≤ (∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v :=
  mul_nonneg (Finset.prod_nonneg (fun _i _ => srwKernel_nonneg _ _))
    (collisionWordUndampedPairRunFactor_nonneg β α r u v)

private theorem abs_sum_le_of_abs_le {ι : Type*} (S : Finset ι) (f g : ι → ℝ)
    (h : ∀ i ∈ S, |f i| ≤ g i) : |∑ i ∈ S, f i| ≤ ∑ i ∈ S, g i :=
  (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum h)


/-- A constant terminal profile controls every bounded signed profile under
nonnegative time and spatial weights. -/
theorem abs_wordFirstLetterLatticeFunctional_le_const {h : ℕ} (N : ℕ) (β : ℝ)
    (α : CollisionPair h) (w : List (CollisionPair h)) (n : ℕ) (x : LatticeConfiguration h)
    (Ψ : Configuration h → ℝ) (κ : ℕ → ℕ → ℝ)
    (χ : (FusedConfiguration α × FusedConfiguration α) → ℝ) (M : ℝ)
    (hΨ : ∀ y, |Ψ y| ≤ M) (hκ : ∀ s r, 0 ≤ κ s r) (hχ : ∀ p, 0 ≤ χ p) :
    |wordFirstLetterLatticeFunctional N β α w n x Ψ κ χ| ≤
      wordFirstLetterLatticeFunctional N β α w n x (fun _ => M) κ χ := by
  unfold wordFirstLetterLatticeFunctional
  apply abs_sum_le_of_abs_le
  intro s hs
  apply abs_sum_le_of_abs_le
  intro r hr
  rw [abs_mul, abs_of_nonneg (hκ s r)]
  apply mul_le_mul_of_nonneg_left _ (hκ s r)
  apply abs_sum_le_of_abs_le
  intro u hu
  apply abs_sum_le_of_abs_le
  intro v hv
  rw [abs_mul, abs_of_nonneg (hχ _)]
  apply mul_le_mul_of_nonneg_left _ (hχ _)
  rw [abs_mul, abs_of_nonneg (free_run_nonneg β α s r x u v)]
  apply mul_le_mul_of_nonneg_left _ (free_run_nonneg β α s r x u v)
  rw [wordTerminalTest_const]
  exact abs_wordTerminalTest_le_mass N (sigmaSq_nonneg β) w (n - s - r) v Ψ hΨ

/-- Increasing a spatial weight increases its nonnegative-profile functional. -/
theorem wordFirstLetterLatticeFunctional_mono_spatial {h : ℕ} (N : ℕ) (β : ℝ)
    (α : CollisionPair h) (w : List (CollisionPair h)) (n : ℕ) (x : LatticeConfiguration h)
    (Ψ : Configuration h → ℝ) (κ : ℕ → ℕ → ℝ)
    (χ χ' : (FusedConfiguration α × FusedConfiguration α) → ℝ)
    (hΨ : ∀ y, 0 ≤ Ψ y) (hκ : ∀ s r, 0 ≤ κ s r) (hχ : ∀ p, χ p ≤ χ' p) :
    wordFirstLetterLatticeFunctional N β α w n x Ψ κ χ ≤
      wordFirstLetterLatticeFunctional N β α w n x Ψ κ χ' := by
  unfold wordFirstLetterLatticeFunctional
  apply Finset.sum_le_sum
  intro s hs
  apply Finset.sum_le_sum
  intro r hr
  apply mul_le_mul_of_nonneg_left _ (hκ s r)
  apply Finset.sum_le_sum
  intro u hu
  apply Finset.sum_le_sum
  intro v hv
  exact mul_le_mul_of_nonneg_right (hχ _)
    (mul_nonneg (free_run_nonneg β α s r x u v)
      (wordTerminalTest_nonneg N (sigmaSq_nonneg β) w (n - s - r) v Ψ hΨ))

/-- With unit spatial weight, the functional is exactly the first-block
endpoint expression used in the time-boundary input. -/
theorem wordFirstLetterLatticeFunctional_one_spatial_eq_firstBlock {h : ℕ}
    (N : ℕ) (β : ℝ) (α : CollisionPair h) (w : List (CollisionPair h)) (n : ℕ)
    (x : LatticeConfiguration h) (Ψ : Configuration h → ℝ) (κ : ℕ → ℕ → ℝ) :
    wordFirstLetterLatticeFunctional N β α w n x Ψ κ (fun _ => 1) =
      ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1), κ s r *
        ∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
          wordFirstBlockKernel β α s r x v * wordTerminalTest N (sigmaSq β) w (n - s - r) v Ψ := by
  unfold wordFirstLetterLatticeFunctional
  simp only [one_mul]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro r hr
  apply congrArg (fun z : ℝ => κ s r * z)
  exact sum_free_run_terminal_eq β α s r x (fun v =>
    wordTerminalTest N (sigmaSq β) w (n - s - r) v Ψ)

end Critical2DKPZ.SHF.Moments
