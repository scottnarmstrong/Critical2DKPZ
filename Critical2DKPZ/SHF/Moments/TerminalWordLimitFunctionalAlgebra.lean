/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitFunctionalBounds
import Mathlib.Tactic

/-! # Time and spatial cutoff errors for first-letter functionals -/

@[expose] public noncomputable section

open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

theorem wordFirstLetterLatticeFunctional_sub_time {h : ℕ} (N : ℕ) (β : ℝ)
    (α : CollisionPair h) (w : List (CollisionPair h)) (n : ℕ) (x : LatticeConfiguration h)
    (Ψ : Configuration h → ℝ) (κ κ' : ℕ → ℕ → ℝ)
    (χ : (FusedConfiguration α × FusedConfiguration α) → ℝ) :
    wordFirstLetterLatticeFunctional N β α w n x Ψ (fun s r => κ s r - κ' s r) χ =
      wordFirstLetterLatticeFunctional N β α w n x Ψ κ χ -
        wordFirstLetterLatticeFunctional N β α w n x Ψ κ' χ := by
  simp only [wordFirstLetterLatticeFunctional, sub_mul, Finset.sum_sub_distrib]

theorem wordFirstLetterLatticeFunctional_sub_spatial {h : ℕ} (N : ℕ) (β : ℝ)
    (α : CollisionPair h) (w : List (CollisionPair h)) (n : ℕ) (x : LatticeConfiguration h)
    (Ψ : Configuration h → ℝ) (κ : ℕ → ℕ → ℝ)
    (χ χ' : (FusedConfiguration α × FusedConfiguration α) → ℝ) :
    wordFirstLetterLatticeFunctional N β α w n x Ψ κ (fun p => χ p - χ' p) =
      wordFirstLetterLatticeFunctional N β α w n x Ψ κ χ -
        wordFirstLetterLatticeFunctional N β α w n x Ψ κ χ' := by
  simp only [wordFirstLetterLatticeFunctional, sub_mul, Finset.sum_sub_distrib, mul_sub]

/-- A full terminal word minus its cutoff is the sum of the time-boundary
error and the spatial error inside the retained time window. -/
theorem wordTerminalTest_sub_latticeFunctional_eq {h : ℕ} (N : ℕ) (β : ℝ)
    (α : CollisionPair h) (w : List (CollisionPair h)) (n : ℕ) (x : LatticeConfiguration h)
    (Ψ : Configuration h → ℝ) (κ : ℕ → ℕ → ℝ)
    (χ : (FusedConfiguration α × FusedConfiguration α) → ℝ) :
    wordTerminalTest N (sigmaSq β) (α :: w) n x Ψ -
        wordFirstLetterLatticeFunctional N β α w n x Ψ κ χ =
      wordFirstLetterLatticeFunctional N β α w n x Ψ (fun s r => 1 - κ s r) (fun _ => 1) +
        wordFirstLetterLatticeFunctional N β α w n x Ψ κ (fun p => 1 - χ p) := by
  rw [wordFirstLetterLatticeFunctional_sub_time, wordFirstLetterLatticeFunctional_sub_spatial,
    wordFirstLetterLatticeFunctional_one_one]
  ring

/-- A constant majorant bounds the complete cutoff error of a signed profile by its positive time-boundary and spatial-cutoff errors. -/
theorem abs_wordTerminalTest_sub_latticeFunctional_le_const {h : ℕ} (N : ℕ) (β : ℝ)
    (α : CollisionPair h) (w : List (CollisionPair h)) (n : ℕ) (x : LatticeConfiguration h)
    (Ψ : Configuration h → ℝ) (κ : ℕ → ℕ → ℝ)
    (χ : (FusedConfiguration α × FusedConfiguration α) → ℝ) (M : ℝ)
    (hΨ : ∀ y, |Ψ y| ≤ M) (hκ : ∀ s r, 0 ≤ κ s r ∧ κ s r ≤ 1)
    (hχ : ∀ p, 0 ≤ χ p ∧ χ p ≤ 1) :
    |wordTerminalTest N (sigmaSq β) (α :: w) n x Ψ -
        wordFirstLetterLatticeFunctional N β α w n x Ψ κ χ| ≤
      wordFirstLetterLatticeFunctional N β α w n x (fun _ => M)
          (fun s r => 1 - κ s r) (fun _ => 1) +
        wordFirstLetterLatticeFunctional N β α w n x (fun _ => M) κ (fun p => 1 - χ p) := by
  rw [wordTerminalTest_sub_latticeFunctional_eq]
  exact (abs_add_le _ _).trans (add_le_add
    (abs_wordFirstLetterLatticeFunctional_le_const N β α w n x Ψ _ _ M hΨ
      (fun s r => sub_nonneg.mpr (hκ s r).2) (fun _ => zero_le_one))
    (abs_wordFirstLetterLatticeFunctional_le_const N β α w n x Ψ _ _ M hΨ
      (fun s r => (hκ s r).1) (fun p => sub_nonneg.mpr (hχ p).2)))

/-- Increasing a time weight increases the functional of a nonnegative
profile and nonnegative spatial cutoff. No sign restriction on the time
weights themselves is needed for this comparison. -/
theorem wordFirstLetterLatticeFunctional_mono_time {h : ℕ} (N : ℕ) (β : ℝ)
    (α : CollisionPair h) (w : List (CollisionPair h)) (n : ℕ) (x : LatticeConfiguration h)
    (Ψ : Configuration h → ℝ) (κ κ' : ℕ → ℕ → ℝ)
    (χ : (FusedConfiguration α × FusedConfiguration α) → ℝ)
    (hΨ : ∀ y, 0 ≤ Ψ y) (hκ : ∀ s r, κ s r ≤ κ' s r) (hχ : ∀ p, 0 ≤ χ p) :
    wordFirstLetterLatticeFunctional N β α w n x Ψ κ χ ≤
      wordFirstLetterLatticeFunctional N β α w n x Ψ κ' χ := by
  unfold wordFirstLetterLatticeFunctional
  apply Finset.sum_le_sum
  intro s hs
  apply Finset.sum_le_sum
  intro r hr
  apply mul_le_mul_of_nonneg_right (hκ s r)
  apply Finset.sum_nonneg
  intro u hu
  apply Finset.sum_nonneg
  intro v hv
  exact mul_nonneg (hχ _)
    (mul_nonneg (mul_nonneg (Finset.prod_nonneg (fun i _ => srwKernel_nonneg s (u i - x i)))
      (collisionWordUndampedPairRunFactor_nonneg β α r u v))
      (wordTerminalTest_nonneg N (sigmaSq_nonneg β) w (n - s - r) v Ψ hΨ))

end Critical2DKPZ.SHF.Moments
