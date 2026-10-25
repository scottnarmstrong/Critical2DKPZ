/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BlockMoments
public import Critical2DKPZ.Extensions.ScaleLimit.BlockRatioBound
public import Critical2DKPZ.Extensions.ScaleLimit.BlockQEstimates
import Mathlib.Tactic

/-! # The geometric flow block estimates with common constants -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A common geometric ratio and common constants give all the flow block
estimates, uniformly in the block indices and the tail level. -/
theorem block_estimates (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ → ∃ (C : ℝ) (ℓ₀ : ℕ),
      0 ≤ C ∧ 1 ≤ ℓ₀ ∧
      (∀ j : ℕ, 1 ≤ j →
        Integrable (fun ω => (blockMass Z ρ j ω - 1) ^ 2) P ∧
        Integrable (fun ω => (blockMass Z ρ j ω - 1) ^ 4) P ∧
        (∫ ω, (blockMass Z ρ j ω - 1) ^ 2 ∂P) ≤ C / j ∧
        (∫ ω, (blockMass Z ρ j ω - 1) ^ 4 ∂P) ≤ C / (j : ℝ) ^ 2) ∧
      (∀ n ℓ : ℕ, ℓ₀ ≤ ℓ → ℓ < n →
        P {ω | 1 / 2 < |blockR Z ρ n ℓ ω - 1|} ≤ ENNReal.ofReal (C / ℓ) ∧
        ∀ u : ℝ, 0 ≤ u →
          P {ω | blockQ Z ρ n ℓ ω < Real.exp (-u)} ≤
            ENNReal.ofReal (C / ℓ + C * ℓ * Real.exp (-u)) ∧
          P {ω | Real.exp u < blockQ Z ρ n ℓ ω} ≤ ENNReal.ofReal (Real.exp (-u))) := by
  obtain ⟨ρR, hρR, hR⟩ := blockR_prob_bound ϑ P Z hZ
  obtain ⟨ρQ, hρQ, hQ⟩ := blockQ_estimates ϑ P Z hZ
  refine ⟨max ρR ρQ, hρR.trans_le (le_max_left _ _), ?_⟩
  intro ρ hρ
  have hρR' : ρR ≤ ρ := (le_max_left _ _).trans hρ
  have hρQ' : ρQ ≤ ρ := (le_max_right _ _).trans hρ
  have hρ1 : 1 < ρ := hρR.trans_le hρR'
  obtain ⟨CM, hCM0, hM⟩ := block_moments ϑ P Z hZ hρ1
  obtain ⟨CR, ℓR, hRb⟩ := hR ρ hρR'
  obtain ⟨CQ, ℓQ, hQb⟩ := hQ ρ hρQ'
  let C := |CM| + |CR| + |CQ| + 1
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hMC : CM ≤ C := by dsimp [C]; linarith [le_abs_self CM, abs_nonneg CR, abs_nonneg CQ]
  have hRC : CR ≤ C := by dsimp [C]; linarith [le_abs_self CR, abs_nonneg CM, abs_nonneg CQ]
  have hQC : CQ ≤ C := by dsimp [C]; linarith [le_abs_self CQ, abs_nonneg CM, abs_nonneg CR]
  refine ⟨C, max 1 (max ℓR ℓQ), hC0, le_max_left _ _, ?_, ?_⟩
  · intro j hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    obtain ⟨hi2, hi4, hb2, hb4⟩ := hM k
    refine ⟨hi2, hi4, ?_, ?_⟩
    · exact hb2.trans (div_le_div_of_nonneg_right hMC (by positivity))
    · exact hb4.trans (div_le_div_of_nonneg_right hMC (sq_nonneg _))
  · intro n ℓ hℓ hℓn
    have hℓR : ℓR ≤ ℓ := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hℓ
    have hℓQ : ℓQ ≤ ℓ := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hℓ
    constructor
    · exact (hRb n ℓ hℓR hℓn).trans
        (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hRC (Nat.cast_nonneg _)))
    · intro u hu
      obtain ⟨hl, hh⟩ := hQb n ℓ hℓQ hℓn u hu
      refine ⟨hl.trans (ENNReal.ofReal_le_ofReal ?_), hh⟩
      apply add_le_add (div_le_div_of_nonneg_right hQC (Nat.cast_nonneg _))
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hQC (Nat.cast_nonneg _)) (Real.exp_nonneg _)

end Critical2DKPZ.Extensions.ScaleLimit
