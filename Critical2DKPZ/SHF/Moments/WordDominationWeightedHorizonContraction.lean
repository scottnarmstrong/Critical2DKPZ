/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationAlphabetContraction
public import Critical2DKPZ.MomentBounds.CCR25GaussianMoments
import Mathlib.Tactic

/-! # Alphabet contraction at every shorter microscopic horizon -/

@[expose] public section

namespace Critical2DKPZ.SHF.Moments

open Filter Critical2DKPZ.MomentBounds Polymer

/-- Damped overlaps increase when the microscopic horizon increases. -/
theorem collisionWord_dampedOverlap_mono_horizon (lam : ℝ) {L K : ℕ} (hLK : L ≤ K) :
    dampedOverlap lam L ≤ dampedOverlap lam K := by
  unfold dampedOverlap
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc le_rfl hLK
  · intro r hr hnot
    exact mul_nonneg (Real.exp_nonneg _) (srwKernel_nonneg _ _)

/-- The positive resolvent denominator preserves the order of its overlap
argument below one. -/
theorem collisionWord_resolvent_ratio_mono {a b : ℝ} (hab : a ≤ b) (hb : b < 1) :
    a / (1 - a) ≤ b / (1 - b) := by
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  nlinarith

/-- One damping parameter gives a uniform partition-alphabet contraction for every shorter microscopic horizon at sufficiently large lattice scales. -/
theorem eventually_critical_alphabet_contraction_all_horizons
    (ϑ : ℝ) (B : ℕ) (hB : 1 ≤ B) (cI cQ P : ℝ)
    (hcI : 1 ≤ cI) (hcQ : 1 ≤ cQ) (hP : 1 ≤ P) :
    ∃ lam : ℝ, 1 ≤ lam ∧ ∀ᶠ N : ℕ in atTop, ∀ L : ℕ, L ≤ B * N →
      sigmaSq (criticalBeta ϑ N) * dampedOverlap (lam / ((B * N : ℕ) : ℝ)) L < 1 ∧
      (1 + cI * (sigmaSq (criticalBeta ϑ N) * dampedOverlap (lam / ((B * N : ℕ) : ℝ)) L /
        (1 - sigmaSq (criticalBeta ϑ N) * dampedOverlap (lam / ((B * N : ℕ) : ℝ)) L))) *
        sigmaSq (criticalBeta ϑ N) * P * cQ < 1 / 4 := by
  obtain ⟨lam, hlam, hgood⟩ :=
    eventually_critical_alphabet_contraction ϑ B hB cI cQ P hcI hcQ hP
  refine ⟨lam, hlam, ?_⟩
  filter_upwards [hgood] with N hN
  intro L hL
  have hσ := sigmaSq_nonneg (criticalBeta ϑ N)
  have hmono := mul_le_mul_of_nonneg_left
    (collisionWord_dampedOverlap_mono_horizon (lam / ((B * N : ℕ) : ℝ)) hL) hσ
  refine ⟨hmono.trans_lt hN.1, ?_⟩
  have hratio := collisionWord_resolvent_ratio_mono hmono hN.1
  apply lt_of_le_of_lt _ hN.2
  apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hcQ)
  apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hP)
  apply mul_le_mul_of_nonneg_right _ hσ
  exact add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hratio (zero_le_one.trans hcI))

end Critical2DKPZ.SHF.Moments

end
