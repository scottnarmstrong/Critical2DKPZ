/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CSZ25GreenCalculus
import Critical2DKPZ.Lattice.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! # Diagonal and finite-mass lower bounds for Green energies -/

@[expose] public noncomputable section

namespace Critical2DKPZ.MomentBounds

/-- Probability profiles have an absolutely summable squared mass. -/
theorem summable_sq_probability_profile (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z)
    (hmass : HasSum φ 1) : Summable (fun z => φ z ^ 2) := by
  apply Summable.of_nonneg_of_le (fun z => sq_nonneg _) (fun z => ?_) hmass.summable
  have hz : φ z ≤ 1 := hmass.tsum_eq ▸ hmass.summable.le_tsum z (fun w _ => hφ w)
  nlinarith only [mul_le_mul_of_nonneg_left hz (hφ z)]

/-- Retaining only the diagonal and the first even time gives a lower energy bound. -/
theorem greenEnergy_ge_diagonal {M : ℕ} (hM : 1 ≤ M) (φ : Site → ℝ)
    (hφ : ∀ z, 0 ≤ φ z) (hmass : HasSum φ 1) :
    srwKernel 2 0 * (∑' z, φ z ^ 2) ≤ greenEnergy M φ := by
  have hs := summable_greenEnergy_terms M φ hφ hmass.summable
  have hsq := summable_sq_probability_profile φ hφ hmass
  rw [← tsum_mul_left]
  apply (hsq.mul_left _).tsum_le_tsum _ hs.prod
  intro z
  have hdiag : srwKernel 2 0 ≤ truncatedGreen M (z - z) := by
    rw [sub_self, truncatedGreen]
    simpa only [Nat.mul_one] using Finset.single_le_sum (f := fun n => srwKernel (2 * n) 0)
      (fun n _ => srwKernel_nonneg (2 * n) 0) (Finset.mem_Icc.2 ⟨le_rfl, hM⟩)
  calc
    _ ≤ φ z * truncatedGreen M (z - z) * φ z := by
      have h := mul_le_mul_of_nonneg_right hdiag (sq_nonneg (φ z))
      nlinarith only [h]
    _ ≤ _ := (hs.prod_factor z).le_tsum z (fun w _ => mul_nonneg
      (mul_nonneg (hφ z) (truncatedGreen_nonneg _ _)) (hφ w))

/-- A finite restriction with substantial mass forces a quantitative Green-energy lower bound. -/
theorem finite_mass_sq_mul_return_le_card_mul_greenEnergy {M : ℕ} (hM : 1 ≤ M)
    (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z) (hmass : HasSum φ 1) (A : Finset Site) :
    (∑ z ∈ A, φ z) ^ 2 * srwKernel 2 0 ≤ (A.card : ℝ) * greenEnergy M φ := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq A (fun _ => (1 : ℝ)) φ
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hsum : (∑ z ∈ A, φ z ^ 2) ≤ ∑' z, φ z ^ 2 :=
    (summable_sq_probability_profile φ hφ hmass).sum_le_tsum _ (fun z _ => sq_nonneg _)
  have hbound := hcs.trans (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _))
  have hdiag := greenEnergy_ge_diagonal hM φ hφ hmass
  calc
    _ ≤ ((A.card : ℝ) * (∑' z, φ z ^ 2)) * srwKernel 2 0 :=
      mul_le_mul_of_nonneg_right hbound srwKernel_two_zero_pos.le
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)
      nlinarith only [h]

end Critical2DKPZ.MomentBounds
