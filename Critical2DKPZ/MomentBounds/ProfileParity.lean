/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CSZ25GreenCalculus
import Mathlib.Algebra.Ring.Int.Parity
import Critical2DKPZ.Lattice.Basic

/-! # Finite profile restrictions with a single lattice parity -/

@[expose] public noncomputable section

namespace Critical2DKPZ.MomentBounds

/-- At least half the mass of a finite restriction lies in one parity class. -/
theorem exists_parity_subset (A : Finset Site) (φ : Site → ℝ) :
    ∃ B : Finset Site, B ⊆ A ∧
      (∀ z ∈ B, ∀ w ∈ B, Even ((z - w) 0 + (z - w) 1)) ∧
      (∑ z ∈ A, φ z) / 2 ≤ ∑ z ∈ B, φ z := by
  let p : Site → Prop := fun z => Even (z 0 + z 1)
  have hsum := Finset.sum_filter_add_sum_filter_not A p φ
  by_cases h : (∑ z ∈ A, φ z) / 2 ≤ ∑ z ∈ A.filter p, φ z
  · refine ⟨A.filter p, Finset.filter_subset _ _, ?_, h⟩
    intro z hz w hw
    have he := (Finset.mem_filter.1 hz).2.sub (Finset.mem_filter.1 hw).2
    convert he using 1
    simp only [Pi.sub_apply]
    ring
  · refine ⟨A.filter (fun z => ¬p z), Finset.filter_subset _ _, ?_, by linarith only [h, hsum]⟩
    intro z hz w hw
    have he := (Int.not_even_iff_odd.1 (Finset.mem_filter.1 hz).2).sub_odd
      (Int.not_even_iff_odd.1 (Finset.mem_filter.1 hw).2)
    convert he using 1
    simp only [Pi.sub_apply]
    ring

/-- A lower kernel bound on a finite restriction gives a lower bound on the full energy. -/
theorem evenTimeEnergy_ge_of_finite_lower (n : ℕ) (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z)
    (hsum : Summable φ) (B : Finset Site) {b : ℝ}
    (hb : ∀ z ∈ B, ∀ w ∈ B, b ≤ srwKernel (2 * n) (z - w)) :
    b * (∑ z ∈ B, φ z) ^ 2 ≤ ∑' z, ∑' w, φ z * srwKernel (2 * n) (z - w) * φ w := by
  have hs := summable_evenTimeEnergy_terms n φ hφ hsum
  rw [← hs.tsum_prod]
  calc
    _ = ∑ z ∈ B, ∑ w ∈ B, φ z * b * φ w := by
      rw [pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ ≤ ∑ z ∈ B, ∑ w ∈ B, φ z * srwKernel (2 * n) (z - w) * φ w :=
      Finset.sum_le_sum fun z hz => Finset.sum_le_sum fun w hw =>
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hb z hz w hw) (hφ z)) (hφ w)
    _ = ∑ p ∈ B ×ˢ B, φ p.1 * srwKernel (2 * n) (p.1 - p.2) * φ p.2 :=
      (Finset.sum_product B B (fun p : Site × Site =>
        φ p.1 * srwKernel (2 * n) (p.1 - p.2) * φ p.2)).symm
    _ ≤ _ := hs.sum_le_tsum _ (fun p _ => mul_nonneg
      (mul_nonneg (hφ _) (srwKernel_nonneg _ _)) (hφ _))

end Critical2DKPZ.MomentBounds
