/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CSZ25GreenCalculus
import Critical2DKPZ.MomentBounds.EvenKernelMaximum
import Critical2DKPZ.Lattice.Basic

/-! # The bounded Green-energy loss from halving time -/

@[expose] public noncomputable section

namespace Critical2DKPZ.MomentBounds

/-- A probability profile's energy at a fixed even time is at most the return probability. -/
theorem evenTimeEnergy_le_return (n : ℕ) (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z)
    (hmass : HasSum φ 1) :
    (∑' z, ∑' w, φ z * srwKernel (2 * n) (z - w) * φ w) ≤ srwKernel (2 * n) 0 := by
  have hs := summable_evenTimeEnergy_terms n φ hφ hmass.summable
  have hb : Summable (fun p : Site × Site => φ p.1 * srwKernel (2 * n) 0 * φ p.2) := by
    convert (hmass.summable.mul_of_nonneg hmass.summable hφ hφ).mul_left (srwKernel (2 * n) 0) using 1
    funext p
    ring
  have hle := hs.tsum_le_tsum (fun p => mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (srwKernel_two_mul_le_zero n _) (hφ _)) (hφ _)) hb
  rw [hs.tsum_prod, hb.tsum_prod] at hle
  simpa only [tsum_mul_left, hmass.tsum_eq, mul_one, tsum_mul_right, one_mul] using hle

/-- Halving the horizon changes the Green energy by at most the upper return-probability constant. -/
theorem greenEnergy_sub_half_le {aHi : ℝ} (ha : ∀ n : ℕ, 1 ≤ n → srwKernel (2 * n) 0 ≤ aHi / n)
    (L : ℕ) (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z) (hmass : HasSum φ 1) :
    greenEnergy L φ - greenEnergy (L / 2) φ ≤ aHi := by
  have hA : 0 < aHi := srwKernel_two_zero_pos.trans_le (by simpa using ha 1 le_rfl)
  let E : ℕ → ℝ := fun n => ∑' z, ∑' w, φ z * srwKernel (2 * n) (z - w) * φ w
  let S := Finset.Icc 1 L \ Finset.Icc 1 (L / 2)
  have hsub : Finset.Icc 1 (L / 2) ⊆ Finset.Icc 1 L :=
    Finset.Icc_subset_Icc_right (Nat.div_le_self L 2)
  have hsplit := Finset.sum_sdiff (f := E) hsub
  have heq : greenEnergy L φ - greenEnergy (L / 2) φ = ∑ n ∈ S, E n := by
    rw [greenEnergy_eq_sum L φ hφ hmass.summable,
      greenEnergy_eq_sum (L / 2) φ hφ hmass.summable]
    change (∑ n ∈ Finset.Icc 1 L, E n) - (∑ n ∈ Finset.Icc 1 (L / 2), E n) = _
    linarith only [hsplit]
  have hcard : S.card ≤ L / 2 + 1 := by
    dsimp [S]
    rw [Finset.card_sdiff, Finset.inter_eq_left.2 hsub]
    simp only [Nat.card_Icc]
    omega
  have hden : (0 : ℝ) < (L / 2 : ℕ) + 1 := by positivity
  rw [heq]
  calc
    _ ≤ ∑ _n ∈ S, aHi / ((L / 2 : ℕ) + 1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hnL, hnnot⟩ := Finset.mem_sdiff.1 hn
      have hn1 := (Finset.mem_Icc.1 hnL).1
      have hnlarge : L / 2 + 1 ≤ n := by
        simp only [Finset.mem_Icc, not_and] at hnnot
        have h := hnnot hn1
        omega
      exact (evenTimeEnergy_le_return n φ hφ hmass).trans ((ha n hn1).trans
        (div_le_div_of_nonneg_left hA.le hden (by exact_mod_cast hnlarge)))
    _ ≤ ((L / 2 : ℕ) + 1 : ℝ) * (aHi / ((L / 2 : ℕ) + 1 : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (div_nonneg hA.le hden.le)
    _ = aHi := by field_simp

end Critical2DKPZ.MomentBounds
