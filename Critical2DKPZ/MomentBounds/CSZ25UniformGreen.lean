/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.LocalizedBoxMass
import Critical2DKPZ.MomentBounds.BoxEnergyLower
import Critical2DKPZ.MomentBounds.GreenDiagonal
import Critical2DKPZ.Lattice.Basic

/-! # The uniform Green-energy lower bound of CSZ25 Lemma 5.3

Large horizons use the local CLT on a box containing half the profile mass, with a parity
restriction. Small horizons use the positive diagonal and finite-box Cauchy--Schwarz.
-/

@[expose] public noncomputable section

namespace Critical2DKPZ.MomentBounds

/-- At horizons at least two, an exponentially localized probability profile has a uniformly positive half-horizon Green energy, as in CSZ25 Lemma 5.3. -/
theorem greenEnergy_half_ge (t c₁ : ℝ) (ht : 0 < t) (hc₁ : 0 < c₁) :
    ∃ η : ℝ, 0 < η ∧ ∀ L : ℕ, 2 ≤ L → ∀ φ : Site → ℝ, (∀ z, 0 ≤ φ z) → HasSum φ 1 →
      ExpLocalized t c₁ L φ → η ≤ greenEnergy (L / 2) φ := by
  obtain ⟨R, hR, hbox⟩ := exists_profileBox_mass_ge_of_expLocalized t c₁ ht hc₁
  let K := 64 * (R + 3) ^ 2
  obtain ⟨c, hc, N₀, hN₀, henergy⟩ := exists_evenTimeEnergy_lower_of_box_mass K
  let T := max (8 * N₀) 8
  let D := (2 * ⌈R * Real.sqrt T + 1⌉₊ + 1) ^ 2
  have hD : (0 : ℝ) < D := by dsimp [D]; positivity
  refine ⟨min (c / 8) (srwKernel 2 0 / (4 * D)), lt_min (by positivity)
    (div_pos srwKernel_two_zero_pos (by positivity)), fun L hL φ hφ hmass hlocal => ?_⟩
  obtain ⟨x, hx⟩ := hbox L (by omega) φ hφ hmass hlocal
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  by_cases hlarge : T ≤ L
  · apply (min_le_left _ _).trans
    let I := Finset.Icc (L / 4 + 1) (L / 2)
    let E : ℕ → ℝ := fun n => ∑' z, ∑' w, φ z * srwKernel (2 * n) (z - w) * φ w
    have hroot : 1 ≤ Real.sqrt (L : ℝ) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ L by exact_mod_cast (show 1 ≤ L by omega))
    have hscale (n : ℕ) (hn : n ∈ I) : 16 * (R * Real.sqrt L + 3) ^ 2 ≤ K * n := by
      have hnfour : (L : ℝ) ≤ 4 * n := by
        exact_mod_cast (show L ≤ 4 * n by have := (Finset.mem_Icc.1 hn).1; omega)
      have hs : R * Real.sqrt L + 3 ≤ (R + 3) * Real.sqrt L := by nlinarith only [hroot]
      have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ R * Real.sqrt L + 3) hs 2
      rw [mul_pow, Real.sq_sqrt hL0.le] at hsq
      have hf := mul_le_mul_of_nonneg_left hnfour (show 0 ≤ 16 * (R + 3) ^ 2 by positivity)
      dsimp [K]
      nlinarith only [hsq, hf]
    have hterm : ∀ n ∈ I, c / L ≤ E n := by
      intro n hn
      have hnin : L / 4 + 1 ≤ n ∧ n ≤ L / 2 := Finset.mem_Icc.1 hn
      have hnN : N₀ ≤ n := by
        have hTL : 8 * N₀ ≤ L := (le_max_left _ _).trans hlarge
        omega
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      exact (div_le_div_of_nonneg_left hc.le hn0 (by exact_mod_cast (show n ≤ L by omega))).trans
        (henergy n hnN φ hφ hmass x _ (mul_nonneg hR.le (Real.sqrt_nonneg _)) (hscale n hn) hx)
    have hcard : (L : ℝ) / 8 ≤ I.card := by
      have hL8 : 8 ≤ L := (le_max_right _ _).trans hlarge
      have hn : L ≤ 8 * I.card := by dsimp [I]; rw [Nat.card_Icc]; omega
      have hr : (L : ℝ) ≤ 8 * I.card := by exact_mod_cast hn
      linarith only [hr]
    have hsub : I ⊆ Finset.Icc 1 (L / 2) :=
      Finset.Icc_subset_Icc_left (by omega)
    have hsum : (∑ n ∈ I, E n) ≤ greenEnergy (L / 2) φ := by
      rw [greenEnergy_eq_sum (L / 2) φ hφ hmass.summable]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ =>
        tsum_nonneg fun z => tsum_nonneg fun w => mul_nonneg
          (mul_nonneg (hφ z) (srwKernel_nonneg _ _)) (hφ w))
    calc
      _ = (L : ℝ) / 8 * (c / L) := by field_simp
      _ ≤ (I.card : ℝ) * (c / L) := mul_le_mul_of_nonneg_right hcard (div_nonneg hc.le hL0.le)
      _ = ∑ _n ∈ I, c / L := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ I, E n := Finset.sum_le_sum hterm
      _ ≤ _ := hsum
  · apply (min_le_right _ _).trans
    have hLT : L ≤ T := le_of_lt (lt_of_not_ge hlarge)
    let A := profileBox x (R * Real.sqrt T)
    have hmassA : (1 / 2 : ℝ) ≤ ∑ z ∈ A, φ z := hx.trans
      (Finset.sum_le_sum_of_subset_of_nonneg (profileBox_mono x
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hLT)) hR.le))
        (fun z _ _ => hφ z))
    have hcardA : (A.card : ℝ) ≤ D := by exact_mod_cast card_profileBox_le x (R * Real.sqrt T)
    have hcs := finite_mass_sq_mul_return_le_card_mul_greenEnergy
      (show 1 ≤ L / 2 by omega) φ hφ hmass A
    have hpos := greenEnergy_nonneg (L / 2) φ hφ
    have hprod := mul_le_mul_of_nonneg_right hcardA hpos
    have hsquare : (1 / 4 : ℝ) ≤ (∑ z ∈ A, φ z) ^ 2 := by nlinarith only [hmassA]
    apply (div_le_iff₀ (show 0 < 4 * (D : ℝ) by positivity)).2
    nlinarith only [hcs, hprod, mul_le_mul_of_nonneg_right hsquare srwKernel_two_zero_pos.le]

end Critical2DKPZ.MomentBounds
