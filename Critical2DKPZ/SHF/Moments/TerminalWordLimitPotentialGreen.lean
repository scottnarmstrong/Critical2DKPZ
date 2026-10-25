/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSeparated
import all Critical2DKPZ.SHF.Moments.TerminalWordLimitPotentialTube
import Mathlib.Tactic

/-! # Horizon-independent inverse-distance domination of the gap potential -/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer

namespace Critical2DKPZ.SHF.Moments

/-- The potential is bounded even on the lattice diagonal. -/
theorem wordGapPotential_le_four (n : ℕ) (z : Site) : wordGapPotential n z ≤ 4 := by
  have hb := sum_wordGapPotential_le_cutoff {z} n 0
  norm_num at hb ⊢
  exact hb

private theorem wordGapPotential_mono_horizon {m n : ℕ} (hmn : m ≤ n) (z : Site) :
    wordGapPotential m z ≤ wordGapPotential n z := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hmn)
    (fun s hs hnot => div_nonneg (srwKernel_nonneg _ _) (Real.sqrt_nonneg _))

private theorem wordGapPotential_le_cutoff (n k : ℕ) (z : Site) :
    wordGapPotential n z ≤ wordGapPotential k z + 2 / Real.sqrt ((k : ℝ) + 1) := by
  by_cases hnk : n ≤ k
  · exact (wordGapPotential_mono_horizon hnk z).trans (le_add_of_nonneg_right (by positivity))
  · have hkn : k < n := by omega
    have hsplit := Finset.sum_Ico_consecutive
      (fun s : ℕ => srwKernel (2 * s) z / Real.sqrt ((s : ℝ) + 1))
      (m := 1) (n := k + 1) (k := n + 1) (by omega) (by omega)
    simp only [Finset.Ico_add_one_right_eq_Icc] at hsplit
    have htail := wordLimit_gapPotential_late_mass_le {z} n k hkn
    simp only [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, mul_one] at htail
    change (∑ s ∈ Finset.Icc 1 n, _) ≤ (∑ s ∈ Finset.Icc 1 k, _) + _
    rw [← hsplit]
    exact add_le_add le_rfl htail

/-- The gap potential has the locally integrable inverse-distance singularity,
with one constant uniform over all microscopic horizons. -/
theorem exists_wordGapPotential_inverse_norm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (z : Site), 0 < ‖siteToPlane z‖ →
      wordGapPotential n z ≤ C / ‖siteToPlane z‖ := by
  obtain ⟨B, hB, hbound⟩ := exists_wordGapPotential_inverse_fourth_bound
  refine ⟨4 * B + 4, by positivity, fun n z hz => ?_⟩
  let r := ‖siteToPlane z‖
  change wordGapPotential n z ≤ (4 * B + 4) / r
  by_cases hr : 1 ≤ r
  · let k : ℕ := ⌈r ^ 2⌉₊
    have hklo : r ^ 2 ≤ (k : ℝ) := Nat.le_ceil _
    have hkhi : (k : ℝ) < r ^ 2 + 1 := Nat.ceil_lt_add_one (sq_nonneg _)
    have hr2 : 1 ≤ r ^ 2 := one_le_pow₀ hr
    have hk2 : (k : ℝ) ≤ 2 * r ^ 2 := by linarith only [hkhi, hr2]
    have hs2 : Real.sqrt ((k : ℝ) + 1) ^ 2 = (k : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hslo : r ≤ Real.sqrt ((k : ℝ) + 1) := by
      apply (sq_le_sq₀ hz.le (Real.sqrt_nonneg _)).mp
      rw [hs2]
      linarith only [hklo]
    have hshi : Real.sqrt ((k : ℝ) + 1) ≤ 2 * r := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
      rw [hs2, mul_pow]
      nlinarith only [hkhi, hr2]
    have hearly : B * (k : ℝ) * Real.sqrt ((k : ℝ) + 1) / r ^ 4 ≤ 4 * B / r := by
      have hnum : B * (k : ℝ) * Real.sqrt ((k : ℝ) + 1) ≤ 4 * B * r ^ 3 := by
        calc
          _ ≤ B * (2 * r ^ 2) * (2 * r) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hk2 hB.le) hshi (Real.sqrt_nonneg _) (by positivity)
          _ = _ := by ring
      calc
        _ ≤ (4 * B * r ^ 3) / r ^ 4 := div_le_div_of_nonneg_right hnum (by positivity)
        _ = _ := by field_simp [hz.ne']
    have hlate : 2 / Real.sqrt ((k : ℝ) + 1) ≤ 2 / r :=
      div_le_div_of_nonneg_left (by norm_num) hz hslo
    calc
      _ ≤ wordGapPotential k z + 2 / Real.sqrt ((k : ℝ) + 1) := wordGapPotential_le_cutoff n k z
      _ ≤ B * k * Real.sqrt ((k : ℝ) + 1) / r ^ 4 + 2 / Real.sqrt ((k : ℝ) + 1) :=
        add_le_add (hbound k z hz) le_rfl
      _ ≤ 4 * B / r + 2 / r := add_le_add hearly hlate
      _ ≤ _ := by rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hz.le
  · have hrle : r ≤ 1 := (lt_of_not_ge hr).le
    calc
      _ ≤ 4 := wordGapPotential_le_four n z
      _ ≤ 4 / r := (le_div_iff₀ hz).2 (by linarith only [hrle])
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [hB]) hz.le

/-- A regularized inverse-distance bound includes zero gaps without a special
value and remains uniform in the horizon. -/
theorem exists_wordGapPotential_regularized_norm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (z : Site),
      wordGapPotential n z ≤ C / (1 + ‖siteToPlane z‖) := by
  obtain ⟨B, hB, hbound⟩ := exists_wordGapPotential_inverse_norm_bound
  refine ⟨2 * B + 8, by positivity, fun n z => ?_⟩
  let r := ‖siteToPlane z‖
  have hr : 0 ≤ r := norm_nonneg _
  apply (le_div_iff₀ (by positivity : 0 < 1 + r)).2
  by_cases hsmall : r ≤ 1
  · calc
      _ ≤ 4 * (1 + r) := mul_le_mul_of_nonneg_right (wordGapPotential_le_four n z) (by positivity)
      _ ≤ 8 := by linarith only [hsmall]
      _ ≤ _ := by linarith only [hB]
  · have hrp : 0 < r := lt_trans zero_lt_one (lt_of_not_ge hsmall)
    calc
      _ ≤ (B / r) * (1 + r) := mul_le_mul_of_nonneg_right (hbound n z hrp) (by positivity)
      _ ≤ (B / r) * (2 * r) := mul_le_mul_of_nonneg_left (by linarith only [hsmall]) (by positivity)
      _ = 2 * B := by field_simp
      _ ≤ _ := by linarith

end Critical2DKPZ.SHF.Moments
