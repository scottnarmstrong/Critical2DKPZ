/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.SpreadEnergyLower
import Critical2DKPZ.MomentBounds.CSZ25DampingChoice
import Critical2DKPZ.Lattice.Basic

/-! # A logarithmic Green lower bound with an explicit spread denominator -/

@[expose] public noncomputable section

namespace Critical2DKPZ.MomentBounds

/-- Green energy bounds a logarithmic ratio from below up to fixed constants. -/
theorem exists_greenEnergy_ge_log_ratio :
    ∃ c A : ℝ, 0 < c ∧ 1 ≤ A ∧ ∀ M : ℕ, 1 ≤ M → ∀ φ : Site → ℝ,
      (∀ z, 0 ≤ φ z) → HasSum φ 1 →
      Summable (fun z => ‖siteToPlane z - profileMean φ‖ ^ 2 * φ z) →
        c * Real.log ((M : ℝ) / (A * (profileSpread φ + 1))) ≤ greenEnergy M φ := by
  obtain ⟨c, hc, N₀, hN₀, henergy⟩ := exists_evenTimeEnergy_lower_of_spread
  let A : ℝ := N₀ + 2
  refine ⟨c, A, hc, by dsimp [A]; have := (Nat.cast_nonneg N₀ : (0 : ℝ) ≤ N₀); linarith,
    fun M hM φ hφ hmass hquad => ?_⟩
  let D := profileSpread φ
  let K := max N₀ ⌈D + 1⌉₊
  have hD : 0 ≤ D := profileSpread_nonneg φ hφ
  have hK : 1 ≤ K := hN₀.trans (le_max_left _ _)
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hA : 0 < A := by dsimp [A]; positivity
  have hden : 0 < A * (D + 1) := mul_pos hA (by positivity)
  have hKb : (K : ℝ) ≤ A * (D + 1) := by
    rw [show (K : ℝ) = max (N₀ : ℝ) (⌈D + 1⌉₊ : ℝ) by exact_mod_cast (rfl : K = max N₀ ⌈D + 1⌉₊)]
    apply max_le
    · dsimp [A]
      nlinarith only [hD, (Nat.cast_nonneg N₀ : (0 : ℝ) ≤ N₀)]
    · have hceil := (Nat.ceil_lt_add_one (show 0 ≤ D + 1 by positivity)).le
      dsimp [A]
      nlinarith only [hceil, hD, (show (1 : ℝ) ≤ N₀ by exact_mod_cast hN₀)]
  by_cases hKM : K ≤ M
  · have hlog : Real.log ((M : ℝ) / (A * (D + 1))) ≤ Real.log ((M : ℝ) / K) :=
      Real.log_le_log (div_pos hM0 hden) (div_le_div_of_nonneg_left hM0.le hK0 hKb)
    have htail : (∑ n ∈ Finset.Icc K M, c / n) ≤ greenEnergy M φ := by
      rw [greenEnergy_eq_sum M φ hφ hmass.summable]
      calc
        _ ≤ ∑ n ∈ Finset.Icc K M, ∑' z, ∑' w, φ z * srwKernel (2 * n) (z - w) * φ w := by
          apply Finset.sum_le_sum
          intro n hn
          have hKn := (Finset.mem_Icc.1 hn).1
          exact henergy n ((le_max_left _ _).trans hKn) φ hφ hmass hquad
            ((Nat.le_ceil (D + 1)).trans (by exact_mod_cast ((le_max_right N₀ ⌈D + 1⌉₊).trans hKn)))
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left hK)
          (fun n _ _ => tsum_nonneg fun z => tsum_nonneg fun w => mul_nonneg
            (mul_nonneg (hφ z) (srwKernel_nonneg _ _)) (hφ w))
    calc
      _ ≤ c * Real.log ((M : ℝ) / K) := mul_le_mul_of_nonneg_left hlog hc.le
      _ ≤ c * (∑ n ∈ Finset.Icc K M, (n : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left (log_div_le_sum_Icc_inv hK hKM) hc.le
      _ = ∑ n ∈ Finset.Icc K M, c / n := by simp only [Finset.mul_sum, div_eq_mul_inv]
      _ ≤ _ := htail
  · have hMK : (M : ℝ) ≤ K := by exact_mod_cast (le_of_lt (lt_of_not_ge hKM))
    have hMb : (M : ℝ) ≤ A * (D + 1) := hMK.trans hKb
    have hlog : Real.log ((M : ℝ) / (A * (D + 1))) ≤ 0 :=
      Real.log_nonpos (div_nonneg hM0.le hden.le) ((div_le_one hden).2 hMb)
    exact (mul_nonpos_of_nonneg_of_nonpos hc.le hlog).trans (greenEnergy_nonneg M φ hφ)

end Critical2DKPZ.MomentBounds
