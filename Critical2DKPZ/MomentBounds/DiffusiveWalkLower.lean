/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.SrwKernel
public import Critical2DKPZ.Definitions.SiteToPlane
import Critical2DKPZ.RandomWalk.Estimates

/-! # A diffusive lower bound from the period-correct local central limit theorem -/

@[expose] public noncomputable section

namespace Critical2DKPZ.MomentBounds

/-- On each fixed diffusive ball, the even walk kernel has a uniform reciprocal-time
lower bound once time is large enough. The parity condition is explicit. -/
theorem exists_srwKernel_two_mul_lower (K : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n → ∀ z : Site,
      Even (z 0 + z 1) → ‖siteToPlane z‖ ^ 2 ≤ K * n → c / n ≤ srwKernel (2 * n) z := by
  obtain ⟨C, hC, hCLT⟩ := srwKernel_localCLT
  let g := Real.exp (-K / 2)
  let c := g / (2 * Real.pi)
  have hc : 0 < c := div_pos (Real.exp_pos _) (mul_pos (by norm_num) Real.pi_pos)
  refine ⟨c, hc, max 1 ⌈C / c⌉₊, le_max_left _ _, fun n hn z hz hnorm => ?_⟩
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hthreshold : C ≤ c * n := by
    have hceil : C / c ≤ (n : ℝ) := (Nat.le_ceil _).trans
      (by exact_mod_cast ((le_max_right 1 ⌈C / c⌉₊).trans hn))
    exact (div_le_iff₀ hc).1 hceil |>.trans_eq (mul_comm _ _)
  have hpar : Even (z 0 + z 1 + (2 * n : ℕ)) := by
    obtain ⟨k, hk⟩ := hz
    refine ⟨k + n, ?_⟩
    push_cast
    rw [hk]
    ring
  have h := (abs_le.1 (hCLT (2 * n) (by omega) z hpar)).1
  have hheat : 2 * heatKernel (((2 * n : ℕ) : ℝ) / 2) (siteToPlane z) =
      Real.exp (-‖siteToPlane z‖ ^ 2 / (2 * n)) / (Real.pi * n) := by
    have htime : ((2 * n : ℕ) : ℝ) / 2 = n := by push_cast; ring
    rw [htime, heatKernel]
    field_simp
  have he : g ≤ Real.exp (-‖siteToPlane z‖ ^ 2 / (2 * n)) := by
    apply Real.exp_le_exp.2
    have hd : ‖siteToPlane z‖ ^ 2 / (2 * n) ≤ K / 2 :=
      (div_le_iff₀ (by positivity)).2 (by nlinarith only [hnorm])
    simpa only [neg_div] using neg_le_neg hd
  have hmain : 2 * c / n ≤ 2 * heatKernel (((2 * n : ℕ) : ℝ) / 2) (siteToPlane z) := by
    rw [hheat]
    calc
      _ = g / (Real.pi * n) := by dsimp [c]; field_simp
      _ ≤ _ := div_le_div_of_nonneg_right he (mul_nonneg Real.pi_pos.le hn0.le)
  have herr : C / ((2 * n : ℕ) : ℝ) ^ 2 ≤ c / n := by
    have hden : (n : ℝ) ^ 2 ≤ ((2 * n : ℕ) : ℝ) ^ 2 := by
      push_cast
      nlinarith only [sq_nonneg (n : ℝ)]
    calc
      _ ≤ C / (n : ℝ) ^ 2 := div_le_div_of_nonneg_left hC.le (sq_pos_of_pos hn0) hden
      _ ≤ _ := (div_le_div_iff₀ (sq_pos_of_pos hn0) hn0).2 (by
        nlinarith only [mul_le_mul_of_nonneg_right hthreshold hn0.le])
  rw [mul_div_assoc] at hmain
  linarith only [h, hmain, herr]

end Critical2DKPZ.MomentBounds
