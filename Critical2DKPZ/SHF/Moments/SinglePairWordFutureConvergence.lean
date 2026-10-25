/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureWindows
import Mathlib.Tactic

/-! # Convergence of the complete tested two-particle future tail -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open MeasureTheory Filter Polymer
open scoped CompactlySupported Topology

/-- Strictly ordered diffusive clock limits give eventual microscopic clock ordering. -/
theorem eventually_nat_le_of_scaled_limit_lt
    (A B : ℕ → ℕ) {a b : ℝ}
    (hA : Tendsto (fun N : ℕ => (A N : ℝ) / N) atTop (𝓝 a))
    (hB : Tendsto (fun N : ℕ => (B N : ℝ) / N) atTop (𝓝 b)) (hab : a < b) :
    ∀ᶠ N : ℕ in atTop, A N ≤ B N := by
  have hgap := (hB.sub hA).eventually (Ioi_mem_nhds (sub_pos.mpr hab))
  filter_upwards [hgap, eventually_gt_atTop 0] with N hgapN hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hratio : (A N : ℝ) / N < (B N : ℝ) / N := sub_pos.mp hgapN
  have h := (div_lt_div_iff_of_pos_right hNr).mp hratio
  exact_mod_cast h.le

/-- The terminal clock-window cardinality has the expected diffusive limit. -/
theorem tendsto_terminal_window_card_ratio
    (B L : ℕ → ℕ) {t H : ℝ}
    (hB : Tendsto (fun N : ℕ => (B N : ℝ) / N) atTop (𝓝 t))
    (hL : Tendsto (fun N : ℕ => (L N : ℝ) / N) atTop (𝓝 H)) (htH : t < H) :
    Tendsto (fun N : ℕ => ((Finset.Icc (B N + 1) (L N)).card : ℝ) / N)
      atTop (𝓝 (H - t)) := by
  have hle := eventually_nat_le_of_scaled_limit_lt B L hB hL htH
  apply (hL.sub hB).congr'
  filter_upwards [hle] with N hN
  have hc : (Finset.Icc (B N + 1) (L N)).card = L N - B N := by
    rw [Nat.card_Icc]
    omega
  rw [hc, Nat.cast_sub hN, sub_div]

/-- If both boundary terms and the interior difference are bounded by `η`, the difference of the two three-term sums is bounded by `5 * η`. -/
theorem three_part_error_le (d₀ d d₁ c₀ c c₁ η : ℝ)
    (hd₀ : |d₀| ≤ η) (hd : |d - c| ≤ η) (hd₁ : |d₁| ≤ η)
    (hc₀ : |c₀| ≤ η) (hc₁ : |c₁| ≤ η) :
    |(d₀ + d + d₁) - (c₀ + c + c₁)| ≤ 5 * η := by
  have heq : (d₀ + d + d₁) - (c₀ + c + c₁) = d₀ + (d - c) + d₁ + (-c₀) + (-c₁) := by ring
  rw [heq]
  have h₀ := abs_add_le d₀ (d - c)
  have h₁ := abs_add_le (d₀ + (d - c)) d₁
  have h₂ := abs_add_le (d₀ + (d - c) + d₁) (-c₀)
  have h₃ := abs_add_le (d₀ + (d - c) + d₁ + (-c₀)) (-c₁)
  simp only [abs_neg] at h₂ h₃
  linarith only [h₀, h₁, h₂, h₃, hd₀, hd, hd₁, hc₀, hc₁]

/-- For nonnegative `C` and `δ`, the bound `δ ≤ η / (4 * (C + 1))` implies `2 * C * δ ≤ η`. -/
theorem terminal_window_error_budget {C δ η : ℝ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hsize : δ ≤ η / (4 * (C + 1))) :
    C * (2 * δ) ≤ η := by
  have hden : 0 < 4 * (C + 1) := by positivity
  have h := (le_div_iff₀ hden).mp hsize
  have hp := mul_nonneg hC hδ
  nlinarith only [h, hp, hδ]


end Critical2DKPZ.SHF.Moments

end
