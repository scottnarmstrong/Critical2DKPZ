/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitClocks
import Mathlib.Tactic

/-! # Uniform interior-clock control for time-cutoff integration -/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

/-- One threshold works for the whole compact interior time triangle.
Entrance and run clocks stay uniformly positive and leave a positive tail. -/
theorem wordClocks_interior_uniform {τ ε : ℝ} (hε : 0 < ε)
    (nN : ℕ → ℕ) (hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ)) :
    ∀ᶠ N : ℕ in atTop, (nN N : ℝ) ≤ (τ + 1) * N ∧
      ∀ s r : ℝ, ε ≤ s → ε ≤ r → s + r ≤ τ - ε →
        (ε / 2) * N ≤ (wordEntranceClock N s : ℝ) ∧
        (ε / 2) * N ≤ ((⌊(N : ℝ) * r⌋₊ : ℕ) : ℝ) ∧
        wordEntranceClock N s + ⌊(N : ℝ) * r⌋₊ < nN N := by
  have hnear := hn.eventually (Ioo_mem_nhds (by linarith only [hε] : τ - ε / 2 < τ)
    (by linarith : τ < τ + 1))
  have hlarge : ∀ᶠ N : ℕ in atTop, (4 : ℝ) / ε ≤ N :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hnear, hlarge, eventually_gt_atTop 0] with N hnearN hlargeN hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hεN : 4 ≤ ε * (N : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hlargeN
  refine ⟨((div_lt_iff₀ hNr).mp hnearN.2).le, ?_⟩
  intro s r hs hr hsr
  have hspos : 0 < s := hε.trans_le hs
  have hrpos : 0 < r := hε.trans_le hr
  have hslo := Nat.lt_floor_add_one ((N : ℝ) * s)
  have hsupper := Nat.floor_le (show 0 ≤ (N : ℝ) * s by positivity)
  have hrlo := Nat.lt_floor_add_one ((N : ℝ) * r)
  have hrupper := Nat.floor_le (show 0 ≤ (N : ℝ) * r by positivity)
  have hnlo : (τ - ε / 2) * N < (nN N : ℝ) := (lt_div_iff₀ hNr).mp hnearN.1
  have hsN : ε * (N : ℝ) ≤ (N : ℝ) * s := by nlinarith only [mul_le_mul_of_nonneg_left hs hNr.le]
  have hrN : ε * (N : ℝ) ≤ (N : ℝ) * r := by nlinarith only [mul_le_mul_of_nonneg_left hr hNr.le]
  have hsumN : (N : ℝ) * s + N * r ≤ (τ - ε) * N := by
    nlinarith only [mul_le_mul_of_nonneg_left hsr hNr.le]
  refine ⟨?_, ?_, ?_⟩
  · simp only [wordEntranceClock, Nat.cast_add, Nat.cast_one]
    linarith only [hslo, hsN, hεN]
  · linarith only [hrlo, hrN, hεN]
  · have hfit : ((wordEntranceClock N s + ⌊(N : ℝ) * r⌋₊ : ℕ) : ℝ) < (nN N : ℝ) := by
      simp only [wordEntranceClock, Nat.cast_add, Nat.cast_one]
      linarith only [hsupper, hrupper, hsumN, hnlo, hεN]
    exact_mod_cast hfit

end Critical2DKPZ.SHF.Moments
