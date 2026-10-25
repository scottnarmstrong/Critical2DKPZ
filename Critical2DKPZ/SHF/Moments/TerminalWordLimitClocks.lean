/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TimeRounding
public import Critical2DKPZ.Renewal.LocalLimit
import Mathlib.Tactic

/-! # Time-cell clocks for the rescaled first-letter recursion -/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

/-- Entrance slices start at one, as in the exact first-letter recursion. -/
def wordEntranceClock (N : ℕ) (s : ℝ) : ℕ := ⌊(N : ℝ) * s⌋₊ + 1

/-- The remaining tail duration after the entrance and the collision run. -/
def wordRemainingClock (N n : ℕ) (s r : ℝ) : ℕ :=
  n - wordEntranceClock N s - ⌊(N : ℝ) * r⌋₊

/-- The scaled run clock `⌊Nr⌋ / N` converges to the positive macroscopic duration `r`. -/
theorem tendsto_wordRunClock_scaled {r : ℝ} (hr : 0 < r) :
    Tendsto (fun N : ℕ => ((⌊(N : ℝ) * r⌋₊ : ℕ) : ℝ) / N) atTop (𝓝 r) := by
  have hfloor := Renewal.tendsto_floor_div_succ tendsto_id (tendsto_const_nhds (x := r)) hr
  have hratio : Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ) / N)) atTop (𝓝 (1 : ℝ)) := by
    have hlim := (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_const_div_nat 1)
    simp only [add_zero] at hlim
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    push_cast
    field_simp [hNr]
  have hlim := hfloor.mul hratio
  simp only [mul_one] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hNs : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [id_eq]
  field_simp [hNp.ne', hNs]

/-- The shifted entrance clock has the same positive macroscopic time. -/
theorem tendsto_wordEntranceClock_scaled {s : ℝ} (hs : 0 < s) :
    Tendsto (fun N : ℕ => (wordEntranceClock N s : ℝ) / N) atTop (𝓝 s) := by
  have h := (tendsto_wordRunClock_scaled hs).add (tendsto_const_div_nat 1)
  simpa only [wordEntranceClock, Nat.cast_add, Nat.cast_one, add_div, add_zero] using h

/-- Interior entrance/run times fit in a moving horizon, and leave the
correct positive macroscopic duration for the tail induction. -/
theorem wordClocks_interior {τ s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (hsr : s + r < τ) (nN : ℕ → ℕ)
    (hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ)) :
    (∀ᶠ N : ℕ in atTop, wordEntranceClock N s + ⌊(N : ℝ) * r⌋₊ < nN N) ∧
    Tendsto (fun N : ℕ => (wordRemainingClock N (nN N) s r : ℝ) / N) atTop (𝓝 (τ - s - r)) := by
  have hlim := (hn.sub (tendsto_wordEntranceClock_scaled hs)).sub (tendsto_wordRunClock_scaled hr)
  have hpos := hlim.eventually (Ioi_mem_nhds (show 0 < τ - s - r by linarith only [hsr]))
  have hfit : ∀ᶠ N : ℕ in atTop, wordEntranceClock N s + ⌊(N : ℝ) * r⌋₊ < nN N := by
    filter_upwards [hpos, eventually_gt_atTop 0] with N hposN hN
    have hNp : (0 : ℝ) < N := by exact_mod_cast hN
    have hlt : ((wordEntranceClock N s : ℝ) + ((⌊(N : ℝ) * r⌋₊ : ℕ) : ℝ)) / N < (nN N : ℝ) / N := by
      rw [add_div]
      linarith only [hposN]
    have hc := (div_lt_div_iff_of_pos_right hNp).mp hlt
    exact_mod_cast hc
  refine ⟨hfit, ?_⟩
  apply hlim.congr'
  filter_upwards [hfit] with N hN
  rw [wordRemainingClock, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  ring

end Critical2DKPZ.SHF.Moments
