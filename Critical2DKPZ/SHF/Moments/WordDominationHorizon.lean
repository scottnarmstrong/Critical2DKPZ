/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.PolymerCalculus.Clocks
import Mathlib.Tactic

/-! # A uniform CCR horizon for compact time windows -/

@[expose] public section

namespace Critical2DKPZ.SHF.Moments

open Filter

/-- The rounded duration, together with an extra terminal averaging window of
length `N + 1`, fits in a fixed integer multiple of `N` uniformly over the
compact time window. -/
theorem exists_evenClock_horizon_bound {τ T : ℝ} (hτ : 0 < τ) :
    ∃ B : ℕ, 1 ≤ B ∧ ∀ᶠ N : ℕ in atTop,
      ∀ s t : ℝ, 0 ≤ s → τ ≤ t - s → t ≤ T →
        evenCeil (N * t) - evenCeil (N * s) + N + 1 ≤ B * N := by
  let B : ℕ := ⌈|T| + 4⌉₊
  have hBabs : |T| + 4 ≤ (B : ℝ) := by
    dsimp [B]
    exact Nat.le_ceil _
  have hBreal : T + 4 ≤ (B : ℝ) := by
    exact le_trans (by linarith [le_abs_self T]) hBabs
  have hB : 1 ≤ B := by
    have hB4 : (4 : ℝ) ≤ (B : ℝ) := by
      linarith [hBabs, abs_nonneg T]
    exact le_trans (by norm_num : 1 ≤ 4) (by exact_mod_cast hB4)
  refine ⟨B, hB, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN
  intro s t hs hst ht
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht0 : 0 ≤ t := by linarith
  have hTlow : τ ≤ T := by
    calc
      τ ≤ t - s := hst
      _ ≤ t := by linarith
      _ ≤ T := ht
  have hTpos : 0 < T := lt_of_lt_of_le hτ hTlow
  have hspan : t - s ≤ T := by linarith
  have hdur := evenCeil_duration_error (s := (N : ℝ) * s)
    (t := (N : ℝ) * t) (mul_nonneg (Nat.cast_nonneg N) hs)
    (mul_nonneg (Nat.cast_nonneg N) ht0)
  have hdurUpper :
      ((evenCeil (N * t) : ℝ) - evenCeil (N * s) : ℝ) ≤
        (N : ℝ) * (t - s) + 2 := by
    have h := abs_lt.mp hdur
    have hclock :
        ((evenCeil (N * t) : ℝ) - evenCeil (N * s) : ℝ) -
          ((N : ℝ) * t - (N : ℝ) * s) < 2 := h.2
    have hmul : (N : ℝ) * t - (N : ℝ) * s = (N : ℝ) * (t - s) := by ring
    rw [hmul] at hclock
    linarith
  have hdurT :
      ((evenCeil (N * t) : ℝ) - evenCeil (N * s) : ℝ) ≤
        (N : ℝ) * T + 2 := by
    calc
      _ ≤ (N : ℝ) * (t - s) + 2 := hdurUpper
      _ ≤ (N : ℝ) * T + 2 := by
        have hmul := mul_le_mul_of_nonneg_left hspan (Nat.cast_nonneg N)
        linarith
  have hclockmono : evenCeil (N * s) ≤ evenCeil (N * t) := by
    apply evenCeil_mono
    exact mul_le_mul_of_nonneg_left (by linarith [hst]) (Nat.cast_nonneg N)
  have hreal :
      ((evenCeil (N * t) - evenCeil (N * s) + N + 1 : ℕ) : ℝ) ≤
        (B * N : ℕ) := by
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_one, Nat.cast_sub hclockmono,
      Nat.cast_mul]
    have hBmul : (N : ℝ) * (T + 4) ≤ (B : ℝ) * N := by
      calc
        (N : ℝ) * (T + 4) = (T + 4) * N := by ring
        _ ≤ (B : ℝ) * N := mul_le_mul_of_nonneg_right hBreal
          (Nat.cast_nonneg N)
    calc
      _ ≤ ((N : ℝ) * T + 2) + (N : ℝ) + 1 := by
        linarith [hdurT]
      _ ≤ (N : ℝ) * (T + 4) := by nlinarith
      _ ≤ (B : ℝ) * N := hBmul
  exact_mod_cast hreal

end Critical2DKPZ.SHF.Moments

end
