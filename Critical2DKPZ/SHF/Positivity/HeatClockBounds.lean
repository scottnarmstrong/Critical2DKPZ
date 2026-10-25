/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.PolymerCalculus.Clocks
import Mathlib.Tactic

/-! # Eventual bounds for heat-start lattice durations -/

@[expose] public section

open Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Positivity

/-- For fixed `0 ≤ s < t`, the even-clock duration lies between `1` and `(t - s + 2) * N` for all sufficiently large lattice scales `N`. -/
theorem eventually_evenClock_duration_bounds {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ N ∧
      (1 : ℝ) ≤ (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s) : ℝ) ∧
      ((evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s) : ℝ) ≤
        (t - s + 2) * N) := by
  let D : ℝ := t - s
  have hD : 0 < D := by dsimp [D]; linarith
  have hlarge : ∀ᶠ N : ℕ in atTop, 4 / D < (N : ℝ) :=
    (tendsto_natCast_atTop_atTop.eventually_gt_atTop (4 / D))
  filter_upwards [hlarge] with N hN
  have hNreal : 0 < (N : ℝ) := lt_trans (by positivity : 0 < 4 / D) hN
  have hNpos : 0 < N := by exact_mod_cast hNreal
  have hNnat : 1 ≤ N := by omega
  have hND : 4 < (N : ℝ) * D := (div_lt_iff₀ hD).mp hN
  have hsN : 0 ≤ (N : ℝ) * s := mul_nonneg (Nat.cast_nonneg N) hs
  have htN : 0 ≤ (N : ℝ) * t := mul_nonneg (Nat.cast_nonneg N) (le_trans hs hst.le)
  let a := evenCeil ((N : ℝ) * s)
  let b := evenCeil ((N : ℝ) * t)
  have hab : a ≤ b := by
    dsimp [a, b]
    exact evenCeil_mono (mul_le_mul_of_nonneg_left hst.le (Nat.cast_nonneg N))
  let L := b - a
  have hLcast : (L : ℝ) = (b : ℝ) - a := by
    dsimp [L]
    exact Nat.cast_sub hab
  have hround := evenCeil_duration_error hsN htN
  have hLround : |(L : ℝ) - (N : ℝ) * D| < 2 := by
    have heq : (L : ℝ) - (N : ℝ) * D =
        (evenCeil ((N : ℝ) * t) : ℝ) - evenCeil ((N : ℝ) * s) -
          ((N : ℝ) * t - (N : ℝ) * s) := by
      rw [hLcast]
      dsimp [D, a, b]
      ring
    rw [heq]
    exact hround
  have hLbounds := abs_lt.mp hLround
  have hLlower : (1 : ℝ) < (L : ℝ) := by dsimp [D] at hND; linarith
  have hLupper : (L : ℝ) ≤ (t - s + 2) * N := by
    have hNone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNnat
    dsimp [D] at hLbounds ⊢
    nlinarith
  have hLupper' : (b : ℝ) - a ≤ (t - s + 2) * N := by
    rw [← hLcast]
    exact hLupper
  exact ⟨hNnat, by exact_mod_cast hLlower.le,
    by simpa only [a, b] using hLupper'⟩

end Critical2DKPZ.SHF.Positivity

end
