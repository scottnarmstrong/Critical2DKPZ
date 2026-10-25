/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedDiagramScalar
public import Critical2DKPZ.SHF.Tsai.ConjugatedAveragingWindow
public import Critical2DKPZ.SHF.Tsai.ConjugatedLogarithmicRate
import Mathlib.Tactic

/-! # Uniform scalar constants for the conjugated diagram bound -/

@[expose] public section

namespace Critical2DKPZ.SHF.Tsai

/-- One scalar constant controls the diagram majorant for all word lengths, admissible damping rates, and positive times. -/
theorem exists_scalar_conjugated_diagram_bound (n : ℕ) (θ g c₀ R P S J : ℝ)
    (hg : 0 ≤ g) (hc₀ : 0 ≤ c₀) (hR : 0 ≤ R) (hP : 0 ≤ P) (hS : 0 ≤ S) (hJ : 0 ≤ J) :
    ∃ c : ℝ, 1 ≤ c ∧ 2 * c₀ ≤ c ∧ R ≤ c ∧ g + Real.exp (2 * max θ 0 + 1) ≤ c ∧
      ∀ (m : ℕ) (rate t : ℝ), c + 3 ≤ rate → 0 < t →
        Real.exp ((rate + 1 / t) * (t + 1 / (rate + 1 / t - c₀))) *
          (2 : ℝ) ^ (n * (2 * (m + 1) + 1)) * P *
          (J / (Real.log (rate + 1 / t - g) - θ)) *
          (S * J / (Real.log (rate + 1 / t - g) - θ)) ^ m ≤
        c ^ (m + 1) * (c / Real.log (rate - c - 1)) ^ m * Real.exp (rate * t) := by
  let A : ℝ := P * Real.exp 3 * (2 : ℝ) ^ (3 * n) * J
  let B : ℝ := (2 : ℝ) ^ (2 * n + 1) * S * J
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hE : 0 < Real.exp (2 * max θ 0 + 1) := Real.exp_pos _
  let c : ℝ := 2 * c₀ + R + g + Real.exp (2 * max θ 0 + 1) + A + B + 3
  have hc1 : 1 ≤ c := by dsimp [c]; linarith only [hc₀, hR, hg, hA, hB, hE]
  have h2c : 2 * c₀ ≤ c := by dsimp [c]; linarith only [hR, hg, hA, hB, hE]
  have hRc : R ≤ c := by dsimp [c]; linarith only [hc₀, hg, hA, hB, hE]
  have hgc : g + Real.exp (2 * max θ 0 + 1) ≤ c := by
    dsimp [c]
    linarith only [hc₀, hR, hA, hB]
  have hAc : A ≤ c := by dsimp [c]; linarith only [hc₀, hR, hg, hB, hE]
  have hBc : B ≤ c := by dsimp [c]; linarith only [hc₀, hR, hg, hA, hE]
  have hc0 : 0 ≤ c := zero_le_one.trans hc1
  refine ⟨c, hc1, h2c, hRc, hgc, ?_⟩
  intro m rate t hrate ht
  have hcr : c ≤ rate := by linarith only [hrate]
  have hwindow := conjugated_averaging_window_bounds hc₀ (h2c.trans hcr) ht
  have hlam : rate ≤ rate + 1 / t := le_add_of_nonneg_right (one_div_pos.mpr ht).le
  have hlog := conjugated_collision_log_rate_bounds hgc hrate hlam
  let L : ℝ := Real.log (rate - c - 1)
  have hL : 0 < L := hlog.1
  have hExp : Real.exp ((rate + 1 / t) * (t + 1 / (rate + 1 / t - c₀))) ≤
      Real.exp 3 * Real.exp (rate * t) := by
    calc
      _ ≤ Real.exp (rate * t + 3) := Real.exp_le_exp.mpr hwindow.2.2.2.2
      _ = _ := by rw [Real.exp_add]; exact mul_comm _ _
  have hcore := scalar_averaged_diagram_le (n := n) (m := m) hP hS hJ hL hlog.2.1 hlog.2.2 hExp
  have hcSquare : c ≤ c ^ 2 := by
    simpa only [mul_one, pow_two] using mul_le_mul_of_nonneg_left hc1 hc0
  have hBcSquare : B ≤ c ^ 2 := hBc.trans hcSquare
  have hDiv : B / L ≤ c ^ 2 / L := div_le_div_of_nonneg_right hBcSquare hL.le
  have hPow := pow_le_pow_left₀ (div_nonneg hB hL.le) hDiv m
  have hCap := mul_le_mul hAc hPow (pow_nonneg (div_nonneg hB hL.le) m) hc0
  have hPower : c * (c ^ 2 / L) ^ m = c ^ (m + 1) * (c / L) ^ m := by
    rw [show c ^ 2 / L = c * (c / L) by ring, mul_pow, pow_succ]
    ring
  calc
    _ ≤ A * (B / L) ^ m * Real.exp (rate * t) := hcore
    _ ≤ (c * (c ^ 2 / L) ^ m) * Real.exp (rate * t) :=
      mul_le_mul_of_nonneg_right hCap (Real.exp_pos _).le
    _ = _ := by rw [hPower]

end Critical2DKPZ.SHF.Tsai

end
