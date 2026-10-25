/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.PolymerCalculus.OverlapRescaling
import Mathlib.Tactic

/-! If integer horizons have a positive limiting ratio to `N`, the ratio of their logarithms tends to one. -/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.PolymerCalculus

/-- Positive macroscopic clock ratios do not change the leading logarithmic scale. -/
theorem tendsto_log_clock_div_log {M : ℕ → ℕ} {D : ℝ} (hD : 0 < D)
    (hM : Tendsto (fun N : ℕ => (M N : ℝ) / N) atTop (𝓝 D)) :
    Tendsto (fun N : ℕ => Real.log (M N) / Real.log N) atTop (𝓝 1) := by
  have hinv := tendsto_inv_atTop_zero.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h := ((tendsto_log_clock_ratio hD hM).mul hinv).const_add 1
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hn : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  dsimp only [Function.comp_apply]
  field_simp [hn]
  ring




end Critical2DKPZ.PolymerCalculus
