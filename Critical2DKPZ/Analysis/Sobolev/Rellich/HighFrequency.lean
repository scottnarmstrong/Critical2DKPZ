/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. Bou-Rabee, Scott Armstrong
Modified for Critical2DKPZ, 2026.
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Rellich.Weight
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The high-frequency energy of order `s₀ ≤ s` is bounded by the weight ratio at the cutoff times the full energy of order `s`.

Adapted from A. Bou-Rabee's Lattice-Probability development (Apache-2.0). -/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal FourierTransform Topology

namespace Critical2DKPZ.Analysis.Sobolev.Rellich


/-- For `s₀ < s`, the Sobolev weight ratio `(1 + (2πΛ)²)^(s₀-s)` tends to zero as `Λ` tends to infinity. -/
theorem tendsto_weight_atTop_zero {s₀ s : ℝ} (h : s₀ < s) :
    Filter.Tendsto (fun Λ : ℝ => (1 + (2 * Real.pi * Λ) ^ 2) ^ (s₀ - s))
      Filter.atTop (𝓝 0) := by
  have hpos : (0 : ℝ) < s - s₀ := by linarith
  have h2 : Filter.Tendsto (fun Λ : ℝ => 2 * Real.pi * Λ) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) tendsto_id
  have h3 : Filter.Tendsto (fun Λ : ℝ => (2 * Real.pi * Λ) ^ 2) Filter.atTop Filter.atTop :=
    (by simpa [Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).comp h2)
  have h1 : Filter.Tendsto (fun Λ : ℝ => 1 + (2 * Real.pi * Λ) ^ 2) Filter.atTop Filter.atTop :=
    (by simpa [add_comm] using tendsto_atTop_add_const_right _ 1 h3)
  have h4 : Filter.Tendsto (fun Λ : ℝ => (1 + (2 * Real.pi * Λ) ^ 2) ^ (s - s₀))
      Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop hpos |>.comp h1
  have h5 : Filter.Tendsto (fun Λ : ℝ => ((1 + (2 * Real.pi * Λ) ^ 2) ^ (s - s₀))⁻¹)
      Filter.atTop (𝓝 0) :=
    h4.inv_tendsto_atTop
  refine h5.congr' ?_
  filter_upwards with Λ
  have hx : (0 : ℝ) ≤ 1 + (2 * Real.pi * Λ) ^ 2 := by nlinarith [sq_nonneg (2 * Real.pi * Λ)]
  rw [show s₀ - s = -(s - s₀) by ring, Real.rpow_neg hx]

end Critical2DKPZ.Analysis.Sobolev.Rellich

end
