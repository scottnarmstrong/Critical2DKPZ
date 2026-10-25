/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.GaussianTailScaling
import Mathlib.Tactic

/-! # The Gaussian truncation makes the finite mesh budget vanish -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Overlapping windows of length `2S/m` have a total Gaussian oscillation
budget tending to zero. The truncation is essential to this mesh refinement. -/
theorem exists_gaussian_mesh_budget {C c S η ρ : ℝ}
    (hC : 0 < C) (hc : 0 < c) (hS : 0 < S) (hη : 0 < η) (hρ : 0 < ρ) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) *
      (C * (2 * (S / (m : ℝ))) / η ^ 2 *
        ∫ y : ℝ, squareTail (c * η / Real.sqrt (2 * (S / (m : ℝ)))) y ∂gaussianReal 0 1) < ρ := by
  let d := c * η / Real.sqrt (2 * S)
  have hd : 0 < d := by dsimp [d]; positivity
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => le_add_of_nonneg_right (by norm_num)) tendsto_natCast_atTop_atTop
  have ht := (Real.tendsto_sqrt_atTop.comp hn).const_mul_atTop hd
  have htail := gaussian_squareTail_tendsto_zero.comp ht
  have hlim : Tendsto (fun n : ℕ => (2 * C * S / η ^ 2) *
      (∫ y : ℝ, squareTail (d * Real.sqrt ((n : ℝ) + 1)) y ∂gaussianReal 0 1)) atTop (𝓝 0) := by
    have hh := htail.const_mul (2 * C * S / η ^ 2)
    change Tendsto (fun n : ℕ => (2 * C * S / η ^ 2) *
      (∫ y : ℝ, squareTail (d * Real.sqrt ((n : ℝ) + 1)) y ∂gaussianReal 0 1))
      atTop (𝓝 ((2 * C * S / η ^ 2) * 0)) at hh
    simpa only [mul_zero] using hh
  obtain ⟨n, hn⟩ := (hlim.eventually (Iio_mem_nhds hρ)).exists
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  have hN : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hq : c * η / Real.sqrt (2 * (S / ((n + 1 : ℕ) : ℝ))) =
      d * Real.sqrt ((n : ℝ) + 1) := by
    rw [show 2 * (S / ((n + 1 : ℕ) : ℝ)) = (2 * S) / ((n + 1 : ℕ) : ℝ) by ring,
      Real.sqrt_div (show 0 ≤ 2 * S by positivity), div_div_eq_mul_div]
    dsimp [d]
    push_cast
    ring
  rw [hq]
  calc
    _ = (2 * C * S / η ^ 2) *
        (∫ y : ℝ, squareTail (d * Real.sqrt ((n : ℝ) + 1)) y ∂gaussianReal 0 1) := by
      field_simp
    _ < ρ := hn

end Critical2DKPZ.Extensions.ScaleLimit
