/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Lattice.Sampling
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Critical2DKPZ.MomentBounds.WeightedLatticeKernel
import Mathlib.Tactic

/-! # Elementary checks for CCR25

The examples concern the weighted lattice norm, the square completion in
Proposition 4.23, and Lemma B.1 of arXiv:2307.02453v3.
-/

@[expose] public noncomputable section
namespace Critical2DKPZ.Errata
open scoped ENNReal

/-- The origin term contradicts the squared lattice-sum bound at `q = 2` and `t = 12`. -/
theorem ccr25_large_weight_bound_false :
    ¬ (∑' z : Site, ENNReal.ofReal (Real.exp (-24 * ‖siteToPlane z‖))) ≤
      ENNReal.ofReal ((36 : ℝ) / 12 ^ 2) := by
  have h := ENNReal.le_tsum (f := fun z : Site => ENNReal.ofReal (Real.exp (-24 * ‖siteToPlane z‖))) 0
  simp only [MomentBounds.siteToPlane_zero, norm_zero, mul_zero, Real.exp_zero, ENNReal.ofReal_one] at h
  intro hb
  have hh := h.trans hb
  norm_num at hh

/-- The quadratic exponent has maximum `4 * c * t² * L`, attained at `8 * c * t * L`. -/
theorem ccr25_quadratic_maximum {c L : ℝ} (hc : 0 < c) (hL : 0 < L) (t : ℝ) :
    IsGreatest (Set.range (fun a : ℝ => t * a - a ^ 2 / (16 * c * L)))
      (4 * c * t ^ 2 * L) := by
  constructor
  · refine ⟨8 * c * t * L, ?_⟩
    field_simp
    ring
  · rintro _ ⟨a, rfl⟩
    have he : 4 * c * t ^ 2 * L - (t * a - a ^ 2 / (16 * c * L)) =
        (a - 8 * c * t * L) ^ 2 / (16 * c * L) := by field_simp; ring
    exact sub_nonneg.mp (he ▸ div_nonneg (sq_nonneg _) (by positivity))

/-- At `n = 3`, the ceiling half is two and exceeds the real half. -/
theorem ccr25_odd_half_step_false :
    ¬ max (⌊(3 : ℝ) / 2⌋₊ : ℝ) (⌈(3 : ℝ) / 2⌉₊ : ℝ) ≤ 3 / 2 := by
  have hc : ⌈(3 : ℝ) / 2⌉₊ = 2 := (Nat.ceil_eq_iff (by decide)).mpr (by norm_num)
  rw [hc]
  norm_num

/-- At `n = 1`, the floor half is smaller than the real half. -/
theorem ccr25_one_half_step_false :
    ¬ (1 : ℝ) / 3 ≤ (⌊(1 : ℝ) / 2⌋₊ : ℝ) := by
  norm_num

end Critical2DKPZ.Errata
