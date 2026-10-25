/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.EntranceMixedCenter
import Mathlib.Tactic

/-! # Uniform spatial tails for tested collision entrances -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open Filter
open scoped Topology

private theorem spatial_tail_linear_envelope {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (c : Plane) (hc : ‖c‖ ≤ R / 2) (F : ℝ × Plane → ℝ)
    (hF : ∀ u x, |F (u, x)| ≤ M)
    (hzero : ∀ u x, ‖x‖ ≤ R → F (u, x) = 0) :
    ∀ u x, 0 ≤ u → |(|F (u, x)|)| ≤ (2 * M / R) * (u + ‖x - c‖) := by
  intro u x hu
  by_cases hx : ‖x‖ ≤ R
  · rw [hzero u x hx, abs_zero, abs_zero]
    positivity
  · have hdist : R / 2 ≤ ‖x - c‖ := by
      have hnorm : ‖x‖ ≤ ‖x - c‖ + ‖c‖ := by
        simpa only [sub_add_cancel] using norm_add_le (x - c) c
      linarith only [hc, hnorm, lt_of_not_ge hx]
    rw [abs_abs]
    calc
      |F (u, x)| ≤ M := hF u x
      _ = (2 * M / R) * (R / 2) := by field_simp
      _ ≤ (2 * M / R) * (u + ‖x - c‖) :=
        mul_le_mul_of_nonneg_left (hdist.trans (le_add_of_nonneg_left hu)) (by positivity)

/-- A bounded test supported outside a large ball has a small collision entrance integral for starting sites in the half-sized ball. The constants are uniform in the starting sites, clock window and tests satisfying the stated bounds. -/
theorem collisionEntrance_spatialTail_le :
    ∃ Creturn Cmoment : ℝ, 0 < Creturn ∧ 0 < Cmoment ∧
      ∀ N K : ℕ, 0 < N → ∀ a b : Site, ∀ R M : ℝ, 0 < R → 0 ≤ M →
      ‖latticeRepresentative N a‖ ≤ R / 2 → ‖latticeRepresentative N b‖ ≤ R / 2 →
      ∀ F : ℝ × Plane → ℝ, (∀ u x, |F (u, x)| ≤ M) →
      (∀ u x, ‖x‖ ≤ R → F (u, x) = 0) →
      |collisionEntrance N 0 K a b F| ≤
        (2 * M / R) * (Creturn * (((K : ℝ) + 1) / N) +
          2 * Cmoment * (Real.sqrt ((N : ℝ) / 2))⁻¹ * Real.sqrt ((K : ℝ) + 1)) := by
  obtain ⟨Cr, Cm, hCr, hCm, hbound⟩ := exists_collisionEntrance_abs_le_linear_center
  refine ⟨Cr, Cm, hCr, hCm, ?_⟩
  intro N K hN a b R M hR hM ha hb F hF hzero
  let B : ℝ := (2 * M / R) * (Cr * (((K : ℝ) + 1) / N) +
    2 * Cm * (Real.sqrt ((N : ℝ) / 2))⁻¹ * Real.sqrt ((K : ℝ) + 1))
  have hd (c : Site) (hc : ‖latticeRepresentative N c‖ ≤ R / 2) :
      collisionEntrance N 0 K c c (fun p => |F p|) ≤ B := by
    have he := hbound N K hN c (latticeRepresentative N c) (2 * M / R)
      (by positivity) (fun p => |F p|)
      (spatial_tail_linear_envelope hR hM _ hc F hF hzero)
    simp only [sub_self, norm_zero, zero_mul, add_zero] at he
    exact (le_abs_self _).trans he
  have he := collisionEntrance_abs_le_diagonal_average N 0 K a b F
  have hda := hd a ha
  have hdb := hd b hb
  change |collisionEntrance N 0 K a b F| ≤ B
  linarith only [he, hda, hdb]

end Critical2DKPZ.SHF.Moments
