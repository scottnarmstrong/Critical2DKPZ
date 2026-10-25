/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitPotentialGreen
public import Critical2DKPZ.SHF.Moments.FirstMoment
public import Critical2DKPZ.Analysis.Lattice.Sampling
import Mathlib.Tactic

/-! # Cell sampling of the initial-gap envelope -/

@[expose] public noncomputable section

namespace Critical2DKPZ.SHF.Moments

/-- The inverse-distance estimate survives rounding both starting locations.
The singularity lies only on the continuum diagonal, independently of `N`. -/
theorem exists_cell_wordGapPotential_inverse_distance_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (N n : ℕ), 0 < N → ∀ a b : Plane, a ≠ b →
      Real.sqrt (N : ℝ) * wordGapPotential n (latticePoint N b - latticePoint N a) ≤
        C / ‖b - a‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_wordGapPotential_regularized_norm_bound
  refine ⟨4 * C, by positivity, fun N n hN a b hab => ?_⟩
  let z := latticePoint N b - latticePoint N a
  let s := Real.sqrt ((N : ℝ) / 2)
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hs2 : s ^ 2 = (N : ℝ) / 2 := Real.sq_sqrt (by positivity)
  have hsN : Real.sqrt (N : ℝ) ≤ 2 * s := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity, by nlinarith only [hs2]⟩
  have hd : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)
  have hrepr : ‖cellSample N b - cellSample N a‖ = s⁻¹ * ‖siteToPlane z‖ := by
    rw [cellSample, cellSample, ← latticeRepresentative_sub, latticeRepresentative,
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
  have hdist : ‖b - a‖ ≤ s⁻¹ * (‖siteToPlane z‖ + 2) := by
    calc
      _ ≤ dist b (cellSample N b) + dist (cellSample N b) (cellSample N a) +
          dist (cellSample N a) a := by
        rw [← dist_eq_norm]
        have h₁ := dist_triangle b (cellSample N b) a
        have h₂ := dist_triangle (cellSample N b) (cellSample N a) a
        linarith only [h₁, h₂]
      _ ≤ s⁻¹ + s⁻¹ * ‖siteToPlane z‖ + s⁻¹ := by
        apply add_le_add
        · apply add_le_add
          · simpa only [dist_comm] using dist_cellSample_le hN b
          · exact le_of_eq (by simpa only [dist_eq_norm] using hrepr)
        · exact dist_cellSample_le hN a
      _ = _ := by ring
  have hscaled : ‖b - a‖ * Real.sqrt (N : ℝ) ≤ 4 * (1 + ‖siteToPlane z‖) := by
    calc
      _ ≤ (s⁻¹ * (‖siteToPlane z‖ + 2)) * (2 * s) :=
        mul_le_mul hdist hsN (Real.sqrt_nonneg _) (by positivity)
      _ = 2 * (‖siteToPlane z‖ + 2) := by field_simp
      _ ≤ _ := by have hn := norm_nonneg (siteToPlane z); linarith only [hn]
  calc
    _ ≤ Real.sqrt (N : ℝ) * (C / (1 + ‖siteToPlane z‖)) :=
      mul_le_mul_of_nonneg_left (hbound n z) (Real.sqrt_nonneg _)
    _ ≤ 4 * C / ‖b - a‖ := by
      apply (le_div_iff₀ hd).mpr
      have hp : 0 < 1 + ‖siteToPlane z‖ := by positivity
      calc
        _ = C * ((‖b - a‖ * Real.sqrt (N : ℝ)) / (1 + ‖siteToPlane z‖)) := by ring
        _ ≤ C * 4 := mul_le_mul_of_nonneg_left ((div_le_iff₀ hp).mpr hscaled) hC.le
        _ = _ := mul_comm _ _

end Critical2DKPZ.SHF.Moments
