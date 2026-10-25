/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.FirstMoment
public import Critical2DKPZ.SHF.Moments.WalkBounds
import Mathlib.Tactic

/-! # Uniform annealed density bounds and measurability -/

public section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

/-- The diffusively rescaled walk kernel is uniformly bounded at times bounded away from zero. -/
theorem scaled_srwKernel_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N n : ℕ, ε * N ≤ n → ∀ z : Site,
      ((N : ℝ) / 4) * srwKernel n z ≤ C := by
  obtain ⟨C, c, hC, hc, h⟩ := srwKernel_gaussianBound_all_times
  refine ⟨C / (4 * ε), by positivity, fun N n hgap z => ?_⟩
  have he : Real.exp (-c * ‖siteToPlane z‖ ^ 2 / ((n : ℝ) + 1)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (sq_nonneg _)) (by positivity))
  have hq : srwKernel n z ≤ C / ((n : ℝ) + 1) :=
    (h n z).trans (mul_le_of_le_one_right (by positivity) he)
  calc
    _ ≤ ((N : ℝ) / 4) * (C / ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = (C / 4) * ((N : ℝ) / ((n : ℝ) + 1)) := by ring
    _ ≤ (C / 4) * (1 / ε) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [div_le_div_iff₀ (by positivity) hε]
      linarith only [hgap]
    _ = _ := by ring

/-- Measurability in both continuum endpoints of the exact annealed density. -/
theorem measurable_integral_rescaledP2P (ϑ : ℝ) (N : ℕ) (s t : ℝ) :
    Measurable (fun p : Plane × Plane => ∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw) := by
  simp_rw [integral_rescaledP2P]
  have hq : Measurable (srwKernel (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))) :=
    measurable_of_countable _
  exact measurable_const.mul (hq.comp
    (((measurable_latticePoint N).comp measurable_snd).sub
      ((measurable_latticePoint N).comp measurable_fst)))

/-- One constant bounds every continuum endpoint pair for all sufficiently large scales. -/
theorem eventually_annealed_rescaledP2P_bound (ϑ : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ p : Plane × Plane,
      |∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw| ≤ C := by
  obtain ⟨C, hC, h⟩ := scaled_srwKernel_bound (half_pos (sub_pos.mpr hst))
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_gt_atTop 0,
    (tendsto_evenCeil_gap_div hs hst.le).eventually
      (lt_mem_nhds (half_lt_self (sub_pos.mpr hst)))] with N hN hgap
  intro p
  rw [integral_rescaledP2P, abs_of_nonneg (mul_nonneg (by positivity)
    (Critical2DKPZ.srwKernel_nonneg _ _))]
  apply h
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  exact ((lt_div_iff₀ hNr).mp hgap).le

end Critical2DKPZ.SHF.Moments
