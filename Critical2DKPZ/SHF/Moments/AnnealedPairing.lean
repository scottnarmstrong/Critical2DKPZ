/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.AnnealedBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! # Compactly supported pairings of the annealed density -/

public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

/-- Convergence after pairing the annealed density with an arbitrary signed compact test. -/
theorem tendsto_pairing_annealed_rescaledP2P (ϑ : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    {φ : Plane × Plane → ℝ} (hφ : Continuous φ) (hφs : HasCompactSupport φ) :
    Tendsto (fun N : ℕ => ∫ p : Plane × Plane,
      φ p * (∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw)) atTop
      (𝓝 (∫ p : Plane × Plane, φ p * heatKernel (t - s) (p.2 - p.1))) := by
  obtain ⟨C, _, hC⟩ := eventually_annealed_rescaledP2P_bound ϑ hs hst
  apply tendsto_integral_filter_of_dominated_convergence (fun p => C * |φ p|)
  · exact Filter.Eventually.of_forall fun N =>
      (hφ.measurable.mul (measurable_integral_rescaledP2P ϑ N s t)).aestronglyMeasurable
  · filter_upwards [hC] with N hN
    exact Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_mul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hN p) (abs_nonneg _)
  · exact ((hφ.integrable_of_hasCompactSupport hφs).norm.const_mul C)
  · exact Filter.Eventually.of_forall fun p =>
      tendsto_const_nhds.mul (tendsto_integral_rescaledP2P ϑ hs hst p)

end Critical2DKPZ.SHF.Moments
