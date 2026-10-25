/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordCutoffExhaustion
import Mathlib.Tactic

/-! # Compact approximations to the full continuum two-particle entrance -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter
open scoped CompactlySupported Topology

/-- Compact cutoff exhaustions approximate the full continuum entrance with its word normalization, using the same plateau as the uniform discrete cutoff estimate. -/
theorem exists_pairTwo_continuum_entrance_approximation
    (θ T : ℝ) (hT : 0 < T) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) :
    ∃ η : ℕ → C_c(ℝ × Plane, ℝ),
      (∀ k p, η k p ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ k, ∀ p ∈ tsupport (η k), 0 < p.1 ∧ p.1 < T) ∧
      (∀ (k : ℕ) (p : ℝ × Plane), T / ((k : ℝ) + 3) ≤ p.1 →
        p.1 ≤ T - T / ((k : ℝ) + 3) → ‖p.2‖ ≤ k → η k p = 1) ∧
      Tendsto (fun k => (1 / 4 : ℝ) * (∫ p : ℝ × (Plane × (Plane × Plane)),
        η k (p.1, p.2.2.1) *
          ((heatKernel p.1 (p.2.2.1 - p.2.1) * heatKernel p.1 (p.2.2.2 - p.2.2.1)) *
            pairTwoContinuumFuture θ (T - p.1) φ ![p.2.1, p.2.2.2] p.2.2.1)
        ∂(volume.restrict (Set.Ioo 0 T)).prod
          ((volume : Measure Plane).prod ((volume : Measure Plane).prod volume)))) atTop
        (𝓝 ((1 / 4 : ℝ) * (∫ p : ℝ × (Plane × (Plane × Plane)),
          (heatKernel p.1 (p.2.2.1 - p.2.1) * heatKernel p.1 (p.2.2.2 - p.2.2.1)) *
            pairTwoContinuumFuture θ (T - p.1) φ ![p.2.1, p.2.2.2] p.2.2.1
          ∂(volume.restrict (Set.Ioo 0 T)).prod
            ((volume : Measure Plane).prod ((volume : Measure Plane).prod volume))))) := by
  obtain ⟨η, hrange, hsupport, hplateau, hone⟩ := exists_pairTwo_entrance_cutoff_exhaustion T hT
  refine ⟨η, hrange, hsupport, hplateau, ?_⟩
  have habs (k : ℕ) (p : ℝ × Plane) : |η k p| ≤ 1 := by
    rw [abs_of_nonneg (hrange k p).1]
    exact (hrange k p).2
  have hlim (p : ℝ × Plane) (hp0 : 0 < p.1) (hpT : p.1 < T) :
      Tendsto (fun k => η k p) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hone p hp0 hpT] with k hk
    exact hk.symm
  exact (tendsto_integral_pairTwo_continuum_entrance_cutoffs θ T hT φ η habs hlim).2.const_mul _

end Critical2DKPZ.SHF.Moments
