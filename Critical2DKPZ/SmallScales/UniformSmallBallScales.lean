/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SmallScales.SmallScaleCLTConsequences

/-! # A uniform-center summable small-ball sequence -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BoundedContinuousFunction Distributions Topology

universe u

namespace Critical2DKPZ.SmallScales

/-- A standard Gaussian small-scale limit and spatial translation invariance give a vanishing sequence of scales with geometrically summable small-ball probabilities, uniformly over the spatial center. -/
theorem exists_uniform_small_ball_scales_of_CLT_and_invariance
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hR7 : KpzTransportAt P H)
    {t : ℝ} (ht : 0 < t) (φ : TestFn)
    (hCLT : TendstoInDistribution
      (fun ε ω => H t 0 ω (φ.dilate ε 0) /
        Real.sqrt (Real.log (Real.log ε⁻¹)))
      (nhdsWithin 0 (Set.Ioi 0)) id (fun _ => P) (gaussianReal 0 1)) :
    ∃ ε : ℕ → ℝ,
      Tendsto ε atTop (nhdsWithin 0 (Set.Ioi 0)) ∧
        ∀ k, 0 < ε k ∧ ε k < 1 / ((k : ℝ) + 1) ∧
          ∀ x : Plane,
            (P {ω | |H t 0 ω (φ.dilate (ε k) x)| ≤ (k : ℝ)}).toNNReal <
              (1 / 2 : NNReal) ^ k := by
  have ha : Tendsto (fun ε : ℝ => Real.sqrt (Real.log (Real.log ε⁻¹)))
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    have h := Real.tendsto_sqrt_atTop.comp
      (Real.tendsto_log_atTop.comp
        (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero))
    convert h using 1
    ext ε
    rfl
  let p : ℕ → ℝ → NNReal := fun k ε =>
    (P {ω | |H t 0 ω (φ.dilate ε 0)| ≤ (k : ℝ)}).toNNReal
  have hp (k : ℕ) : Tendsto (p k) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    simpa only [p] using
      tendsto_measure_abs_le_zero_of_tendstoInDistribution P
        (fun ε ω => H t 0 ω (φ.dilate ε 0))
        (fun ε => Real.sqrt (Real.log (Real.log ε⁻¹))) ha hCLT (k : ℝ)
  obtain ⟨ε, hεlim, hε⟩ :=
    exists_sequence_tending_zero_with_summable_event_probabilities p hp
  refine ⟨ε, hεlim, ?_⟩
  intro k
  rcases hε k with ⟨hεpos, hεsmall, hprob⟩
  refine ⟨hεpos, hεsmall, ?_⟩
  intro x
  have hcenter := measure_abs_dilate_eq_of_KpzTransportAt P H hR7
    t (ε k) (k : ℝ) ht φ x
  rw [hcenter]
  exact hprob

end Critical2DKPZ.SmallScales

end
