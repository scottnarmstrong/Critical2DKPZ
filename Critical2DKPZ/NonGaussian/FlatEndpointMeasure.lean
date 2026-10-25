/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.Inputs
public import Critical2DKPZ.Differentiation.RandomHeat
public import Critical2DKPZ.SHF.Tsai.BlockMarginals
import Critical2DKPZ.RandomMeasure.GeneralRandom
import Critical2DKPZ.RandomMeasure.GeneralTests

/-! # The flat endpoint random measure -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

universe u

namespace Critical2DKPZ.NonGaussian

/-- The mean of the flat terminal marginal is Lebesgue measure, as tested against every
nonnegative measurable function. -/
theorem flatEndpoint_terminalMarginal_lintegral_eq_of (ϑ : ℝ) {Ω : Type u}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hdense : DenseSHFAt ϑ P Z)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (f : Plane → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, ∫⁻ x : Plane, f x ∂(Z s t ω).map Prod.snd ∂P) =
      ∫⁻ x : Plane, f x := by
  let D : Set ℝ := {s, t}
  have hD : D.Countable := by
    simp only [D, Set.countable_insert, Set.countable_singleton]
  have hDnonneg : ∀ r ∈ D, 0 ≤ r := by
    intro r hr
    simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact hs
    · linarith only [hst, hs]
  have hsD : s ∈ D := by simp [D]
  have htD : t ∈ D := by simp [D]
  have hB : Critical2DKPZ.SHF.Tsai.HasDeltaBoseMoments
      (ϑ - Real.eulerMascheroniConstant) (t - s) P (Z s t) :=
    (hdense D hD hDnonneg).hasDeltaBoseMoments hsD htD hst
  have hterminal := hB.lintegral_terminal_marginal (sub_pos.mpr hst) f hf
  have hmap (ω : Ω) :
      (∫⁻ x : Plane, f x ∂(Z s t ω).map Prod.snd) =
        ∫⁻ p : Plane × Plane, f p.2 ∂Z s t ω := by
    rw [lintegral_map hf measurable_snd]
  calc
    (∫⁻ ω, ∫⁻ x : Plane, f x ∂(Z s t ω).map Prod.snd ∂P) =
        ∫⁻ ω, ∫⁻ p : Plane × Plane, f p.2 ∂Z s t ω ∂P := by
          apply lintegral_congr_ae
          exact Filter.Eventually.of_forall hmap
    _ = ∫⁻ x : Plane, f x := hterminal

end Critical2DKPZ.NonGaussian

end
