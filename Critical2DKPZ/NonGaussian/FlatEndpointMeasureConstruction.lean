/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.FlatEndpointMeasure
public import Critical2DKPZ.NonGaussian.FlatEndpointBallMeasurability
import Critical2DKPZ.RandomMeasure.GeneralRandom

/-! # Radon-valued flat endpoint measure -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

universe u

namespace Critical2DKPZ.NonGaussian

/-- The flat terminal marginal has an almost surely locally finite version whose mean
is Lebesgue measure. -/
theorem exists_flatEndpoint_randomPlanarMeasure_of (ϑ : ℝ) {Ω : Type u}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hdense : DenseSHFAt ϑ P Z)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    ∃ ν : Differentiation.RandomPlanarMeasure Ω,
      (∀ᵐ ω ∂P, ν.measure ω = (Z s t ω).map Prod.snd) ∧
        ∀ A : Set Plane, MeasurableSet A →
          ∫⁻ ω, ν.measure ω A ∂P = (volume : Measure Plane) A := by
  let F : Ω → Measure Plane := fun ω => (Z s t ω).map Prod.snd
  have hF : Measurable F := by
    exact (Measure.measurable_map Prod.snd measurable_snd).comp (hZ.1 s t hs hst)
  let K : CompactExhaustion Plane := RandomMeasure.vagueCompactExhaustion Plane
  have hfinite : ∀ n : ℕ, ∀ᵐ ω ∂P, F ω (K n) < ∞ := by
    intro n
    let A : Set Plane := K n
    have hA : MeasurableSet A := (K.isCompact n).isClosed.measurableSet
    let f : Plane → ℝ≥0∞ := A.indicator fun _ => 1
    have hf : Measurable f := measurable_const.indicator hA
    have hmoment := flatEndpoint_terminalMarginal_lintegral_eq_of
      ϑ P Z hdense hs hst f hf
    have hmean : (∫⁻ ω, F ω A ∂P) = (volume : Measure Plane) A := by
      calc
        (∫⁻ ω, F ω A ∂P) = ∫⁻ ω, ∫⁻ x, f x ∂F ω ∂P := by
          apply lintegral_congr_ae
          exact Filter.Eventually.of_forall fun ω =>
            (lintegral_indicator_one hA : ∫⁻ x, f x ∂F ω = F ω A).symm
        _ = ∫⁻ x, f x := hmoment
        _ = (volume : Measure Plane) A := lintegral_indicator_one hA
    have hvol : (volume : Measure Plane) A < ∞ := (K.isCompact n).measure_lt_top
    have hnotTop : (∫⁻ ω, F ω A ∂P) ≠ ∞ := by
      rw [hmean]
      exact hvol.ne
    have hmeas : Measurable (fun ω => F ω A) :=
      (Measure.measurable_coe hA).comp hF
    exact ae_lt_top hmeas hnotTop
  have hLF : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (F ω) := by
    have hfiniteAll : ∀ᵐ ω ∂P, ∀ n : ℕ, F ω (K n) < ∞ :=
      ae_all_iff.2 hfinite
    filter_upwards [hfiniteAll] with ω hω
    exact (RandomMeasure.locallyFinite_iff_finite_compactExhaustion K (F ω)).2 hω
  let G : Ω → RandomMeasure.PositiveRadonMeasure Plane :=
    fun ω => RandomMeasure.radonValuedModification K F ω
  have hG : @Measurable Ω (RandomMeasure.PositiveRadonMeasure Plane)
      inferInstance (@borel _ (RandomMeasure.vagueTopology Plane)) G :=
    RandomMeasure.measurable_radonValuedModification K F hF
  let R : RandomMeasure.RandomRadonMeasure Ω Plane := ⟨G, hG⟩
  have hball (r : ℝ) : Measurable (fun p : Ω × Plane =>
      (R.value p.1).measure (Metric.closedBall p.2 r)) := by
    have hjoint := measurable_joint_closedBall_mass r
    have hGeval : @Measurable Ω (RandomMeasure.PositiveRadonMeasure Plane)
        inferInstance (MeasurableSpace.comap Subtype.val inferInstance) G :=
      (RandomMeasure.measurable_radonMap_iff_evaluation G).mp hG
    have hpair : Measurable (fun p : Ω × Plane => (G p.1, p.2)) :=
      (hGeval.comp measurable_fst).prodMk measurable_snd
    exact hjoint.comp hpair
  let ν : Differentiation.RandomPlanarMeasure Ω := ⟨R, hball⟩
  have hmod := RandomMeasure.ae_eq_radonValuedModification K P F hLF
  have hEq : ∀ᵐ ω ∂P, ν.measure ω = F ω := by
    filter_upwards [hmod] with ω hω
    exact hω
  refine ⟨ν, ?_, ?_⟩
  · filter_upwards [hEq] with ω hω
    simpa only [F] using hω
  · intro A hA
    let f : Plane → ℝ≥0∞ := A.indicator fun _ => 1
    have hf : Measurable f := measurable_const.indicator hA
    have hmoment := flatEndpoint_terminalMarginal_lintegral_eq_of
      ϑ P Z hdense hs hst f hf
    calc
      (∫⁻ ω, ν.measure ω A ∂P) = ∫⁻ ω, F ω A ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hEq] with ω hω
        rw [hω]
      _ = ∫⁻ ω, ∫⁻ x, f x ∂F ω ∂P := by
        apply lintegral_congr_ae
        exact Filter.Eventually.of_forall fun ω =>
          (lintegral_indicator_one hA : ∫⁻ x, f x ∂F ω = F ω A).symm
      _ = ∫⁻ x, f x := hmoment
      _ = (volume : Measure Plane) A := lintegral_indicator_one hA

end Critical2DKPZ.NonGaussian

end
