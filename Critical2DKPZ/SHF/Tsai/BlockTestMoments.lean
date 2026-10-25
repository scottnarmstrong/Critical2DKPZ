/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.BlockJointMoments
public import Critical2DKPZ.SHF.Tsai.EndpointMomentIntegration

/-! # Block moments on arbitrary endpoint tests

The full endpoint moment measure supplies positive moments without any
spatial L2 restriction. For real tests, integrability against that common
moment measure gives product integrability and its exact expectation. This
is the form needed after conditioning a chain on all but one block.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Positive products of arbitrary measurable endpoint tests have the literal joint block moment. -/
theorem HasDeltaBoseMoments.lintegral_prod_tests_eq {θ τ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {B : Ω → Measure (Plane × Plane)}
    (hB : HasDeltaBoseMoments θ τ P B) (hτ : 0 < τ) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4)
    (F : Fin n → Plane × Plane → ℝ≥0∞) (hF : ∀ i, Measurable (F i)) :
    (∫⁻ ω, ∏ i, (∫⁻ p, F i p ∂B ω) ∂P) =
      ∫⁻ q : Configuration n × Configuration n, momentKernel n θ τ q.1 q.2 *
        ∏ i, F i (q.1 i, q.2 i) := by
  have hH : Measurable (fun q : Configuration n × Configuration n => ∏ i, F i (q.1 i, q.2 i)) :=
    Finset.measurable_prod _ (fun i _ => (hF i).comp
      (((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)))
  rw [← hB.lintegral_blockTupleMeasure_eq hτ hn1 hn _ hH]
  apply lintegral_congr_ae
  filter_upwards [hB.2.1] with ω hω
  let : IsLocallyFiniteMeasure (B ω) := hω
  exact (lintegral_endpointTupleMeasure_prod (fun _ => B ω) F hF).symm

/-- Integrable joint endpoint tests give integrable real products and their exact block moment. -/
theorem HasDeltaBoseMoments.integral_prod_tests_eq {θ τ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {B : Ω → Measure (Plane × Plane)}
    (hB : HasDeltaBoseMoments θ τ P B) (hτ : 0 < τ) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4)
    (F : Fin n → Plane × Plane → ℝ)
    (hI : Integrable (fun q : Configuration n × Configuration n => ∏ i, F i (q.1 i, q.2 i))
      (volume.withDensity (Function.uncurry (momentKernel n θ τ)))) :
    Integrable (fun ω => ∏ i, ∫ p, F i p ∂B ω) P ∧
      (∫ ω, ∏ i, (∫ p, F i p ∂B ω) ∂P) =
        ∫ q : Configuration n × Configuration n, ∏ i, F i (q.1 i, q.2 i)
          ∂volume.withDensity (Function.uncurry (momentKernel n θ τ)) := by
  let E := CompactExhaustion.choice (Plane × Plane)
  let B' := RandomMeasure.locallyFiniteMeasureModification E B
  have hB' : HasDeltaBoseMoments θ τ P B' := hB.locallyFiniteMeasureModification E
  have hlf (ω) : IsLocallyFiniteMeasure (B' ω) :=
    RandomMeasure.locallyFinite_locallyFiniteMeasureModification E B ω
  have heq : B' =ᵐ[P] B := RandomMeasure.ae_eq_radonValuedModification E P B hB.2.1
  have hmean := hB'.bind_blockTupleMeasure_eq_of_locallyFinite hτ hlf hn1 hn
  obtain ⟨houter, hmoment⟩ := integral_prod_tests_of_endpointTuple_mean P
    (fun _ : Fin n => B') (fun _ => hB'.1) (fun _ => hlf) _ hmean F hI
  have hprod : (fun ω => ∏ i, ∫ p, F i p ∂B' ω) =ᵐ[P]
      fun ω => ∏ i, ∫ p, F i p ∂B ω := by
    filter_upwards [heq] with ω hω
    rw [hω]
  exact ⟨houter.congr hprod, (integral_congr_ae hprod).symm.trans hmoment⟩

end Critical2DKPZ.SHF.Tsai

end
