/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.MixedBlockTensorMoments
public import Critical2DKPZ.SHF.Tsai.BlockJointMoments

/-! # The joint endpoint moment measure of a partially heat-replaced block

Positive tensor moments determine the full expected endpoint tuple measure.
The mixed form bound supplies finite spanning rectangles, and canonical
locally finite modifications extend the result to the almost-sure axioms.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The heat block is locally finite because its density is continuous. -/
theorem locallyFinite_heatBlock (τ : ℝ) : IsLocallyFiniteMeasure (heatBlock τ) :=
  IsLocallyFiniteMeasure.withDensity_ofReal
    ((continuous_heatKernel τ).comp (continuous_snd.sub continuous_fst))

/-- With everywhere locally finite blocks, the mixed endpoint tuple mean is its literal kernel measure. -/
theorem HasDeltaBoseMoments.bind_endpointTupleMeasure_ite_heat_eq_of_locallyFinite
    {θ τ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : Ω → Measure (Plane × Plane)} (hB : HasDeltaBoseMoments θ τ P B) (hτ : 0 < τ)
    (hlf : ∀ ω, IsLocallyFiniteMeasure (B ω)) {n : ℕ} (hn : n ≤ 4) (S : Finset (Fin n)) :
    P.bind (fun ω => endpointTupleMeasure (fun i => if i ∈ S then B ω else heatBlock τ)) =
      volume.withDensity (Function.uncurry (mixedBlockKernel n θ τ S)) := by
  classical
  let C (i : Fin n) (ω : Ω) := if i ∈ S then B ω else heatBlock τ
  have hCm (i) : Measurable (C i) := by
    by_cases hi : i ∈ S
    · simpa only [C, ite_eq_left hi] using hB.1
    · simp only [C, ite_eq_right hi]
      exact measurable_const
  have hClf (i) (ω) : IsLocallyFiniteMeasure (C i ω) := by
    dsimp only [C]
    split_ifs
    · exact hlf ω
    · exact locallyFinite_heatBlock τ
  have htuplem := measurable_endpointTupleMeasure C hCm hClf
  obtain ⟨c, hc, hF⟩ := exists_formBound_mixedBlockKernel n S θ hτ
  have hKm := measurable_mixedBlockKernel n θ τ S
  apply (kernelMeasure_eq_of_rectangles hKm hc hF _ ?_).symm
  intro A D hA hD
  let f (i : Fin n) : Plane → ℝ≥0∞ := (A i).indicator (fun _ => 1)
  let g (i : Fin n) : Plane → ℝ≥0∞ := (D i).indicator (fun _ => 1)
  have hf (i) : Measurable (f i) := measurable_const.indicator (hA i)
  have hg (i) : Measurable (g i) := measurable_const.indicator (hD i)
  have hfp : Measurable (fun x : Configuration n => ∏ i, f i (x i)) :=
    Finset.measurable_prod _ (fun i _ => (hf i).comp (measurable_pi_apply i))
  have hgp : Measurable (fun x : Configuration n => ∏ i, g i (x i)) :=
    Finset.measurable_prod _ (fun i _ => (hg i).comp (measurable_pi_apply i))
  have ht : Measurable (fun q : Configuration n × Configuration n =>
      (∏ i, f i (q.1 i)) * ∏ i, g i (q.2 i)) :=
    (hfp.comp measurable_fst).mul (hgp.comp measurable_snd)
  have heval (ω) : (∫⁻ q, (∏ i, f i (q.1 i)) * ∏ i, g i (q.2 i)
      ∂endpointTupleMeasure (C · ω)) = ∏ i, ∫⁻ p, f i p.1 * g i p.2 ∂C i ω := by
    have hsf (i) : SigmaFinite (C i ω) := by
      let : IsLocallyFiniteMeasure (C i ω) := hClf i ω
      infer_instance
    let : ∀ i, SigmaFinite (C i ω) := hsf
    exact lintegral_endpointTupleMeasure_tensor (C · ω) f g hf hg
  calc
    _ = ∫⁻ q, (∏ i, f i (q.1 i)) * ∏ i, g i (q.2 i)
        ∂volume.withDensity (Function.uncurry (mixedBlockKernel n θ τ S)) :=
      measure_configurationRectangle_eq_lintegral_tensor _ A D hA hD
    _ = ∫⁻ x : Configuration n, ∫⁻ y : Configuration n,
        (∏ i, f i (x i)) * mixedBlockKernel n θ τ S x y * ∏ i, g i (y i) :=
      lintegral_kernelMeasure_mul hKm hfp hgp
    _ = ∫⁻ ω, ∏ i, ∫⁻ p, f i p.1 * g i p.2 ∂C i ω ∂P :=
      (hB.lintegral_prod_ite_heat_eq hτ hn S f g hf hg).symm
    _ = ∫⁻ ω, ∫⁻ q, (∏ i, f i (q.1 i)) * ∏ i, g i (q.2 i)
        ∂endpointTupleMeasure (C · ω) ∂P := lintegral_congr (fun ω => (heval ω).symm)
    _ = ∫⁻ q, (∏ i, f i (q.1 i)) * ∏ i, g i (q.2 i)
        ∂P.bind (fun ω => endpointTupleMeasure (C · ω)) :=
      (Measure.lintegral_bind htuplem.aemeasurable ht.aemeasurable).symm
    _ = _ := (measure_configurationRectangle_eq_lintegral_tensor _ A D hA hD).symm


end Critical2DKPZ.SHF.Tsai

end
