/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.BlockTupleMeasures
public import Critical2DKPZ.SHF.Tsai.KernelMeasureTests
public import Critical2DKPZ.SHF.Tsai.BlockModification
public import Critical2DKPZ.SHF.DeltaBose.MomentKernelFormBounds

/-! # Block moments for arbitrary joint endpoint tests

Positive tensor moments determine the expected tuple measure by rectangle
uniqueness. The canonical locally finite modification then removes the
auxiliary everywhere-finiteness assumption, giving the joint-test identity
under the original moment axiom.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- For everywhere locally finite blocks, the expected tuple measure is the moment-kernel measure. -/
theorem HasDeltaBoseMoments.bind_blockTupleMeasure_eq_of_locallyFinite
    {θ τ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : Ω → Measure (Plane × Plane)} (hB : HasDeltaBoseMoments θ τ P B) (hτ : 0 < τ)
    (hlf : ∀ ω, IsLocallyFiniteMeasure (B ω)) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4) :
    P.bind (fun ω => blockTupleMeasure n (B ω)) =
      volume.withDensity (Function.uncurry (momentKernel n θ τ)) := by
  have hKm : Measurable (Function.uncurry (momentKernel n θ τ)) :=
    Measurable.comp
      (g := fun p : (ℝ × ℝ) × Configuration n × Configuration n =>
        momentKernel n p.1.1 p.1.2 p.2.1 p.2.2)
      (f := fun q : Configuration n × Configuration n => ((θ, τ), q))
      (measurable_momentKernel n) (measurable_const.prodMk measurable_id)
  obtain ⟨C, rate, _, hC⟩ := exists_formBound_momentKernel n θ
  have hForm := hC θ le_rfl τ hτ
  apply (kernelMeasure_eq_of_rectangles hKm ENNReal.ofReal_ne_top hForm _ ?_).symm
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
  have htuplem := measurable_blockTupleMeasure n B hB.1 hlf
  calc
    _ = ∫⁻ q, (∏ i, f i (q.1 i)) * ∏ i, g i (q.2 i)
        ∂volume.withDensity (Function.uncurry (momentKernel n θ τ)) :=
      measure_configurationRectangle_eq_lintegral_tensor _ A D hA hD
    _ = ∫⁻ x : Configuration n, ∫⁻ y : Configuration n,
        (∏ i, f i (x i)) * momentKernel n θ τ x y * ∏ i, g i (y i) :=
      lintegral_kernelMeasure_mul hKm hfp hgp
    _ = ∫⁻ ω, ∫⁻ q, (∏ i, f i (q.1 i)) * ∏ i, g i (q.2 i) ∂blockTupleMeasure n (B ω) ∂P :=
      (hB.lintegral_blockTupleMeasure_tensor hτ hn1 hn f g hf hg).symm
    _ = ∫⁻ q, (∏ i, f i (q.1 i)) * ∏ i, g i (q.2 i)
        ∂P.bind (fun ω => blockTupleMeasure n (B ω)) :=
      (Measure.lintegral_bind htuplem.aemeasurable ht.aemeasurable).symm
    _ = _ := (measure_configurationRectangle_eq_lintegral_tensor _ A D hA hD).symm

/-- The original block moment axiom evaluates every nonnegative measurable joint endpoint test. -/
theorem HasDeltaBoseMoments.lintegral_blockTupleMeasure_eq
    {θ τ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : Ω → Measure (Plane × Plane)} (hB : HasDeltaBoseMoments θ τ P B) (hτ : 0 < τ)
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4)
    (H : Configuration n × Configuration n → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ ω, ∫⁻ q, H q ∂blockTupleMeasure n (B ω) ∂P) =
      ∫⁻ q, momentKernel n θ τ q.1 q.2 * H q := by
  let E := CompactExhaustion.choice (Plane × Plane)
  let B' := RandomMeasure.locallyFiniteMeasureModification E B
  have hB' : HasDeltaBoseMoments θ τ P B' := hB.locallyFiniteMeasureModification E
  have hlf' (ω) : IsLocallyFiniteMeasure (B' ω) :=
    RandomMeasure.locallyFinite_locallyFiniteMeasureModification E B ω
  have heq : B' =ᵐ[P] B := RandomMeasure.ae_eq_radonValuedModification E P B hB.2.1
  have hKm : Measurable (Function.uncurry (momentKernel n θ τ)) :=
    Measurable.comp
      (g := fun p : (ℝ × ℝ) × Configuration n × Configuration n =>
        momentKernel n p.1.1 p.1.2 p.2.1 p.2.2)
      (f := fun q : Configuration n × Configuration n => ((θ, τ), q))
      (measurable_momentKernel n) (measurable_const.prodMk measurable_id)
  calc
    _ = ∫⁻ ω, ∫⁻ q, H q ∂blockTupleMeasure n (B' ω) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [heq] with ω hω
      rw [hω]
    _ = ∫⁻ q, H q ∂P.bind (fun ω => blockTupleMeasure n (B' ω)) :=
      (Measure.lintegral_bind (measurable_blockTupleMeasure n B' hB'.1 hlf').aemeasurable hH.aemeasurable).symm
    _ = _ := by
      rw [hB'.bind_blockTupleMeasure_eq_of_locallyFinite hτ hlf' hn1 hn,
        lintegral_withDensity_eq_lintegral_mul _ hKm hH]
      rfl

end Critical2DKPZ.SHF.Tsai

end
