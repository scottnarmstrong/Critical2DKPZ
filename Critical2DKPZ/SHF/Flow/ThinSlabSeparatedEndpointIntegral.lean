/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.TwoParticleEndpointForms
public import Critical2DKPZ.SHF.Tsai.KernelChainPaths

/-! # General endpoint tests for the separated continuum kernels -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.DeltaBose Critical2DKPZ.SHF.Tsai
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- A general measurable endpoint test of the separated continuum blocks integrates against
the spatial composition of their two kernels and their connector. -/
theorem lintegral_slabSeparatedMomentPiMeasure_endpoint (θ : ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    {C H : Configuration 2 → Configuration 2 → ℝ≥0∞}
    (hC : Measurable (Function.uncurry C)) (hH : Measurable (Function.uncurry H)) :
    (∫⁻ p, C (p 0).2 (p 1).1 * H (p 0).1 (p 1).2
      ∂slabSeparatedMomentPiMeasure θ a b) =
      ∫⁻ x, ∫⁻ y,
        spatialKernelComp volume (momentKernel 2 θ a)
          (spatialKernelComp volume C (momentKernel 2 θ b)) x y * H x y := by
  let μ := slabMomentKernelEndpointMeasure θ a
  let ν := slabMomentKernelEndpointMeasure θ b
  have hμloc : IsLocallyFiniteMeasure μ := locallyFinite_momentKernelMeasure 2 θ ha
  have hνloc : IsLocallyFiniteMeasure ν := locallyFinite_momentKernelMeasure 2 θ hb
  have : SigmaFinite μ := @sigmaFinite_of_locallyFinite _ _ μ _ _ hμloc
  have : SigmaFinite ν := @sigmaFinite_of_locallyFinite _ _ ν _ _ hνloc
  let J (p : (Configuration 2 × Configuration 2) ×
      (Configuration 2 × Configuration 2)) : ℝ≥0∞ := C p.1.2 p.2.1 * H p.1.1 p.2.2
  have hJ : Measurable J :=
    (hC.comp (measurable_fst.snd.prodMk measurable_snd.fst)).mul
      (hH.comp (measurable_fst.fst.prodMk measurable_snd.snd))
  have hpi := (measurePreserving_finTwoArrow_vec μ ν).lintegral_comp hJ
  have hsource : (∫⁻ p, C (p 0).2 (p 1).1 * H (p 0).1 (p 1).2
      ∂slabSeparatedMomentPiMeasure θ a b) = ∫⁻ p, J p ∂μ.prod ν := by
    have hm : slabSeparatedMomentPiMeasure θ a b = Measure.pi ![μ, ν] := by
      unfold slabSeparatedMomentPiMeasure
      congr 1
      funext i
      fin_cases i <;> rfl
    rw [hm]
    exact hpi
  have hKa := measurable_slabMomentKernelTwo θ a
  have hKb := measurable_slabMomentKernelTwo θ b
  let B (p : Configuration 2 × Configuration 2) : ℝ≥0∞ :=
    ∫⁻ y, momentKernel 2 θ b p.2 y * H p.1 y
  have hB : Measurable B := by
    have hm : Measurable (fun q : (Configuration 2 × Configuration 2) × Configuration 2 =>
        momentKernel 2 θ b q.1.2 q.2 * H q.1.1 q.2) :=
      (hKb.comp (measurable_fst.snd.prodMk measurable_snd)).mul
        (hH.comp (measurable_fst.fst.prodMk measurable_snd))
    exact hm.lintegral_prod_right'
  let A (p : Configuration 2 × Configuration 2) : ℝ≥0∞ :=
    ∫⁻ w, C p.2 w * B (p.1, w)
  have hA : Measurable A := by
    have hm : Measurable (fun q : (Configuration 2 × Configuration 2) × Configuration 2 =>
        C q.1.2 q.2 * B (q.1.1, q.2)) :=
      (hC.comp (measurable_fst.snd.prodMk measurable_snd)).mul
        (hB.comp (measurable_fst.fst.prodMk measurable_snd))
    exact hm.lintegral_prod_right'
  calc
    _ = ∫⁻ p, ∫⁻ q, J (p, q) ∂ν ∂μ := by
      rw [hsource, lintegral_prod _ hJ.aemeasurable]
    _ = ∫⁻ p, A p ∂μ := by
      apply lintegral_congr
      intro p
      have hHx : Measurable (H p.1) := hH.comp (measurable_const.prodMk measurable_id)
      exact lintegral_kernelMeasure_connector hKb hC hHx p.2
    _ = ∫⁻ x, ∫⁻ z, momentKernel 2 θ a x z * A (x, z) := by
      change (∫⁻ p, A p ∂(volume.prod volume).withDensity
        (Function.uncurry (momentKernel 2 θ a))) = _
      rw [lintegral_withDensity_eq_lintegral_mul _ hKa hA]
      exact lintegral_prod _ (hKa.mul hA).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro x
      have hHx : Measurable (H x) := hH.comp (measurable_const.prodMk measurable_id)
      rw [spatialKernelComp_action_eq volume volume hKa
        (measurable_spatialKernelComp volume hC hKb) hHx x]
      apply lintegral_congr
      intro z
      exact congrArg (fun q : ℝ≥0∞ => momentKernel 2 θ a x z * q)
        (spatialKernelComp_action_eq volume volume hC hKb hHx z).symm

/-- Inserting the free two-particle heat connector gives the free-middle composition kernel,
for every nonnegative measurable endpoint test. -/
theorem lintegral_slabSeparatedMomentPiMeasure_freeEndpoint (θ : ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (v : ℝ)
    {H : Configuration 2 → Configuration 2 → ℝ≥0∞}
    (hH : Measurable (Function.uncurry H)) :
    (∫⁻ p, ENNReal.ofReal (freeKernel 2 v (p 0).2 (p 1).1) * H (p 0).1 (p 1).2
      ∂slabSeparatedMomentPiMeasure θ a b) =
      ∫⁻ x, ∫⁻ y, slabTwoParticleFreeMiddleComp θ a v b x y * H x y := by
  have hp : Measurable (fun p : Configuration 2 × Configuration 2 => (v, p)) :=
    measurable_const.prodMk measurable_id
  have hC : Measurable (Function.uncurry
      (fun x y : Configuration 2 => ENNReal.ofReal (freeKernel 2 v x y))) :=
    ((measurable_freeKernel 2).comp hp).ennreal_ofReal
  exact lintegral_slabSeparatedMomentPiMeasure_endpoint θ ha hb hC hH

end Critical2DKPZ.SHF.Flow

end
