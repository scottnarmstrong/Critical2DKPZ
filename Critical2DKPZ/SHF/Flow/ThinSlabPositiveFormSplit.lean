/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabPositiveConnectorForm
public import Critical2DKPZ.SHF.Flow.ThinSlabConnectorActionSplit
import Mathlib.Tactic

/-! # Free-plus-correction splitting of continuum positive connector forms -/

@[expose] public noncomputable section
open MeasureTheory Critical2DKPZ.DeltaBose
open scoped ENNReal
namespace Critical2DKPZ.SHF.Flow

private theorem measurable_slabParamAction
    {L F : Configuration 2 → Configuration 2 → ℝ≥0∞}
    (hL : Measurable (Function.uncurry L)) (hF : Measurable (Function.uncurry F)) :
    Measurable (fun p : Configuration 2 × Configuration 2 => ∫⁻ z, L p.2 z * F p.1 z) := by
  have h : Measurable (fun p : (Configuration 2 × Configuration 2) × Configuration 2 =>
      L p.1.2 p.2 * F p.1.1 p.2) :=
    (hL.comp (f := fun p : (Configuration 2 × Configuration 2) × Configuration 2 =>
      (p.1.2, p.2)) (by fun_prop)).mul
      (hF.comp (f := fun p : (Configuration 2 × Configuration 2) × Configuration 2 =>
        (p.1.1, p.2)) (by fun_prop))
  exact h.lintegral_prod_right

/-- The long second block splits into the heat-connected block and the
one-collision correction form, before converting any integral to real values. -/
theorem slabPositiveConnectorForm_free_add_correction_of {θ r v b : ℝ}
    (hSG : MomentKernelTwoSemigroup θ) (hv : 0 < v) (hb : 0 < b)
    (F K : Configuration 2 → Configuration 2 → ℝ≥0∞)
    (hF : Measurable (Function.uncurry F)) (hK : Measurable (Function.uncurry K)) :
    slabPositiveConnectorForm θ r (v + b) F K =
      slabPositiveConnectorForm θ r b F
        (spatialKernelComp volume K (fun x y => ENNReal.ofReal (freeKernel 2 v x y))) +
      slabPositiveConnectorForm θ r b F (spatialKernelComp volume K (twoParticleCorrection θ v)) := by
  have hQ (t : ℝ) : Measurable (Function.uncurry (momentKernel 2 θ t)) :=
    Measurable.comp (g := fun p : (ℝ × ℝ) × Configuration 2 × Configuration 2 =>
      momentKernel 2 p.1.1 p.1.2 p.2.1 p.2.2)
      (f := fun p : Configuration 2 × Configuration 2 => ((θ, t), p))
      (measurable_momentKernel 2) (measurable_const.prodMk measurable_id)
  let P : Configuration 2 → Configuration 2 → ℝ≥0∞ := fun x y => ENNReal.ofReal (freeKernel 2 v x y)
  have hP : Measurable (Function.uncurry P) :=
    ((measurable_freeKernel 2).comp (f := fun p : Configuration 2 × Configuration 2 => (v, p))
      (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hC : Measurable (Function.uncurry (twoParticleCorrection θ v)) :=
    (measurable_diagramKernel [pairTwo]).comp
      (f := fun p : Configuration 2 × Configuration 2 => ((θ, v), p))
      (measurable_const.prodMk measurable_id)
  let KP := spatialKernelComp volume K P
  let KC := spatialKernelComp volume K (twoParticleCorrection θ v)
  have hKP : Measurable (Function.uncurry KP) := measurable_spatialKernelComp volume hK hP
  have hKC : Measurable (Function.uncurry KC) := measurable_spatialKernelComp volume hK hC
  let B : Configuration 2 → Configuration 2 → ℝ≥0∞ := fun x z =>
    ∫⁻ q, momentKernel 2 θ b z q * F x q
  have hB : Measurable (Function.uncurry B) := measurable_slabParamAction (hQ b) hF
  let A₁ : Configuration 2 × Configuration 2 → ℝ≥0∞ := fun p =>
    momentKernel 2 θ r p.1 p.2 * (∫⁻ z, KP p.2 z * B p.1 z)
  let A₂ : Configuration 2 × Configuration 2 → ℝ≥0∞ := fun p =>
    momentKernel 2 θ r p.1 p.2 * (∫⁻ z, KC p.2 z * B p.1 z)
  have hA₁ : Measurable A₁ := (hQ r).mul (measurable_slabParamAction hKP hB)
  have hPoint (x y : Configuration 2) :
      (∫⁻ z, K y z * (∫⁻ q, momentKernel 2 θ (v + b) z q * F x q)) =
        (∫⁻ z, KP y z * B x z) + (∫⁻ z, KC y z * B x z) := by
    have hFx := hF.comp (f := fun q : Configuration 2 => (x, q)) (by fun_prop)
    have hBx := hB.comp (f := fun q : Configuration 2 => (x, q)) (by fun_prop)
    have h := connector_momentKernel_two_action_split_of hSG hv hb K hK hFx y
    have hp := spatialKernelComp_action_eq volume volume hK hP hBx y
    have hc := spatialKernelComp_action_eq volume volume hK hC hBx y
    exact h.trans (congrArg₂ (fun a b : ℝ≥0∞ => a + b) hp.symm hc.symm)
  calc
    _ = ∫⁻ x : Configuration 2, ∫⁻ y : Configuration 2, A₁ (x, y) + A₂ (x, y) := by
      unfold slabPositiveConnectorForm
      apply lintegral_congr
      intro x
      apply lintegral_congr
      intro y
      rw [hPoint, mul_add]
    _ = ∫⁻ x : Configuration 2, (∫⁻ y : Configuration 2, A₁ (x, y)) +
        ∫⁻ y : Configuration 2, A₂ (x, y) := by
      apply lintegral_congr
      intro x
      exact lintegral_add_left (hA₁.comp (measurable_const.prodMk measurable_id)) _
    _ = _ := lintegral_add_left hA₁.lintegral_prod_right _

end Critical2DKPZ.SHF.Flow
end
