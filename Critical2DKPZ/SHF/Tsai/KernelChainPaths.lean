/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConfigurationPathRecursion
public import Critical2DKPZ.SHF.Tsai.KernelMeasureTests

/-! # Evaluation of positive kernel path integrals

Integrating the last block gives a connector action on the last block action.
The exact positive kernel-composition identity then identifies the finite
path integral with the chain kernel.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Integrating a block kernel measure after a connector gives their iterated positive action. -/
theorem lintegral_kernelMeasure_connector {n : ℕ}
    {L C : Configuration n → Configuration n → ℝ≥0∞}
    (hL : Measurable (Function.uncurry L)) (hC : Measurable (Function.uncurry C))
    {F : Configuration n → ℝ≥0∞} (hF : Measurable F) (y : Configuration n) :
    (∫⁻ z, C y z.1 * F z.2 ∂volume.withDensity (Function.uncurry L)) =
      ∫⁻ u, C y u * ∫⁻ v, L u v * F v := by
  have hCy : Measurable (C y) := hC.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_kernelMeasure_mul hL hCy hF]
  apply lintegral_congr
  intro u
  have hLu : Measurable (fun v => L u v * F v) :=
    (hL.comp (measurable_const.prodMk measurable_id)).mul hF
  simp only [mul_assoc]
  exact lintegral_const_mul _ hLu

/-- The positive path integral of kernel measures is the literal chain-kernel form. -/
theorem lintegral_configurationChainPathTest_eq {n : ℕ} (K : ℕ)
    (Kb : ℕ → Configuration n → Configuration n → ℝ≥0∞)
    (hKb : ∀ k, Measurable (Function.uncurry (Kb k)))
    [∀ k, SigmaFinite (volume.withDensity (Function.uncurry (Kb k)))]
    (w : Fin n → ℕ → Plane → ℝ) (hw : ∀ i k, Measurable (w i k))
    (G F : Configuration n → ℝ≥0∞) (hG : Measurable G) (hF : Measurable F) :
    (∫⁻ p, configurationChainPathTest K w G F p
      ∂Measure.pi (fun k : Fin (K + 1) => volume.withDensity (Function.uncurry (Kb k)))) =
      ∫⁻ x, ∫⁻ y, G x * chainKernel n Kb w K x y * F y := by
  induction K generalizing F with
  | zero =>
    have he := measurePreserving_piUnique
      (fun k : Fin 1 => volume.withDensity (Function.uncurry (Kb k)))
    have hm : Measurable (fun q : Configuration n × Configuration n => G q.1 * F q.2) :=
      (hG.comp measurable_fst).mul (hF.comp measurable_snd)
    have ht := he.lintegral_comp hm
    have hdef : (default : Fin 1) = 0 := Subsingleton.elim _ _
    have hlast : Fin.last 0 = 0 := rfl
    have hpath : (∫⁻ p, configurationChainPathTest 0 w G F p
        ∂Measure.pi (fun k : Fin 1 => volume.withDensity (Function.uncurry (Kb k)))) =
        ∫⁻ q, G q.1 * F q.2 ∂volume.withDensity (Function.uncurry (Kb 0)) := by
      simpa only [configurationChainPathTest, Finset.univ_eq_empty, Finset.prod_empty, one_mul,
        MeasurableEquiv.piUnique, Equiv.piUnique, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk,
        hdef, hlast, Fin.val_zero] using ht
    exact hpath.trans (lintegral_kernelMeasure_mul (hKb 0) hG hF)
  | succ K ih =>
    let C := connectorKernel (fun i => w i K)
    have hCm : Measurable (Function.uncurry C) := measurable_connectorKernel _ (fun i => hw i K)
    let T (y : Configuration n) := ∫⁻ z, C y z.1 * F z.2
      ∂volume.withDensity (Function.uncurry (Kb (K + 1)))
    have hTjoint : Measurable (fun q : Configuration n × (Configuration n × Configuration n) =>
        C q.1 q.2.1 * F q.2.2) :=
      (hCm.comp (measurable_fst.prodMk measurable_snd.fst)).mul (hF.comp measurable_snd.snd)
    have hTm : Measurable T := hTjoint.lintegral_prod_right'
    have hTeq (y) : T y = ∫⁻ u, C y u * ∫⁻ v, Kb (K + 1) u v * F v :=
      lintegral_kernelMeasure_connector (hKb (K + 1)) hCm hF y
    rw [lintegral_configurationChainPathTest_succ K
      (fun k => volume.withDensity (Function.uncurry (Kb k))) w hw G F hG hF]
    change (∫⁻ p, configurationChainPathTest K w G T p
      ∂Measure.pi (fun k : Fin (K + 1) => volume.withDensity (Function.uncurry (Kb k)))) = _
    rw [ih T hTm]
    have hprev := measurable_chainKernel Kb hKb w hw K
    have hlast := measurable_spatialKernelComp volume hCm (hKb (K + 1))
    have haction (x : Configuration n) :
        (∫⁻ y, chainKernel n Kb w (K + 1) x y * F y) =
          ∫⁻ y, chainKernel n Kb w K x y * T y := by
      rw [chainKernel_succ_eq_comp Kb hKb w hw K,
        spatialKernelComp_action_eq volume volume hprev hlast hF x]
      apply lintegral_congr
      intro y
      rw [spatialKernelComp_action_eq volume volume hCm (hKb (K + 1)) hF y, ← hTeq y]
    apply lintegral_congr
    intro x
    have hp : Measurable (fun y => chainKernel n Kb w K x y * T y) :=
      (hprev.comp (measurable_const.prodMk measurable_id)).mul hTm
    have hn : Measurable (fun y => chainKernel n Kb w (K + 1) x y * F y) :=
      ((measurable_chainKernel Kb hKb w hw (K + 1)).comp
        (measurable_const.prodMk measurable_id)).mul hF
    simp only [mul_assoc]
    rw [lintegral_const_mul _ hp, lintegral_const_mul _ hn, haction]

end Critical2DKPZ.SHF.Tsai

end
