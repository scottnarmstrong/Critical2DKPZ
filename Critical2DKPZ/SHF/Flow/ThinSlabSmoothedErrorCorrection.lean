/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabSmoothedMomentFormula
public import Critical2DKPZ.SHF.Flow.ThinSlabSmoothedPositiveForms
import Mathlib.Tactic

/-! # The smoothed slab error converges to the signed collision correction -/

@[expose] public noncomputable section
open MeasureTheory Filter Critical2DKPZ.DeltaBose Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported ENNReal Topology
namespace Critical2DKPZ.SHF.Flow

/-- The limiting smoothed slab error is exactly the difference of its positive
and negative one-collision source forms. -/
theorem tendsto_slabSmoothedSlabError_correctionForm (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    (hSG : MomentKernelTwoSemigroup (ϑ - Real.eulerMascheroniConstant))
    {s t u v e : ℝ} (hs : 0 ≤ s) (hst : s < t) (hv : 0 < v)
    (hvu : t + v < u) (he : 0 < e) (he1 : e ≤ 1)
    (Φ : C_c(Plane × Plane, ℝ)) (w : Plane → ℝ)
    (hw : Continuous w) (hwc : HasCompactSupport w)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∫ x, w x = 1) :
    Tendsto (fun N => ∫ ω,
      (smoothedProductPairing (polymerMeasure ϑ N s t ω)
        (fun x => e⁻¹ ^ 2 * w (e⁻¹ • x)) (polymerMeasure ϑ N t u ω) Φ -
        kernelProductPairing (polymerMeasure ϑ N s t ω)
          (slabSmoothedConnector ϑ N t (t + v) (fun x => e⁻¹ ^ 2 * w (e⁻¹ • x)))
          (polymerMeasure ϑ N (t + v) u ω) Φ) ^ 2 ∂disorderLaw) atTop
      (𝓝 (
        (slabPositiveConnectorForm (ϑ - Real.eulerMascheroniConstant) (t - s) (u - (t + v))
          (fun x y => ENNReal.ofReal (∏ i : Fin 2, Φ (x i, y i)))
          (spatialKernelComp volume (slabMollifierTensorKernel 2 e w)
            (twoParticleCorrection (ϑ - Real.eulerMascheroniConstant) v))).toReal -
        (slabPositiveConnectorForm (ϑ - Real.eulerMascheroniConstant) (t - s) (u - (t + v))
          (fun x y => ENNReal.ofReal (-(∏ i : Fin 2, Φ (x i, y i))))
          (spatialKernelComp volume (slabMollifierTensorKernel 2 e w)
            (twoParticleCorrection (ϑ - Real.eulerMascheroniConstant) v))).toReal)) := by
  let θ := ϑ - Real.eulerMascheroniConstant
  let r := t - s
  let b := u - (t + v)
  let we : Plane → ℝ := fun x => e⁻¹ ^ 2 * w (e⁻¹ • x)
  let κ : Plane × Plane → ℝ := fun p => we (p.1 - p.2)
  let Ψ : Configuration 2 → Configuration 2 → ℝ := fun x y => ∏ i : Fin 2, Φ (x i, y i)
  have hΨ : Measurable (Function.uncurry Ψ) := by
    apply Continuous.measurable
    unfold Ψ
    fun_prop
  have hwe : Continuous we := continuous_const.mul
    (hw.comp ((continuous_const : Continuous fun _ : Plane => e⁻¹).smul continuous_id))
  have hwec : HasCompactSupport we := by
    have hcomp : HasCompactSupport (fun x : Plane => w (e⁻¹ • x)) :=
      hwc.comp_smul (inv_ne_zero he.ne')
    exact HasCompactSupport.smul_left (f := fun _ : Plane => (e⁻¹ ^ 2 : ℝ)) hcomp
  have hκ : Measurable κ := (hwe.comp (continuous_fst.sub continuous_snd)).measurable
  have hκ0 (p : Plane × Plane) : 0 ≤ κ p := mul_nonneg (sq_nonneg _) (hw0 _)
  have hHeat : Measurable (slabSmoothedHeatConnector v e w) :=
    (continuous_slabSmoothedHeatConnector he w hw hwc).measurable
  have hHeat0 (p : Plane × Plane) : 0 ≤ slabSmoothedHeatConnector v e w p := by
    rcases p with ⟨a, b⟩
    rw [slabSmoothedHeatConnector_eq_integral]
    exact integral_nonneg fun y => mul_nonneg (mul_nonneg (sq_nonneg _) (hw0 _)) (heatKernel_nonneg hv.le _)
  have hr : 0 < r := sub_pos.mpr hst
  have hb : 0 < b := sub_pos.mpr hvu
  have hTime : v + b = u - t := by dsimp [b]; ring
  have htu : t < u := (lt_add_of_pos_right t hv).trans hvu
  have hX := tendsto_mollified_block_second_moment_with_integrability ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst htu Φ we hwe hwec
  have hS := tendsto_slabSmoothed_secondMoment_with_integrability ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst hv hvu he he1
    Φ w hw hwc hw0 hw1
  have hValue (k : Plane × Plane → ℝ) (z : Fin 2 → Configuration 2 × Configuration 2) :
      slabConnectorReplicaValue Φ k z = Ψ (z 0).1 (z 1).2 * ∏ i : Fin 2, k ((z 0).2 i, (z 1).1 i) := by
    simp only [slabConnectorReplicaValue, Ψ, Fin.prod_univ_two]
    ring
  have hIX : Integrable (fun z : Fin 2 → Configuration 2 × Configuration 2 =>
      Ψ (z 0).1 (z 1).2 * ∏ i : Fin 2, κ ((z 0).2 i, (z 1).1 i))
      (slabSeparatedMomentPiMeasure θ r (v + b)) := by
    rw [hTime]
    exact hX.1.congr (Eventually.of_forall fun z => hValue κ z)
  have hIS : Integrable (fun z : Fin 2 → Configuration 2 × Configuration 2 =>
      Ψ (z 0).1 (z 1).2 * ∏ i : Fin 2, slabSmoothedHeatConnector v e w ((z 0).2 i, (z 1).1 i))
      (slabSeparatedMomentPiMeasure θ r b) :=
    hS.1.congr (Eventually.of_forall fun z => hValue _ z)
  have hIXneg : Integrable (fun z : Fin 2 → Configuration 2 × Configuration 2 =>
      (-Ψ (z 0).1 (z 1).2) * ∏ i : Fin 2, κ ((z 0).2 i, (z 1).1 i))
      (slabSeparatedMomentPiMeasure θ r (v + b)) := by
    apply hIX.neg.congr
    filter_upwards [] with z
    change -(Ψ (z 0).1 (z 1).2 * ∏ i : Fin 2, κ ((z 0).2 i, (z 1).1 i)) =
      (-Ψ (z 0).1 (z 1).2) * ∏ i : Fin 2, κ ((z 0).2 i, (z 1).1 i)
    rw [neg_mul]
  have hFi := slabPositiveConnectorForm_ofReal_ne_top θ hr (add_pos hv hb) Ψ hΨ κ hκ hκ0 hIX
  have hGi := slabPositiveConnectorForm_ofReal_ne_top θ hr (add_pos hv hb)
    (fun x y => -Ψ x y) hΨ.neg κ hκ hκ0 hIXneg
  have hTensor : slabConnectorTensorKernel κ = slabMollifierTensorKernel 2 e w := rfl
  rw [hTensor] at hFi hGi
  have hSplit := slabSignedSmoothedForm_sub_eq_correction (r := r) hSG hv hb he w hw hwc hw0
    (fun x y => ENNReal.ofReal (Ψ x y)) (fun x y => ENNReal.ofReal (-Ψ x y))
    hΨ.ennreal_ofReal hΨ.neg.ennreal_ofReal hFi hGi
  have hEqX := integral_slabConnector_eq_positive_sub_negative θ hr (add_pos hv hb) Ψ hΨ κ hκ hκ0 hIX
  have hEqS := integral_slabConnector_eq_positive_sub_negative θ hr hb Ψ hΨ
    (slabSmoothedHeatConnector v e w) hHeat hHeat0 hIS
  simp only [← hValue, hTensor] at hEqX hEqS
  have hError := tendsto_slabSmoothedSlabError_secondMoment ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst hv hvu he he1
    Φ w hw hwc hw0 hw1
  rw [← hTime] at hError
  change Tendsto _ atTop (𝓝 (
    (∫ z, slabConnectorReplicaValue Φ κ z ∂slabSeparatedMomentPiMeasure θ r (v + b)) -
      ∫ z, slabConnectorReplicaValue Φ (slabSmoothedHeatConnector v e w) z ∂
        slabSeparatedMomentPiMeasure θ r b)) at hError
  rw [hEqX, hEqS, hSplit] at hError
  exact hError

end Critical2DKPZ.SHF.Flow
end
