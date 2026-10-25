/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConfigurationKernelAction
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! # Bounded operators represented by positive configuration kernels

A positive kernel with a finite bilinear bound defines a bounded operator on `L²`
whose inner product is the corresponding double integral.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The integral action of a configuration kernel as a linear map on `L²` equivalence classes. -/
def configurationKernelLinearMap {n : ℕ}
    {K : Configuration n → Configuration n → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hKF : FormBound volume volume K c) :
    Lp ℝ 2 (volume : Measure (Configuration n)) →ₗ[ℝ]
      Lp ℝ 2 (volume : Measure (Configuration n)) where
  toFun F := (memLp_configurationKernelAction hK hc hKF (Lp.memLp F)).toLp (configurationKernelAction K F)
  map_add' F G := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    have hinput := configurationKernelAction_congr_ae K (Lp.coeFn_add F G)
    have heq : configurationKernelAction K (⇑(F + G)) =ᵐ[volume]
        configurationKernelAction K (⇑F + ⇑G) :=
      Filter.Eventually.of_forall fun x => congrFun hinput x
    exact heq.trans (configurationKernelAction_add_ae hK hc hKF (Lp.memLp F) (Lp.memLp G))
  map_smul' a F := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    apply Filter.Eventually.of_forall
    intro x
    change configurationKernelAction K (⇑(a • F)) x = a * configurationKernelAction K F x
    rw [configurationKernelAction_congr_ae K (Lp.coeFn_smul a F), configurationKernelAction_smul]
    rfl

/-- The positive form constant bounds the actual linear map on `L²`. -/
theorem configurationKernelLinearMap_bound {n : ℕ}
    {K : Configuration n → Configuration n → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hKF : FormBound volume volume K c)
    (F : Lp ℝ 2 (volume : Measure (Configuration n))) :
    ‖configurationKernelLinearMap hK hc hKF F‖ ≤ c.toReal * ‖F‖ := by
  change ‖(memLp_configurationKernelAction hK hc hKF (Lp.memLp F)).toLp
    (configurationKernelAction K F)‖ ≤ _
  rw [Lp.norm_toLp, Lp.norm_def]
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hc (Lp.eLpNorm_ne_top F))
    (eLpNorm_configurationKernelAction_le hK hKF (Lp.memLp F))
  simpa only [ENNReal.toReal_mul] using h

/-- The bounded right-to-left integral operator of a positive configuration kernel. -/
def configurationKernelOperator {n : ℕ}
    {K : Configuration n → Configuration n → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hKF : FormBound volume volume K c) :
    Lp ℝ 2 (volume : Measure (Configuration n)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Configuration n)) :=
  (configurationKernelLinearMap hK hc hKF).mkContinuous c.toReal
    (configurationKernelLinearMap_bound hK hc hKF)

/-- The bounded kernel operator agrees almost everywhere with its integral action; row integrability follows from `ae_integrable_configurationKernelAction`. -/
theorem coe_configurationKernelOperator {n : ℕ}
    {K : Configuration n → Configuration n → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hKF : FormBound volume volume K c)
    (F : Lp ℝ 2 (volume : Measure (Configuration n))) :
    ⇑(configurationKernelOperator hK hc hKF F) =ᵐ[volume] configurationKernelAction K F :=
  (memLp_configurationKernelAction hK hc hKF (Lp.memLp F)).coeFn_toLp


/-- The operator pairing is the literal real kernel form, whose integrability is supplied by
`configurationKernel_real_form_bound`. -/
theorem inner_configurationKernelOperator {n : ℕ}
    {K : Configuration n → Configuration n → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hKF : FormBound volume volume K c)
    (F G : Lp ℝ 2 (volume : Measure (Configuration n))) :
    ⟪configurationKernelOperator hK hc hKF G, F⟫_ℝ =
      ∫ xy : Configuration n × Configuration n,
        F xy.1 * (K xy.1 xy.2).toReal * G xy.2 ∂(volume.prod volume) := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, F x * configurationKernelAction K G x := by
      apply integral_congr_ae
      filter_upwards [coe_configurationKernelOperator hK hc hKF G] with x hx
      simp only [hx, RCLike.inner_apply, conj_trivial]
    _ = ∫ x, ∫ y, F x * (K x y).toReal * G y := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      change F x * (∫ y, (K x y).toReal * G y) = _
      rw [← integral_const_mul]
      congr 1
      funext y
      ring
    _ = _ := (integral_prod _
      (configurationKernel_real_form_bound hK hc hKF F G (Lp.memLp F) (Lp.memLp G)).1).symm

/-- The bounded kernel operator applied to an `L²` representative equals its kernel integral almost everywhere. -/
theorem coe_configurationKernelOperator_toLp {n : ℕ}
    {K : Configuration n → Configuration n → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hKF : FormBound volume volume K c)
    {F : Configuration n → ℝ} (hF : MemLp F 2) :
    ⇑(configurationKernelOperator hK hc hKF (hF.toLp F)) =ᵐ[volume] configurationKernelAction K F := by
  have h := coe_configurationKernelOperator hK hc hKF (hF.toLp F)
  rw [configurationKernelAction_congr_ae K hF.coeFn_toLp] at h
  exact h

/-- The inner product of the kernel operator on square-integrable functions equals the iterated kernel integral, whose absolute integrability follows from `configurationKernel_real_form_bound`. -/
theorem inner_configurationKernelOperator_toLp {n : ℕ}
    {K : Configuration n → Configuration n → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hKF : FormBound volume volume K c)
    {F G : Configuration n → ℝ} (hF : MemLp F 2) (hG : MemLp G 2) :
    ⟪configurationKernelOperator hK hc hKF (hG.toLp G), hF.toLp F⟫_ℝ =
      ∫ x : Configuration n, ∫ y : Configuration n, F x * (K x y).toReal * G y := by
  rw [inner_configurationKernelOperator]
  rw [← integral_prod _ (configurationKernel_real_form_bound hK hc hKF F G hF hG).1]
  apply integral_congr_ae
  have hx := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure (Configuration n)))
    (ν := (volume : Measure (Configuration n)))).ae_eq_comp hF.coeFn_toLp
  have hy := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure (Configuration n)))
    (ν := (volume : Measure (Configuration n)))).ae_eq_comp hG.coeFn_toLp
  filter_upwards [hx, hy] with xy hxy hxy'
  rw [show hF.toLp F xy.1 = F xy.1 from hxy,
    show hG.toLp G xy.2 = G xy.2 from hxy']

end Critical2DKPZ.SHF.Tsai

end
