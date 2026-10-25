/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainFormBounds
public import Critical2DKPZ.SHF.Tsai.MollifierFormBounds
public import Critical2DKPZ.SHF.Tsai.ConfigurationKernelOperator
public import Critical2DKPZ.SHF.Tsai.TensorMoments

/-! # Actual convolution by configuration connectors

The positive connector is finite pointwise. Its real action is the product
convolution, with absolutely integrable rows on every `L²` input. The planar
uniform bounds give one common configuration-space bound for the whole family.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Actual convolution by the product of planar mollifiers. -/
def configurationMollifierAction {n : ℕ} (w : Fin n → Plane → ℝ)
    (F : Configuration n → ℝ) (x : Configuration n) : ℝ :=
  ∫ y, (∏ i, w i (x i - y i)) * F y

/-- The product convolution is measurable whenever its data are measurable. -/
theorem measurable_configurationMollifierAction {n : ℕ} {w : Fin n → Plane → ℝ}
    (hw : ∀ i, Measurable (w i)) {F : Configuration n → ℝ} (hF : Measurable F) :
    Measurable (configurationMollifierAction w F) := by
  have hm : Measurable (fun q : Configuration n × Configuration n =>
      (∏ i, w i (q.1 i - q.2 i)) * F q.2) := by
    apply Measurable.mul _ (hF.comp measurable_snd)
    apply Finset.measurable_prod
    intro i _
    exact (hw i).comp (((measurable_pi_apply i).comp measurable_fst).sub
      ((measurable_pi_apply i).comp measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- Joint measurability of configuration convolution with a passive parameter. -/
theorem measurable_fiber_configurationMollifierAction {n : ℕ} {Y : Type*} [MeasurableSpace Y]
    {w : Fin n → Plane → ℝ} (hw : ∀ i, Measurable (w i))
    {F : Configuration n × Y → ℝ} (hF : Measurable F) :
    Measurable (fun q : Configuration n × Y =>
      configurationMollifierAction w (fun x => F (x, q.2)) q.1) := by
  have hm : Measurable (fun q : (Configuration n × Y) × Configuration n =>
      (∏ i, w i (q.1.1 i - q.2 i)) * F (q.2, q.1.2)) := by
    apply Measurable.mul _ (hF.comp (measurable_snd.prodMk measurable_fst.snd))
    apply Finset.measurable_prod
    intro i _
    exact (hw i).comp (((measurable_pi_apply i).comp measurable_fst.fst).sub
      ((measurable_pi_apply i).comp measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- Each row is absolutely integrable, by the tensor `L²` bound and Hölder. -/
theorem integrable_configurationMollifierAction_integrand {n : ℕ} {w : Fin n → Plane → ℝ}
    (hw : ∀ i, MemLp (w i) 2) {F : Configuration n → ℝ} (hF : MemLp F 2)
    (x : Configuration n) : Integrable (fun y => (∏ i, w i (x i - y i)) * F y) := by
  exact (memLp_configuration_tensor (fun i y => w i (x i - y))
    (fun i => (hw i).comp_measurePreserving (volume.measurePreserving_sub_left (x i)))).integrable_mul hF

/-- The positive connector's real value is the literal product of its nonnegative factors. -/
theorem connectorKernel_toReal {n : ℕ} {w : Fin n → Plane → ℝ}
    (hw : ∀ i x, 0 ≤ w i x) (x y : Configuration n) :
    (connectorKernel w x y).toReal = ∏ i, w i (x i - y i) := by
  simp only [connectorKernel, ENNReal.toReal_prod, ENNReal.toReal_ofReal (hw _ _)]

/-- The real connector action is the actual product convolution. -/
theorem configurationKernelAction_connectorKernel {n : ℕ} {w : Fin n → Plane → ℝ}
    (hw : ∀ i x, 0 ≤ w i x) (F : Configuration n → ℝ) :
    configurationKernelAction (connectorKernel w) F = configurationMollifierAction w F := by
  funext x
  simp only [configurationKernelAction, configurationMollifierAction, connectorKernel_toReal hw]

/-- One finite form constant controls every member of the product family. -/
theorem exists_formBound_connector_uniform {n : ℕ} {w : Fin n → ℕ → Plane → ℝ}
    (hw : ∀ i, IsL2ApplicableMollifier (w i)) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ j,
      FormBound volume volume (connectorKernel (fun i => w i j)) M := by
  choose M hMfin hM using fun i => exists_formBound_mollifier_uniform (hw i)
  refine ⟨∏ i, M i, ENNReal.prod_ne_top (fun i _ => hMfin i), fun j => ?_⟩
  exact formBound_connectorKernel (fun i => w i j) (fun i => ((hw i).2.1 j).measurable)
    M (fun i => hM i j)

/-- The actual product convolutions have one common finite `L²` bound. -/
theorem exists_configurationMollifierAction_uniform_bound {n : ℕ}
    {w : Fin n → ℕ → Plane → ℝ} (hw : ∀ i, IsL2ApplicableMollifier (w i)) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ j (F : Configuration n → ℝ), MemLp F 2 →
      eLpNorm (configurationMollifierAction (fun i => w i j) F) 2 ≤ M * eLpNorm F 2 := by
  obtain ⟨M, hMfin, hM⟩ := exists_formBound_connector_uniform hw
  refine ⟨M, hMfin, fun j F hF => ?_⟩
  rw [← configurationKernelAction_connectorKernel (fun i => (hw i).1 j) F]
  exact eLpNorm_configurationKernelAction_le
    (measurable_connectorKernel _ (fun i => ((hw i).2.1 j).measurable)) (hM j) hF

end Critical2DKPZ.SHF.Tsai

end
