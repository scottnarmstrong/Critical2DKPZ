/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConfigurationMollifierLimits
public import Critical2DKPZ.SHF.Tsai.KernelCompositionOperators

/-! # Strong limits of the bounded connector kernel operators

The operators retain the actual integral action. Their definition is
independent of which finite form bound establishes continuity.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Equal kernels give the same operator, independently of their finite form constants. -/
theorem configurationKernelOperator_eq_of_eq {n : ℕ}
    {K L : Configuration n → Configuration n → ℝ≥0∞} (hKL : K = L)
    (hK : Measurable (Function.uncurry K)) (hL : Measurable (Function.uncurry L))
    {c d : ℝ≥0∞} (hc : c ≠ ⊤) (hd : d ≠ ⊤)
    (hKF : FormBound volume volume K c) (hLF : FormBound volume volume L d) :
    configurationKernelOperator hK hc hKF = configurationKernelOperator hL hd hLF := by
  subst L
  apply ContinuousLinearMap.ext
  intro F
  apply Lp.ext
  exact (coe_configurationKernelOperator hK hc hKF F).trans
    (coe_configurationKernelOperator hL hd hLF F).symm

/-- The actual bounded connector operators converge strongly, for any chosen finite form bounds. -/
theorem tendsto_connectorKernelOperator {n : ℕ} {w : Fin n → ℕ → Plane → ℝ}
    (hw : ∀ i, IsL2ApplicableMollifier (w i)) (c : ℕ → ℝ≥0∞) (hc : ∀ j, c j ≠ ⊤)
    (hC : ∀ j, FormBound volume volume (connectorKernel (fun i => w i j)) (c j))
    (F : Lp ℝ 2 (volume : Measure (Configuration n))) :
    Tendsto (fun j => configurationKernelOperator
      (measurable_connectorKernel _ (fun i => ((hw i).2.1 j).measurable)) (hc j) (hC j) F)
      atTop (𝓝 F) := by
  have hlim := tendsto_configurationMollifierAction n hw
    (Lp.stronglyMeasurable F).measurable (Lp.memLp F)
  have heq (j) : eLpNorm (⇑(configurationKernelOperator
      (measurable_connectorKernel _ (fun i => ((hw i).2.1 j).measurable)) (hc j) (hC j) F) - ⇑F) 2 =
      eLpNorm (configurationMollifierAction (fun i => w i j) F - ⇑F) 2 := by
    apply eLpNorm_congr_ae
    have hrep := coe_configurationKernelOperator
      (measurable_connectorKernel _ (fun i => ((hw i).2.1 j).measurable)) (hc j) (hC j) F
    rw [configurationKernelAction_connectorKernel (fun i => (hw i).1 j) F] at hrep
    exact hrep.sub Filter.EventuallyEq.rfl
  simp_rw [← heq] at hlim
  have h := Lp.tendsto_Lp_of_tendsto_eLpNorm (F : Configuration n → ℝ) (Lp.memLp F) hlim
  simpa only [Lp.toLp_coeFn] using h

end Critical2DKPZ.SHF.Tsai

end
