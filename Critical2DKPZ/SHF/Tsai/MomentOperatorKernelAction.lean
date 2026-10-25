/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.MomentOperators
public import Critical2DKPZ.SHF.Tsai.KernelOperatorSymmetry
import Critical2DKPZ.SHF.DeltaBose.EndpointSymmetry

/-! # Kernel representations of moment operators

Symmetry of the moment kernel identifies its `L²` operator with integration against the
kernel. For at most four particles, this gives an almost-everywhere integral representative
on every `L²` input at positive times.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The moment operator equals the configuration-kernel operator for any finite form bound on the same moment kernel. -/
theorem momentOperator_eq_configurationKernelOperator {n : ℕ} (hn : n ≤ 4) (θ : ℝ)
    {τ : ℝ} (hτ : 0 < τ) (hK : Measurable (Function.uncurry (momentKernel n θ τ)))
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hQ : FormBound volume volume (momentKernel n θ τ) c) :
    momentOperator hn θ hτ = configurationKernelOperator hK hc hQ := by
  apply ContinuousLinearMap.ext
  intro F
  apply ext_inner_right ℝ
  intro G
  calc
    ⟪momentOperator hn θ hτ F, G⟫_ℝ =
        ∫ q : Configuration n × Configuration n,
          F q.1 * (momentKernel n θ τ q.1 q.2).toReal * G q.2 ∂volume.prod volume :=
      inner_momentOperator hn θ hτ F G
    _ = ⟪configurationKernelOperator hK hc hQ G, F⟫_ℝ :=
      (inner_configurationKernelOperator hK hc hQ F G).symm
    _ = ⟪F, configurationKernelOperator hK hc hQ G⟫_ℝ := real_inner_comm _ _
    _ = ⟪configurationKernelOperator hK hc hQ F, G⟫_ℝ :=
      (inner_configurationKernelOperator_symm hK hc hQ (momentKernel_symm n θ τ) F G).symm

/-- The moment operator agrees almost everywhere with integration against its kernel on every `L²` representative; row integrability is supplied by `ae_integrable_configurationKernelAction`. -/
theorem coe_momentOperator_toLp {n : ℕ} (hn : n ≤ 4) (θ : ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hK : Measurable (Function.uncurry (momentKernel n θ τ)))
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hQ : FormBound volume volume (momentKernel n θ τ) c)
    {F : Configuration n → ℝ} (hF : MemLp F 2) :
    ⇑(momentOperator hn θ hτ (hF.toLp F)) =ᵐ[volume]
      fun x => ∫ y, (momentKernel n θ τ x y).toReal * F y := by
  rw [momentOperator_eq_configurationKernelOperator hn θ hτ hK hc hQ]
  exact coe_configurationKernelOperator_toLp hK hc hQ hF

end Critical2DKPZ.SHF.Tsai

end
