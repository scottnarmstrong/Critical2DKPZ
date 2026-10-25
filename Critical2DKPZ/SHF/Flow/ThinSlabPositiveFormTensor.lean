/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabPositiveConnectorForm
import Mathlib.Tactic

/-! # Separated endpoint sources in positive connector forms -/

@[expose] public noncomputable section
open MeasureTheory Critical2DKPZ.DeltaBose
open scoped ENNReal
namespace Critical2DKPZ.SHF.Flow

/-- A separated positive endpoint source turns the connector form into a
bilinear kernel action, without any finiteness assumption. -/
theorem slabPositiveConnectorForm_tensor_source (θ a b : ℝ)
    (K : Configuration 2 → Configuration 2 → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (f g : Configuration 2 → ℝ≥0∞)
    (hf : Measurable f) :
    slabPositiveConnectorForm θ a b (fun x z => g x * f z) K =
      ∫⁻ x, (∫⁻ y, momentKernel 2 θ a x y *
        (∫⁻ z, K y z * (∫⁻ q, momentKernel 2 θ b z q * f q))) * g x := by
  have hQ (t : ℝ) : Measurable (Function.uncurry (momentKernel 2 θ t)) :=
    Measurable.comp (g := fun p : (ℝ × ℝ) × Configuration 2 × Configuration 2 =>
      momentKernel 2 p.1.1 p.1.2 p.2.1 p.2.2)
      (f := fun p : Configuration 2 × Configuration 2 => ((θ, t), p))
      (measurable_momentKernel 2) (measurable_const.prodMk measurable_id)
  have hB := measurable_kernelAction volume (hQ b) hf
  have hKB := measurable_kernelAction volume hK hB
  unfold slabPositiveConnectorForm
  apply lintegral_congr
  intro x
  have hInner (z : Configuration 2) :
      (∫⁻ q, momentKernel 2 θ b z q * (g x * f q)) =
        (∫⁻ q, momentKernel 2 θ b z q * f q) * g x := by
    have hrow : Measurable (fun q : Configuration 2 => momentKernel 2 θ b z q * f q) :=
      ((hQ b).comp (f := fun q : Configuration 2 => (z, q)) (by fun_prop)).mul hf
    rw [← lintegral_mul_const (μ := volume) (g x) hrow]
    apply lintegral_congr
    intro q
    ac_rfl
  simp_rw [hInner]
  have hrow : Measurable (fun y : Configuration 2 => momentKernel 2 θ a x y *
      (∫⁻ z, K y z * (∫⁻ q, momentKernel 2 θ b z q * f q))) :=
    ((hQ a).comp (f := fun y : Configuration 2 => (x, y)) (by fun_prop)).mul hKB
  rw [← lintegral_mul_const (μ := volume) (g x) hrow]
  apply lintegral_congr
  intro y
  have hKrow : Measurable (fun z : Configuration 2 => K y z *
      (∫⁻ q, momentKernel 2 θ b z q * f q)) :=
    (hK.comp (f := fun z : Configuration 2 => (y, z)) (by fun_prop)).mul hB
  rw [mul_assoc, ← lintegral_mul_const (μ := volume) (g x) hKrow]
  congr 1
  apply lintegral_congr
  intro z
  ac_rfl

end Critical2DKPZ.SHF.Flow
end
