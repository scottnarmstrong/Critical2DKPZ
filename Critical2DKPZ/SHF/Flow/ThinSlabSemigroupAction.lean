/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.MomentKernelTwoSemigroup
public import Critical2DKPZ.SHF.Flow.TwoParticleAction
import Mathlib.Tactic

/-! # Semigroup and correction identities for positive two-particle actions -/

@[expose] public noncomputable section
open MeasureTheory Critical2DKPZ.DeltaBose
open scoped ENNReal
namespace Critical2DKPZ.SHF.Flow

/-- The almost-everywhere kernel semigroup law acts on every nonnegative
measurable input. Tonelli requires no finiteness assumption. -/
theorem momentKernel_two_action_semigroup_of {θ v b : ℝ}
    (hSG : MomentKernelTwoSemigroup θ) (hv : 0 < v) (hb : 0 < b)
    {f : Configuration 2 → ℝ≥0∞} (hf : Measurable f) :
    (fun x => ∫⁻ y, momentKernel 2 θ (v + b) x y * f y) =ᵐ[volume]
      (fun x => ∫⁻ z, momentKernel 2 θ v x z * (∫⁻ y, momentKernel 2 θ b z y * f y)) := by
  have hK (t : ℝ) : Measurable (Function.uncurry (momentKernel 2 θ t)) :=
    Measurable.comp (g := fun p : (ℝ × ℝ) × Configuration 2 × Configuration 2 =>
      momentKernel 2 p.1.1 p.1.2 p.2.1 p.2.2)
      (f := fun p : Configuration 2 × Configuration 2 => ((θ, t), p))
      (measurable_momentKernel 2) (measurable_const.prodMk measurable_id)
  have hAE : ∀ᵐ x : Configuration 2, ∀ᵐ y : Configuration 2,
      (∫⁻ z, momentKernel 2 θ v x z * momentKernel 2 θ b z y) =
        momentKernel 2 θ (v + b) x y := Measure.ae_ae_of_ae_prod (hSG hv hb)
  filter_upwards [hAE] with x hx
  calc
    _ = ∫⁻ y, spatialKernelComp volume (momentKernel 2 θ v) (momentKernel 2 θ b) x y * f y := by
      apply lintegral_congr_ae
      filter_upwards [hx] with y hy
      rw [spatialKernelComp, hy]
    _ = _ := spatialKernelComp_action_eq volume volume (hK v) (hK b) hf x

/-- Splitting the first semigroup factor isolates the one-collision correction
that controls the thin-slab error. -/
theorem momentKernel_two_action_free_add_correction_of {θ v b : ℝ}
    (hSG : MomentKernelTwoSemigroup θ) (hv : 0 < v) (hb : 0 < b)
    {f : Configuration 2 → ℝ≥0∞} (hf : Measurable f) :
    (fun x => ∫⁻ y, momentKernel 2 θ (v + b) x y * f y) =ᵐ[volume]
      (fun x =>
        (∫⁻ z, ENNReal.ofReal (freeKernel 2 v x z) * (∫⁻ y, momentKernel 2 θ b z y * f y)) +
        ∫⁻ z, twoParticleCorrection θ v x z * (∫⁻ y, momentKernel 2 θ b z y * f y)) := by
  have hK : Measurable (Function.uncurry (momentKernel 2 θ b)) :=
    Measurable.comp (g := fun p : (ℝ × ℝ) × Configuration 2 × Configuration 2 =>
      momentKernel 2 p.1.1 p.1.2 p.2.1 p.2.2)
      (f := fun p : Configuration 2 × Configuration 2 => ((θ, b), p))
      (measurable_momentKernel 2) (measurable_const.prodMk measurable_id)
  have hAction : Measurable (fun z => ∫⁻ y, momentKernel 2 θ b z y * f y) :=
    measurable_kernelAction volume hK hf
  filter_upwards [momentKernel_two_action_semigroup_of hSG hv hb hf] with x hx
  rw [hx]
  have hSplit (z : Configuration 2) : momentKernel 2 θ v x z =
      ENNReal.ofReal (freeKernel 2 v x z) + twoParticleCorrection θ v x z := by
    simpa only [twoParticleCorrection] using momentKernel_two_eq_free_add_diagram θ v x z
  simp_rw [hSplit, add_mul]
  apply lintegral_add_left
  exact (((measurable_freeKernel 2).comp
    (measurable_const.prodMk (measurable_const.prodMk measurable_id))).ennreal_ofReal).mul hAction

end Critical2DKPZ.SHF.Flow
end
