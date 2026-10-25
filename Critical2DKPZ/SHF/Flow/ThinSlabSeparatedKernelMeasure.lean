/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabSeparatedCoordinates
public import Critical2DKPZ.SHF.Flow.ThinSlabSeparatedTensorMoment
public import Critical2DKPZ.SHF.Flow.PiTensorApproximation
public import Critical2DKPZ.SHF.Tsai.MomentKernelMeasureFiniteness
public import Critical2DKPZ.SHF.Flow.SubseqDenseMoments

/-! Two separated replica blocks define a continuum endpoint measure. -/

@[expose] public noncomputable section

open MeasureTheory
open Filter
open Critical2DKPZ.DeltaBose
open Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Flow

/-- The endpoint measure whose density is the two-replica moment kernel. -/
def slabMomentKernelEndpointMeasure (θ τ : ℝ) :
    Measure (Configuration 2 × Configuration 2) :=
  (volume.prod volume).withDensity (Function.uncurry (momentKernel 2 θ τ))

/-- The product endpoint law for two independent polymer blocks with different durations. -/
def slabSeparatedMomentPiMeasure (θ τ₁ τ₂ : ℝ) :
    Measure (Fin 2 → Configuration 2 × Configuration 2) :=
  Measure.pi fun i => if i.val = 0 then slabMomentKernelEndpointMeasure θ τ₁
    else slabMomentKernelEndpointMeasure θ τ₂

/-- The limiting integral of a four-replica test against the two separated moment kernels.
For positive durations both factors are locally finite by `locallyFinite_momentKernelMeasure`,
so the compact grouped test is integrable. -/
def slabSeparatedMomentIntegral (θ τ₁ τ₂ : ℝ)
    (F : C_c((Fin 4 → Plane × Plane), ℝ)) : ℝ :=
  ∫ z, slabSeparatedGroupedTest F z ∂slabSeparatedMomentPiMeasure θ τ₁ τ₂

private def slabPairArrayHomeomorph :
    (Fin 2 → Plane × Plane) ≃ₜ (Configuration 2 × Configuration 2) where
  toEquiv := Equiv.arrowProdEquivProdArrow (Fin 2) (fun _ => Plane) (fun _ => Plane)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def slabMomentBlockTensorTest (φ : Fin 2 → C_c(Plane × Plane, ℝ)) :
    C_c((Configuration 2 × Configuration 2), ℝ) := by
  let f (z : Configuration 2 × Configuration 2) : ℝ :=
    ∏ i : Fin 2, φ i (z.1 i, z.2 i)
  have hf : Continuous f := by fun_prop
  refine ⟨⟨f, hf⟩, ?_⟩
  apply HasCompactSupport.of_support_subset_isCompact
    ((slabCompactPiTensorTest φ).hasCompactSupport.image slabPairArrayHomeomorph.continuous)
  intro z hz
  have hval : f z = slabCompactPiTensorTest φ (slabPairArrayHomeomorph.symm z) := by
    simp [f, slabPairArrayHomeomorph, Equiv.arrowProdEquivProdArrow,
      slabCompactPiTensorTest_apply]
  have hne : slabCompactPiTensorTest φ (slabPairArrayHomeomorph.symm z) ≠ 0 := by
    change f z ≠ 0 at hz
    rw [← hval]
    exact hz
  refine ⟨slabPairArrayHomeomorph.symm z, subset_tsupport _ hne, ?_⟩
  simp [slabPairArrayHomeomorph, Equiv.arrowProdEquivProdArrow]


private theorem slabMomentKernelEndpointMeasure_integral (θ : ℝ) {τ : ℝ} (hτ : 0 < τ)
    (F : C_c((Configuration 2 × Configuration 2), ℝ)) :
    (∫ z, F z ∂slabMomentKernelEndpointMeasure θ τ) =
      ∫ x : Configuration 2, ∫ y : Configuration 2,
        F (x, y) * (momentKernel 2 θ τ x y).toReal := by
  let ν := slabMomentKernelEndpointMeasure θ τ
  have hνloc : IsLocallyFiniteMeasure ν := locallyFinite_momentKernelMeasure 2 θ hτ
  have hν : Integrable (F : Configuration 2 × Configuration 2 → ℝ) ν :=
    integrable_compactTest_of_locallyFinite ν hνloc F
  have hK : Measurable (Function.uncurry (momentKernel 2 θ τ)) := by
    exact Measurable.comp (g := fun p : (ℝ × ℝ) × Configuration 2 × Configuration 2 =>
      momentKernel 2 p.1.1 p.1.2 p.2.1 p.2.2)
      (f := fun z : Configuration 2 × Configuration 2 => ((θ, τ), z))
      (measurable_momentKernel 2) (measurable_const.prodMk measurable_id)
  have hKtop : ∀ᵐ z ∂(volume.prod volume), momentKernel 2 θ τ z.1 z.2 < ⊤ := by
    filter_upwards [momentKernel_ne_top 2 (by norm_num) θ hτ] with z hz
    exact lt_top_iff_ne_top.mpr hz
  have hprod : Integrable (fun z : Configuration 2 × Configuration 2 =>
      F z * (momentKernel 2 θ τ z.1 z.2).toReal) (volume.prod volume) :=
    (integrable_withDensity_iff hK hKtop).mp hν
  calc
    _ = ∫ z, (momentKernel 2 θ τ z.1 z.2).toReal * F z ∂(volume.prod volume) :=
      integral_withDensity_eq_integral_toReal_smul hK hKtop F
    _ = ∫ z, F z * (momentKernel 2 θ τ z.1 z.2).toReal ∂(volume.prod volume) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => mul_comm _ _
    _ = ∫ x : Configuration 2, ∫ y : Configuration 2,
        F (x, y) * (momentKernel 2 θ τ x y).toReal := integral_prod _ hprod

private theorem integral_slabMomentBlockTensorTest (θ : ℝ) {τ : ℝ} (hτ : 0 < τ)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) :
    (∫ z, slabMomentBlockTensorTest φ z ∂slabMomentKernelEndpointMeasure θ τ) =
      ∫ x : Configuration 2, ∫ y : Configuration 2,
        (∏ i : Fin 2, φ i (x i, y i)) * (momentKernel 2 θ τ x y).toReal := by
  rw [slabMomentKernelEndpointMeasure_integral θ hτ (slabMomentBlockTensorTest φ)]
  rfl

/-- Integrating a four-coordinate tensor against the separated continuum law factors into the
two moment-kernel tensor integrals. -/
theorem integral_slabSeparatedMomentPiMeasure_tensor (θ : ℝ) {τ₁ τ₂ : ℝ}
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) (φ : Fin 4 → C_c(Plane × Plane, ℝ)) :
    slabSeparatedMomentIntegral θ τ₁ τ₂ (slabCompactPiTensorTest φ) =
      (∫ x : Configuration 2, ∫ y : Configuration 2,
        (∏ i : Fin 2, φ (i.castAdd 2) (x i, y i)) *
          (momentKernel 2 θ τ₁ x y).toReal) *
      (∫ x : Configuration 2, ∫ y : Configuration 2,
        (∏ i : Fin 2, φ (i.natAdd 2) (x i, y i)) *
          (momentKernel 2 θ τ₂ x y).toReal) := by
  let ν : Fin 2 → Measure (Configuration 2 × Configuration 2) := fun i =>
    if i.val = 0 then slabMomentKernelEndpointMeasure θ τ₁
      else slabMomentKernelEndpointMeasure θ τ₂
  have hloc (i : Fin 2) : IsLocallyFiniteMeasure (ν i) := by
    dsimp [ν]
    split_ifs with hi
    · exact locallyFinite_momentKernelMeasure 2 θ hτ₁
    · exact locallyFinite_momentKernelMeasure 2 θ hτ₂
  have hσ (i : Fin 2) : SigmaFinite (ν i) :=
    @MeasureTheory.sigmaFinite_of_locallyFinite (Configuration 2 × Configuration 2) _
      (ν i) inferInstance inferInstance (hloc i)
  let φ₁ : Fin 2 → C_c(Plane × Plane, ℝ) := fun i => φ (i.castAdd 2)
  let φ₂ : Fin 2 → C_c(Plane × Plane, ℝ) := fun i => φ (i.natAdd 2)
  let H : Fin 2 → C_c((Configuration 2 × Configuration 2), ℝ) :=
    ![slabMomentBlockTensorTest φ₁, slabMomentBlockTensorTest φ₂]
  have hgroup (z : Fin 2 → Configuration 2 × Configuration 2) :
      slabSeparatedGroupedTest (slabCompactPiTensorTest φ) z = ∏ i : Fin 2, H i (z i) := by
    rw [slabSeparatedGroupedTest_apply, slabCompactPiTensorTest_apply]
    rw [Fin.prod_univ_four, Fin.prod_univ_two]
    simp [H, slabSeparatedArrayHomeomorph, slabSeparatedArrayEquiv,
      slabMomentBlockTensorTest, φ₁, φ₂, Fin.prod_univ_two]
    ring
  have hfact := @MeasureTheory.integral_fintype_prod_eq_prod ℝ (Fin 2)
    inferInstance inferInstance (fun _ => Configuration 2 × Configuration 2)
    (fun i z => H i z) (mE := fun _ => inferInstance) (μ := ν) hσ
  change (∫ z, slabSeparatedGroupedTest (slabCompactPiTensorTest φ) z
      ∂Measure.pi ν) = _
  rw [show (fun z : Fin 2 → Configuration 2 × Configuration 2 =>
      slabSeparatedGroupedTest (slabCompactPiTensorTest φ) z) =
      (fun z => ∏ i, H i (z i)) from funext hgroup, hfact]
  rw [Fin.prod_univ_two]
  simp [H, ν]
  rw [integral_slabMomentBlockTensorTest θ hτ₁ φ₁,
    integral_slabMomentBlockTensorTest θ hτ₂ φ₂]
  simp [φ₁, φ₂, Fin.prod_univ_two]

end Critical2DKPZ.SHF.Flow

end
