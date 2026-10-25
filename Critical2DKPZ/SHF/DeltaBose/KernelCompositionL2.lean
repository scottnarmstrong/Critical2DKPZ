/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.CollisionResolvent
public import Critical2DKPZ.SHF.DeltaBose.PotentialIntegratedSchur
public import Critical2DKPZ.SHF.DeltaBose.TraceL2
public import Critical2DKPZ.SHF.DeltaBose.TwoParticle
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Composition of nonnegative kernels on squared L²

Spatial composition multiplies kernel-action bounds for extended nonnegative kernels, without requiring pointwise finiteness. -/

@[expose] public section

open MeasureTheory
open Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- Spatial composition of two nonnegative kernels. -/
noncomputable def spatialKernelComp {X Y Z : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (K : X → Y → ℝ≥0∞) (L : Y → Z → ℝ≥0∞) : X → Z → ℝ≥0∞ :=
  fun x z => ∫⁻ y, K x y * L y z ∂ν

/-- Joint measurability of a spatial composition of positive kernels. -/
theorem measurable_spatialKernelComp {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] (ν : Measure Y)
    [SFinite ν] {K : X → Y → ℝ≥0∞} {L : Y → Z → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) (hL : Measurable (Function.uncurry L)) :
    Measurable (Function.uncurry (spatialKernelComp ν K L)) := by
  have hF : Measurable (fun p : (X × Z) × Y => K p.1.1 p.2 * L p.2 p.1.2) := by
    exact (hK.comp (measurable_fst.fst.prodMk measurable_snd)).mul
      (hL.comp (measurable_snd.prodMk measurable_fst.snd))
  exact hF.lintegral_prod_right'

/-- Measurability of the action of a positive kernel on measurable data. -/
theorem measurable_kernelAction {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure Y) [SFinite ν]
    {K : X → Y → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {f : Y → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun x => ∫⁻ y, K x y * f y ∂ν) := by
  have hF : Measurable (fun p : X × Y => K p.1 p.2 * f p.2) :=
    hK.mul (hf.comp measurable_snd)
  exact hF.lintegral_prod_right' (ν := ν)

/-- Kernel action of a spatial composition is the iterated kernel action. -/
theorem spatialKernelComp_action_eq {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Y) (ρ : Measure Z) [SFinite ν] [SFinite ρ]
    {K : X → Y → ℝ≥0∞} {L : Y → Z → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) (hL : Measurable (Function.uncurry L))
    {f : Z → ℝ≥0∞} (hf : Measurable f) (x : X) :
    (∫⁻ z, spatialKernelComp ν K L x z * f z ∂ρ) =
      ∫⁻ y, K x y * (∫⁻ z, L y z * f z ∂ρ) ∂ν := by
  have hKx : Measurable (fun y : Y => K x y) :=
    hK.comp (measurable_const.prodMk measurable_id)
  have hLxy : Measurable (fun p : Z × Y => L p.2 p.1) :=
    hL.comp (measurable_snd.prodMk measurable_fst)
  have hF : Measurable (fun p : Z × Y =>
      (K x p.2 * L p.2 p.1) * f p.1) :=
    ((hKx.comp measurable_snd).mul hLxy).mul (hf.comp measurable_fst)
  have hLx : ∀ y, Measurable (fun z => L y z * f z) := fun y =>
    (hL.comp (measurable_const.prodMk measurable_id)).mul hf
  have hKL (z : Z) : Measurable (fun y : Y => K x y * L y z) :=
    hKx.mul (hL.comp (measurable_id.prodMk measurable_const))
  calc (∫⁻ z, spatialKernelComp ν K L x z * f z ∂ρ)
      = ∫⁻ z, ∫⁻ y, K x y * L y z * f z ∂ν ∂ρ := by
          apply lintegral_congr
          intro z
          rw [spatialKernelComp]
          calc (∫⁻ y, K x y * L y z ∂ν) * f z
              = ∫⁻ y, (K x y * L y z) * f z ∂ν :=
                  (lintegral_mul_const _ (hKL z)).symm
            _ = ∫⁻ y, K x y * L y z * f z ∂ν := by
                  apply lintegral_congr
                  intro y
                  simp only [mul_assoc]
    _ = ∫⁻ y, ∫⁻ z, K x y * L y z * f z ∂ρ ∂ν :=
          lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ y, K x y * (∫⁻ z, L y z * f z ∂ρ) ∂ν := by
          apply lintegral_congr
          intro y
          calc (∫⁻ z, K x y * L y z * f z ∂ρ)
              = ∫⁻ z, K x y * (L y z * f z) ∂ρ := by
                  apply lintegral_congr
                  intro z
                  simp only [mul_assoc]
            _ = K x y * (∫⁻ z, L y z * f z ∂ρ) :=
                  lintegral_const_mul _ (hLx y)

/-- The squared `L²` operator bound multiplies under spatial kernel
composition. -/
theorem spatialKernelComp_l2_sq_le {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) (ρ : Measure Z)
    [SFinite μ] [SFinite ν] [SFinite ρ]
    {K : X → Y → ℝ≥0∞} {L : Y → Z → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) (hL : Measurable (Function.uncurry L))
    {A B : ℝ≥0∞}
    (hKbound : ∀ {g : Y → ℝ≥0∞}, Measurable g →
      (∫⁻ x, (∫⁻ y, K x y * g y ∂ν) ^ 2 ∂μ) ≤ A ^ 2 * ∫⁻ y, g y ^ 2 ∂ν)
    (hLbound : ∀ {f : Z → ℝ≥0∞}, Measurable f →
      (∫⁻ y, (∫⁻ z, L y z * f z ∂ρ) ^ 2 ∂ν) ≤ B ^ 2 * ∫⁻ z, f z ^ 2 ∂ρ)
    {f : Z → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, (∫⁻ z, spatialKernelComp ν K L x z * f z ∂ρ) ^ 2 ∂μ) ≤
      (A * B) ^ 2 * ∫⁻ z, f z ^ 2 ∂ρ := by
  let g : Y → ℝ≥0∞ := fun y => ∫⁻ z, L y z * f z ∂ρ
  have hg : Measurable g := by
    exact measurable_kernelAction ρ hL hf
  have hcomp (x : X) :
      (∫⁻ z, spatialKernelComp ν K L x z * f z ∂ρ) =
        ∫⁻ y, K x y * g y ∂ν :=
    spatialKernelComp_action_eq ν ρ hK hL hf x
  calc (∫⁻ x, (∫⁻ z, spatialKernelComp ν K L x z * f z ∂ρ) ^ 2 ∂μ)
      = ∫⁻ x, (∫⁻ y, K x y * g y ∂ν) ^ 2 ∂μ := by
          apply lintegral_congr
          intro x
          rw [hcomp x]
    _ ≤ A ^ 2 * ∫⁻ y, g y ^ 2 ∂ν := hKbound hg
    _ ≤ A ^ 2 * (B ^ 2 * ∫⁻ z, f z ^ 2 ∂ρ) :=
          mul_le_mul' le_rfl (hLbound hf)
    _ = (A * B) ^ 2 * ∫⁻ z, f z ^ 2 ∂ρ := by rw [mul_pow, mul_assoc]

/-- Composition also multiplies estimates stated directly in squared-norm
form, without choosing square roots of the constants. -/
theorem spatialKernelComp_l2_sq_mul_le {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) (ρ : Measure Z)
    [SFinite μ] [SFinite ν] [SFinite ρ]
    {K : X → Y → ℝ≥0∞} {L : Y → Z → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) (hL : Measurable (Function.uncurry L))
    {A B : ℝ≥0∞}
    (hKbound : ∀ {g : Y → ℝ≥0∞}, Measurable g →
      (∫⁻ x, (∫⁻ y, K x y * g y ∂ν) ^ 2 ∂μ) ≤ A * ∫⁻ y, g y ^ 2 ∂ν)
    (hLbound : ∀ {f : Z → ℝ≥0∞}, Measurable f →
      (∫⁻ y, (∫⁻ z, L y z * f z ∂ρ) ^ 2 ∂ν) ≤ B * ∫⁻ z, f z ^ 2 ∂ρ)
    {f : Z → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, (∫⁻ z, spatialKernelComp ν K L x z * f z ∂ρ) ^ 2 ∂μ) ≤
      (A * B) * ∫⁻ z, f z ^ 2 ∂ρ := by
  let g : Y → ℝ≥0∞ := fun y => ∫⁻ z, L y z * f z ∂ρ
  have hg : Measurable g := measurable_kernelAction ρ hL hf
  have hcomp (x : X) :
      (∫⁻ z, spatialKernelComp ν K L x z * f z ∂ρ) =
        ∫⁻ y, K x y * g y ∂ν :=
    spatialKernelComp_action_eq ν ρ hK hL hf x
  calc
    (∫⁻ x, (∫⁻ z, spatialKernelComp ν K L x z * f z ∂ρ) ^ 2 ∂μ)
        = ∫⁻ x, (∫⁻ y, K x y * g y ∂ν) ^ 2 ∂μ := by
          apply lintegral_congr
          intro x
          rw [hcomp x]
    _ ≤ A * ∫⁻ y, g y ^ 2 ∂ν := hKbound hg
    _ ≤ A * (B * ∫⁻ z, f z ^ 2 ∂ρ) := mul_le_mul' le_rfl (hLbound hf)
    _ = (A * B) * ∫⁻ z, f z ^ 2 ∂ρ := by rw [mul_assoc]

/-- The spatial part of a one-collision diagram at fixed incoming, collision,
and outgoing durations. -/
noncomputable def oneCollisionSpatialSlice {n : ℕ} (α : CollisionPair n)
    (θ r s q : ℝ) (x y : Configuration n) : ℝ≥0∞ :=
  spatialKernelComp volume
    (fun x z => ENNReal.ofReal (incomingKernel α r z x))
    (spatialKernelComp volume
      (fun z z' => ENNReal.ofReal (collisionKernel α θ s z z'))
      (fun z' y => ENNReal.ofReal (incomingKernel α q z' y))) x y


/-- Spatial composition of the incoming, repeated-collision and outgoing kernels equals the spatial integral in the one-collision diagram. -/
theorem oneCollisionSpatialSlice_eq_integral {n : ℕ} (α : CollisionPair n)
    (θ r s q : ℝ) (x y : Configuration n) :
    oneCollisionSpatialSlice α θ r s q x y =
      ∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
        ENNReal.ofReal (incomingKernel α r z x) *
          ENNReal.ofReal (collisionKernel α θ s z z') *
            ENNReal.ofReal (freeKernel n q (collisionEmbedding α z') y) := by
  have hC : Measurable (Function.uncurry
      (fun z : FusedConfiguration α => fun z' : FusedConfiguration α =>
        ENNReal.ofReal (collisionKernel α θ s z z'))) := by
    have hp : Measurable (fun p : FusedConfiguration α × FusedConfiguration α =>
        ((θ, s), p)) := measurable_const.prodMk measurable_id
    exact ((measurable_collisionKernel α).comp hp).ennreal_ofReal
  have hO : Measurable (fun z' : FusedConfiguration α =>
      ENNReal.ofReal (incomingKernel α q z' y)) := by
    exact ((measurable_incomingKernel α).comp
      (measurable_const.prodMk (measurable_id.prodMk measurable_const))).ennreal_ofReal
  have hI (z : FusedConfiguration α) : Measurable (fun z' : FusedConfiguration α =>
      ENNReal.ofReal (collisionKernel α θ s z z') *
        ENNReal.ofReal (incomingKernel α q z' y)) :=
    (hC.comp (measurable_const.prodMk measurable_id)).mul hO
  have hfree (z' : FusedConfiguration α) :
      incomingKernel α q z' y = freeKernel n q (collisionEmbedding α z') y := by
    unfold incomingKernel
    exact freeKernel_symm n q y (collisionEmbedding α z')
  unfold oneCollisionSpatialSlice spatialKernelComp
  calc
    (∫⁻ z : FusedConfiguration α,
        ENNReal.ofReal (incomingKernel α r z x) *
          ∫⁻ z' : FusedConfiguration α,
            ENNReal.ofReal (collisionKernel α θ s z z') *
              ENNReal.ofReal (incomingKernel α q z' y))
        = ∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
            ENNReal.ofReal (incomingKernel α r z x) *
              (ENNReal.ofReal (collisionKernel α θ s z z') *
                ENNReal.ofReal (incomingKernel α q z' y)) := by
          apply lintegral_congr
          intro z
          rw [← lintegral_const_mul _ (hI z)]
    _ = ∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
          ENNReal.ofReal (incomingKernel α r z x) *
            ENNReal.ofReal (collisionKernel α θ s z z') *
              ENNReal.ofReal (freeKernel n q (collisionEmbedding α z') y) := by
          apply lintegral_congr
          intro z
          apply lintegral_congr
          intro z'
          rw [hfree z']
          ac_rfl


/-- A squared `L²` kernel-action bound gives the corresponding nonnegative
bilinear form bound. -/
theorem kernelAction_bilinear_l2_sq_le {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] {K : X → Y → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) {C : ℝ≥0∞}
    (hKsq : ∀ {f : Y → ℝ≥0∞}, Measurable f →
      (∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ (2 : ℝ) ∂μ) ≤
        C ^ 2 * ∫⁻ y, f y ^ (2 : ℝ) ∂ν)
    {f : Y → ℝ≥0∞} (hf : Measurable f) {g : X → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ x, (∫⁻ y, K x y * f y ∂ν) * g x ∂μ) ≤
      C * (∫⁻ y, f y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) *
        (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
  have hact : AEMeasurable (fun x : X => ∫⁻ y : Y, K x y * f y ∂ν) μ := by
    have hMeas : Measurable (fun p : X × Y => K p.1 p.2 * f p.2) :=
      hK.mul (hf.comp measurable_snd)
    exact ⟨_, hMeas.lintegral_prod_right' (ν := ν), Filter.EventuallyEq.rfl⟩
  have hg' : AEMeasurable g μ := ⟨g, hg, Filter.EventuallyEq.rfl⟩
  have hroot :
      (∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) ≤
        C * (∫⁻ y, f y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) := by
    calc
      (∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) ≤
          (C ^ 2 * ∫⁻ y, f y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) :=
            ENNReal.monotone_rpow_of_nonneg (by norm_num) (hKsq hf)
      _ = C * (∫⁻ y, f y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
            rw [← ENNReal.rpow_natCast_mul]
            norm_num
  calc
    (∫⁻ x, (∫⁻ y, K x y * f y ∂ν) * g x ∂μ) ≤
        (∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
          (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) :=
            ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hact hg'
    _ ≤ C * (∫⁻ y, f y ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) *
          (∫⁻ x, g x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
            exact mul_le_mul' hroot le_rfl



end Critical2DKPZ.DeltaBose
