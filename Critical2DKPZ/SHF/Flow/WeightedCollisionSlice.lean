/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.KernelConjugation
public import Critical2DKPZ.SHF.Flow.WeightMeasurability
public import Critical2DKPZ.SHF.DeltaBose.CollisionWeight

/-! # The weighted spatial slice of a single collision -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- Compose the weighted incoming, collision, and outgoing block bounds. -/
theorem oneCollisionSpatialSlice_weighted_l2_sq_le {n : ℕ} (α : CollisionPair n) (θ : ℝ)
    {a r s q : ℝ} (ha : 0 ≤ a) (hr : 0 < r) (hs : 0 < s) (hq : 0 < q)
    {f : Configuration n → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x : Configuration n, (∫⁻ y : Configuration n,
      expConjugate (fun x => a * configurationOneNorm x) (fun y => a * configurationOneNorm y)
        (oneCollisionSpatialSlice α θ r s q) x y * f y) ^ 2) ≤
      (ENNReal.ofReal (weightGrowth n a r) ^ 2 * ENNReal.ofReal (4 * Real.pi * (2 * r))⁻¹) *
        (ENNReal.ofReal (weightGrowth n a s * (4 * Real.pi * scalarDensity θ s)) ^ 2 *
          (ENNReal.ofReal (weightGrowth n a q) ^ 2 * ENNReal.ofReal (4 * Real.pi * (2 * q))⁻¹)) *
        ∫⁻ y : Configuration n, f y ^ 2 := by
  let A : Configuration n → ℝ := fun x => a * configurationOneNorm x
  let B : FusedConfiguration α → ℝ := fun z => a * fusedOneNorm α z
  have hA : Measurable A := measurable_const.mul (measurable_configurationOneNorm n)
  have hB : Measurable B := measurable_const.mul (measurable_fusedOneNorm α)
  let K : Configuration n → FusedConfiguration α → ℝ≥0∞ :=
    fun x z => ENNReal.ofReal (incomingKernel α r z x)
  let C : FusedConfiguration α → FusedConfiguration α → ℝ≥0∞ :=
    fun z w => ENNReal.ofReal (collisionKernel α θ s z w)
  let L : FusedConfiguration α → Configuration n → ℝ≥0∞ :=
    fun z y => ENNReal.ofReal (incomingKernel α q z y)
  have hK : Measurable (Function.uncurry K) := by
    exact ((measurable_incomingKernel α).comp
      (measurable_const.prodMk (measurable_snd.prodMk measurable_fst))).ennreal_ofReal
  have hC : Measurable (Function.uncurry C) := by
    have hp : Measurable (fun p : FusedConfiguration α × FusedConfiguration α => ((θ, s), p)) :=
      measurable_const.prodMk measurable_id
    exact ((measurable_collisionKernel α).comp hp).ennreal_ofReal
  have hL : Measurable (Function.uncurry L) :=
    ((measurable_incomingKernel α).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hKb : ∀ {g : FusedConfiguration α → ℝ≥0∞}, Measurable g →
      (∫⁻ x : Configuration n, (∫⁻ z, expConjugate A B K x z * g z) ^ 2) ≤
        (ENNReal.ofReal (weightGrowth n a r) ^ 2 * ENNReal.ofReal (4 * Real.pi * (2 * r))⁻¹) *
          ∫⁻ z : FusedConfiguration α, g z ^ 2 := by
    intro g hg
    simpa only [A, B, K, expConjugate_ofReal, ← mul_sub] using
      incomingKernel_adjoint_weighted_l2_sq_le α ha hr hg
  have hCb : ∀ {g : FusedConfiguration α → ℝ≥0∞}, Measurable g →
      (∫⁻ z : FusedConfiguration α, (∫⁻ w, expConjugate B B C z w * g w) ^ 2) ≤
        ENNReal.ofReal (weightGrowth n a s * (4 * Real.pi * scalarDensity θ s)) ^ 2 *
          ∫⁻ w : FusedConfiguration α, g w ^ 2 := by
    intro g hg
    simpa only [B, C, expConjugate_ofReal, ← mul_sub] using
      collisionKernel_weighted_l2_sq_le α θ ha hs hg
  have hLb : ∀ {g : Configuration n → ℝ≥0∞}, Measurable g →
      (∫⁻ z : FusedConfiguration α, (∫⁻ y, expConjugate B A L z y * g y) ^ 2) ≤
        (ENNReal.ofReal (weightGrowth n a q) ^ 2 * ENNReal.ofReal (4 * Real.pi * (2 * q))⁻¹) *
          ∫⁻ y : Configuration n, g y ^ 2 := by
    intro g hg
    simpa only [A, B, L, expConjugate_ofReal, ← mul_sub] using
      incomingKernel_weighted_l2_sq_le α ha hq hg
  have hCL := measurable_spatialKernelComp volume hC hL
  have hCLb := fun {g : Configuration n → ℝ≥0∞} (hg : Measurable g) =>
    expConjugate_spatialKernelComp_l2_sq_le volume volume volume hB hB hA hC hL hCb hLb hg
  exact expConjugate_spatialKernelComp_l2_sq_le volume volume volume hA hB hA hK hCL hKb hCLb hf

end Critical2DKPZ.SHF.Flow

end
