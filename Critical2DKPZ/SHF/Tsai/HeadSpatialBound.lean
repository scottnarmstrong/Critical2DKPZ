/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.HeadTensorBound
public import Critical2DKPZ.SHF.Tsai.HeadDeletedConvolution
import Mathlib.Tactic

/-! # A pointwise weighted bound for the deleted-coordinate head block -/

@[expose] public section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

private theorem measurable_oneCollisionSpatialSlice {α : CollisionPair 3}
    (θ r v q : ℝ) :
    Measurable (Function.uncurry (oneCollisionSpatialSlice α θ r v q)) := by
  have hIn : Measurable (Function.uncurry
      (fun x : Configuration 3 => fun z : FusedConfiguration α =>
        ENNReal.ofReal (incomingKernel α r z x))) := by
    exact ((measurable_incomingKernel α).comp
      (measurable_const.prodMk (measurable_snd.prodMk measurable_fst))).ennreal_ofReal
  have hCol : Measurable (Function.uncurry
      (fun z z' : FusedConfiguration α => ENNReal.ofReal (collisionKernel α θ v z z'))) := by
    have hp : Measurable (fun p : FusedConfiguration α × FusedConfiguration α =>
        ((θ, v), p)) := measurable_const.prodMk measurable_id
    exact ((measurable_collisionKernel α).comp hp).ennreal_ofReal
  have hOut : Measurable (Function.uncurry
      (fun z : FusedConfiguration α => fun y : Configuration 3 =>
        ENNReal.ofReal (incomingKernel α q z y))) := by
    exact ((measurable_incomingKernel α).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hInner : Measurable (Function.uncurry
      (spatialKernelComp volume
        (fun z z' : FusedConfiguration α => ENNReal.ofReal (collisionKernel α θ v z z'))
        (fun z' : FusedConfiguration α => fun y : Configuration 3 =>
          ENNReal.ofReal (incomingKernel α q z' y)))) :=
    measurable_spatialKernelComp volume hCol hOut
  change Measurable (Function.uncurry
    (spatialKernelComp volume
      (fun x : Configuration 3 => fun z : FusedConfiguration α =>
        ENNReal.ofReal (incomingKernel α r z x))
      (spatialKernelComp volume
        (fun z z' : FusedConfiguration α =>
          ENNReal.ofReal (collisionKernel α θ v z z'))
        (fun z' : FusedConfiguration α => fun y : Configuration 3 =>
          ENNReal.ofReal (incomingKernel α q z' y)))))
  exact measurable_spatialKernelComp volume hIn hInner

private theorem configurationOneNorm_omitted_split (i : Fin 4)
    (x : Configuration 4) :
    configurationOneNorm x = configurationOneNorm (omittedFullPart i x) +
      planeOneNorm (x i) := by
  classical
  rw [configurationOneNorm, configurationOneNorm]
  have hsum := Fin.sum_univ_succAbove
    (fun j : Fin 4 => planeOneNorm (x j)) i
  calc
    (∑ j : Fin 4, planeOneNorm (x j)) =
        planeOneNorm (x i) + ∑ k : Fin 3, planeOneNorm (x (i.succAbove k)) := hsum
    _ = planeOneNorm (x i) +
        ∑ k : Fin 3, planeOneNorm (omittedFullPart i x k) := by
          rfl
    _ = _ := by ac_rfl

/-- At fixed positive strand durations, deleting a free label leaves the
three-particle one-collision operator and contributes one planar heat
point-evaluation factor. -/
theorem exists_weightedFormBound_deletedHeadSpatialSlice {α β : CollisionPair 4}
    (i : Fin 4) (hi₁ : α.1.1 ≠ i) (hi₂ : α.1.2 ≠ i)
    (hβ : i = β.1.1 ∨ i = β.1.2) (θ : ℝ) {p a : ℝ}
    (hp : 2 < p) (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∀ r v q : ℝ, 0 < r → 0 < v → 0 < q →
      WeightedFormBound volume volume
        (fun x : Configuration 4 => a * configurationOneNorm x)
        (fun _ : FusedConfiguration β => 0) 2 p
        (fun x w => ENNReal.ofReal (heatKernel (r + v + q) (w.1 - x i)) *
          deletedHeadSpatialSlice i hi₁ hi₂ θ r v q x w)
        (ENNReal.ofReal (c * r ^ (-1 / p) * scalarDensity θ v *
          q ^ (-(1 : ℝ) / 2) * (r + v + q) ^ (-1 / p))) := by
  obtain ⟨c₁, hc₁, hOne⟩ :=
    exists_weightedFormBound_oneCollisionSpatialSlice
      (omittedCollisionPair i α hi₁ hi₂) θ hp ha
  obtain ⟨c₂, hc₂, hEval⟩ := integral_heatKernel_mul_le (by linarith : 1 < p)
  let c : ℝ := c₁ * c₂
  have hc : 0 < c := by positivity
  refine ⟨c, hc, ?_⟩
  intro r v q hr hv hq
  let γ := omittedCollisionPair i α hi₁ hi₂
  let eX := omittedFullConfigurationEquiv i
  let eY : FusedConfiguration β ≃ᵐ Configuration 3 :=
    (omittedBetaConfigurationEquiv i β hβ).trans (omittedConfigurationEquiv i).symm
  let η : Configuration 3 → Plane := fun y => (eY.symm y).1
  let R : Configuration 3 → Configuration 3 → ℝ≥0∞ :=
    oneCollisionSpatialSlice γ θ r v q
  have hN : Measurable (configurationOneNorm : Configuration 3 → ℝ) :=
    measurable_configurationOneNorm
  have hη : Measurable η := by
    exact measurable_fst.comp eY.symm.measurable
  have hR : Measurable (Function.uncurry R) := by
    exact measurable_oneCollisionSpatialSlice θ r v q
  have hBase := hOne r v q hr hv hq
  have hAttached := WeightedFormBound.planarHeatFactor_of_eval
    (by linarith : 1 < p) (le_of_lt ha) hN hη hR (fun s hs y ψ hψ => hEval s hs y ψ hψ)
    hBase (r + v + q) (by linarith)
  have hMPX := measurePreserving_omittedFullConfigurationEquiv i
  have hMPY := (measurePreserving_omittedConfigurationEquiv i).symm.comp
    (measurePreserving_omittedBetaConfigurationEquiv i β hβ)
  have hPull := WeightedFormBound.pullback eX eY hMPX hMPY hAttached
  have hY (w : FusedConfiguration β) :
      eY w = omittedFullPart i (collisionEmbedding β w) := by
    funext k
    change omittedBetaConfigurationEquiv i β hβ w (omittedLabelsEquiv i k) =
      collisionEmbedding β w ((omittedLabelsEquiv i k).1)
    exact omittedBetaConfigurationEquiv_apply i β hβ w (omittedLabelsEquiv i k)
  have hXi (x : Configuration 4) : (eX x).2 = x i := by
    change (Critical2DKPZ.DeltaBose.splitCoordinate i x).2 = x i
    rw [Critical2DKPZ.DeltaBose.splitCoordinate_apply]
  have hNorm (x : Configuration 4) :
      configurationOneNorm x = configurationOneNorm (eX x).1 +
        planeOneNorm (eX x).2 := by
    rw [configurationOneNorm_omitted_split i x]
    simp only [eX, omittedFullPart]
    rw [hXi]
  have hSlice (x : Configuration 4) (w : FusedConfiguration β) :
      deletedHeadSpatialSlice i hi₁ hi₂ θ r v q x w =
        R (eX x).1 (eY w) := by
    dsimp [deletedHeadSpatialSlice, γ, R]
    rw [hY]
    have hX : (eX x).1 = omittedFullPart i x := rfl
    rw [hX, oneCollisionSpatialSlice_eq_integral]
  have hEta (w : FusedConfiguration β) : η (eY w) = w.1 := by
    simp [η]
  have hKernel (x : Configuration 4) (w : FusedConfiguration β) :
      ENNReal.ofReal (heatKernel (r + v + q) (w.1 - x i)) *
        deletedHeadSpatialSlice i hi₁ hi₂ θ r v q x w =
      ENNReal.ofReal (heatKernel (r + v + q)
        (η (eY w) - (eX x).2)) * R (eX x).1 (eY w) := by
    rw [hSlice, hEta, hXi]
  have hWeightX (x : Configuration 4) :
      a * (configurationOneNorm (eX x).1 + planeOneNorm (eX x).2) =
        a * configurationOneNorm x := by
    rw [← hNorm x]
  have hPull' :
      WeightedFormBound volume volume
        (fun x : Configuration 4 => a * configurationOneNorm x)
        (fun _ : FusedConfiguration β => 0) 2 p
        (fun x w => ENNReal.ofReal (heatKernel (r + v + q) (w.1 - x i)) *
          deletedHeadSpatialSlice i hi₁ hi₂ θ r v q x w)
        (ENNReal.ofReal (c₁ * r ^ (-1 / p) * scalarDensity θ v *
          q ^ (-(1 : ℝ) / 2)) *
          ENNReal.ofReal (c₂ * (r + v + q) ^ (-1 / p))) := by
    simpa only [Function.comp_apply, hWeightX, hKernel] using hPull
  have hcoef :
      ENNReal.ofReal (c₁ * r ^ (-1 / p) * scalarDensity θ v * q ^ (-(1 : ℝ) / 2)) *
          ENNReal.ofReal (c₂ * (r + v + q) ^ (-1 / p)) =
        ENNReal.ofReal (c * r ^ (-1 / p) * scalarDensity θ v *
          q ^ (-(1 : ℝ) / 2) * (r + v + q) ^ (-1 / p)) := by
    have hscalar : 0 < scalarDensity θ v := scalarDensity_pos θ hv
    have hrpow : 0 < r ^ (-1 / p) := Real.rpow_pos_of_pos hr _
    have hqpow : 0 < q ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hq _
    have hspow : 0 < (r + v + q) ^ (-1 / p) :=
      Real.rpow_pos_of_pos (by linarith) _
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    dsimp [c]
    ring
  simpa only [hcoef] using hPull'

end Critical2DKPZ.SHF.Tsai

end
