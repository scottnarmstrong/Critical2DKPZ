/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.HeadBlockBounds
public import Critical2DKPZ.SHF.Tsai.HeadTail
import Mathlib.Tactic

/-! # Weighted bound for one fixed collision slice -/

@[expose] public section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

private theorem measurable_collisionENNKernel {n : ℕ} (α : CollisionPair n)
    (θ v : ℝ) :
    Measurable (Function.uncurry
      (fun z z' : FusedConfiguration α => ENNReal.ofReal (collisionKernel α θ v z z'))) := by
  have hArgs : Measurable (fun p : FusedConfiguration α × FusedConfiguration α => ((θ, v), p)) :=
    measurable_const.prodMk measurable_id
  exact ((measurable_collisionKernel α).comp hArgs).ennreal_ofReal

private theorem measurable_incomingENNKernel {n : ℕ} (α : CollisionPair n)
    (t : ℝ) :
    Measurable (Function.uncurry
      (fun z : FusedConfiguration α => fun y : Configuration n =>
        ENNReal.ofReal (incomingKernel α t z y))) := by
  exact ((measurable_incomingKernel α).comp
    (measurable_const.prodMk measurable_id)).ennreal_ofReal

private theorem measurable_collisionOutgoingSlice {n : ℕ} (α : CollisionPair n)
    (θ v q : ℝ) :
    Measurable (Function.uncurry
      (spatialKernelComp volume
        (fun z z' : FusedConfiguration α => ENNReal.ofReal (collisionKernel α θ v z z'))
        (fun z' : FusedConfiguration α => fun y : Configuration n =>
          ENNReal.ofReal (incomingKernel α q z' y)))) := by
  exact measurable_spatialKernelComp volume
    (measurable_collisionENNKernel α θ v) (measurable_incomingENNKernel α q)

/-- A collision kernel composed with a free incoming strand has an unweighted `L²` form bound given by the product of their time coefficients. -/
private theorem exists_weightedFormBound_collisionOutgoingSlice {n : ℕ}
    (α : CollisionPair n) (θ : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ v q : ℝ, 0 < v → 0 < q →
      WeightedFormBound volume volume (fun _ : FusedConfiguration α => 0)
        (fun _ : Configuration n => 0) 2 2
        (spatialKernelComp volume
          (fun z z' : FusedConfiguration α => ENNReal.ofReal (collisionKernel α θ v z z'))
          (fun z' : FusedConfiguration α => fun y : Configuration n =>
            ENNReal.ofReal (incomingKernel α q z' y)))
        (ENNReal.ofReal (c * scalarDensity θ v * q ^ (-(1 : ℝ) / 2))) := by
  obtain ⟨cOut, hcOut, hOut⟩ := weightedFormBound_incoming_L2 α
  let c : ℝ := 4 * Real.pi * cOut
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro v q hv hq
  have hColForm := formBound_collisionKernel_scalarDensity α θ hv
  have hCol : WeightedFormBound volume volume (fun _ : FusedConfiguration α => 0)
      (fun _ : FusedConfiguration α => 0) 2 2
      (fun z z' => ENNReal.ofReal (collisionKernel α θ v z z'))
      (ENNReal.ofReal (4 * Real.pi * scalarDensity θ v)) :=
    WeightedFormBound.ofFormBound hColForm
  have hOut' : WeightedFormBound volume volume (fun _ : FusedConfiguration α => 0)
      (fun _ : Configuration n => 0) 2 2
      (fun z y => ENNReal.ofReal (incomingKernel α q z y))
      (ENNReal.ofReal (cOut * q ^ (-(1 : ℝ) / 2))) := by
    simpa only [show -(1 : ℝ) / 2 = -(1 : ℝ) / 2 by rfl] using hOut q hq
  have hComp := WeightedFormBound.comp_two
    (measurable_collisionENNKernel α θ v) (measurable_incomingENNKernel α q) hCol hOut'
  have hscalar : 0 < scalarDensity θ v := scalarDensity_pos θ hv
  have hqpow : 0 < q ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos hq _
  have hcoeff : ENNReal.ofReal (4 * Real.pi * scalarDensity θ v) *
        ENNReal.ofReal (cOut * q ^ (-(1 : ℝ) / 2)) =
      ENNReal.ofReal (c * scalarDensity θ v * q ^ (-(1 : ℝ) / 2)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    dsimp [c]
    ring
  change WeightedFormBound volume volume (fun _ : FusedConfiguration α => 0)
    (fun _ : Configuration n => 0) 2 2
    (spatialKernelComp volume
      (fun z z' : FusedConfiguration α => ENNReal.ofReal (collisionKernel α θ v z z'))
      (fun z' : FusedConfiguration α => fun y : Configuration n =>
        ENNReal.ofReal (incomingKernel α q z' y))) _
  simpa only [hcoeff] using hComp

/-- A one-collision slice has a bilinear bound between an exponentially weighted `Lᵖ` test and an unweighted `L²` test, with its three time factors explicit. -/
theorem exists_weightedFormBound_oneCollisionSpatialSlice {n : ℕ}
    (α : CollisionPair n) (θ : ℝ) {p a : ℝ} (hp : 2 < p) (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∀ r v q : ℝ, 0 < r → 0 < v → 0 < q →
      WeightedFormBound volume volume
        (fun x : Configuration n => a * configurationOneNorm x)
        (fun _ : Configuration n => 0) 2 p
        (oneCollisionSpatialSlice α θ r v q)
        (ENNReal.ofReal (c * r ^ (-1 / p) * scalarDensity θ v * q ^ (-(1 : ℝ) / 2))) := by
  obtain ⟨cIn, hcIn, hIn⟩ := weightedFormBound_incoming_adjoint α hp ha
  obtain ⟨cMid, hcMid, hMid⟩ := exists_weightedFormBound_collisionOutgoingSlice α θ
  let c : ℝ := cIn * cMid
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro r v q hr hv hq
  let KIn : Configuration n → FusedConfiguration α → ℝ≥0∞ := fun x z =>
    ENNReal.ofReal (incomingKernel α r z x)
  let KMid : FusedConfiguration α → Configuration n → ℝ≥0∞ := fun z y =>
    spatialKernelComp volume
      (fun z₀ z₁ : FusedConfiguration α => ENNReal.ofReal (collisionKernel α θ v z₀ z₁))
      (fun z₁ : FusedConfiguration α => fun y : Configuration n =>
        ENNReal.ofReal (incomingKernel α q z₁ y)) z y
  have hInMeas : Measurable (Function.uncurry KIn) := by
    dsimp [KIn]
    exact ((measurable_incomingKernel α).comp
      (measurable_const.prodMk (measurable_snd.prodMk measurable_fst))).ennreal_ofReal
  have hMidMeas : Measurable (Function.uncurry KMid) := by
    dsimp [KMid]
    exact measurable_collisionOutgoingSlice α θ v q
  have hIn' := hIn r hr
  have hMid' := hMid v q hv hq
  have hFull := WeightedFormBound.comp_two hInMeas hMidMeas hIn' hMid'
  have hcoeff : ENNReal.ofReal (cIn * r ^ (-1 / p)) *
        ENNReal.ofReal (cMid * scalarDensity θ v * q ^ (-(1 : ℝ) / 2)) =
      ENNReal.ofReal (c * r ^ (-1 / p) * scalarDensity θ v * q ^ (-(1 : ℝ) / 2)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    dsimp [c]
    ring
  change WeightedFormBound volume volume
      (fun x : Configuration n => a * configurationOneNorm x)
      (fun _ : Configuration n => 0) 2 p
      (spatialKernelComp volume KIn KMid) _
  simpa only [oneCollisionSpatialSlice, KIn, KMid, hcoeff] using hFull

end Critical2DKPZ.SHF.Tsai

end
