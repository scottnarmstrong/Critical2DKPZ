/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedLaplaceWordConstants
public import Critical2DKPZ.SHF.Tsai.ConjugatedLaplaceSwapConstants
public import Critical2DKPZ.SHF.DeltaBose.ChainSummability
import Critical2DKPZ.SHF.Tsai.ConjugatedComposition
import Critical2DKPZ.SHF.Flow.WeightMeasurability
import Mathlib.Tactic

/-! # Conjugated Laplace estimates for literal collision paths -/

@[expose] public noncomputable section

open MeasureTheory Critical2DKPZ.DeltaBose Critical2DKPZ.SHF.Flow
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Every admissible suffix has the product of its integrated swapping and
collision bounds, followed by the precise terminal endpoint Laplace power. -/
theorem weightedFormBound_laplace_path_conj {n : ℕ} (θ : ℝ) {p a rate : ℝ}
    (hp : 1 < p) (ha : 0 ≤ a)
    (hrEndpoint : conjugatedEndpointShift n hp ha < rate)
    (hrSwap : conjugatedSwappingThreshold n hp ha ≤ rate)
    (hrCollision : 2 * n * a ^ 2 < rate)
    (hθ : θ < Real.log (rate - 2 * n * a ^ 2)) :
    ∀ (β : CollisionPair n) (w : List (CollisionPair n)),
      collisionListNoAdjacentRepeat (β :: w) →
      WeightedFormBound volume volume (fun z => -(a * fusedOneNorm β z))
        (fun y => a * configurationOneNorm y) p (p / (p - 1))
        (laplaceTimeKernel rate (pathTimeKernel θ w (collisionEmbedding β) id))
        ((ENNReal.ofReal (conjugatedSwappingConstant n hp ha) *
          conjugatedCollisionLaplaceFactor n θ a rate) ^ w.length *
          conjugatedEndpointLaplaceFactor n hp ha rate (1 - 1 / p)) := by
  let S : ℝ≥0∞ := ENNReal.ofReal (conjugatedSwappingConstant n hp ha)
  let J : ℝ≥0∞ := conjugatedCollisionLaplaceFactor n θ a rate
  let I : ℝ≥0∞ := conjugatedEndpointLaplaceFactor n hp ha rate (1 - 1 / p)
  intro β w
  induction w generalizing β with
  | nil =>
    intro _hword
    have hKernel : laplaceTimeKernel rate (pathTimeKernel θ [] (collisionEmbedding β) id) =
        laplaceTimeKernel rate (freeTimeKernel (collisionEmbedding β) id) := by
      funext z y
      exact laplaceTimeKernel_causalKernel rate _ z y
    rw [hKernel]
    simpa only [List.length_nil, pow_zero, one_mul] using
      weightedFormBound_laplace_free_incoming_conj_uniform hp ha β hrEndpoint
  | cons γ w ih =>
    intro hword
    change β ≠ γ ∧ collisionListNoAdjacentRepeat (γ :: w) at hword
    have hrec := ih γ hword.2
    have hSwap := weightedFormBound_laplace_free_swapping_conj_uniform hp ha β γ hword.1 hrSwap
    have hCollision : WeightedFormBound volume volume (fun z => -(a * fusedOneNorm γ z))
        (fun z => a * fusedOneNorm γ z) p (p / (p - 1))
        (laplaceTimeKernel rate (collisionTimeKernel γ θ)) J :=
      weightedFormBound_laplace_collision_conj γ θ hp ha hrCollision hθ
    have hCollisionMeas : Measurable (Function.uncurry
        (laplaceTimeKernel rate (collisionTimeKernel γ θ))) :=
      measurable_laplaceTimeKernel rate (measurable_collisionTimeKernel γ θ)
    have hPathMeas : Measurable (Function.uncurry
        (laplaceTimeKernel rate (pathTimeKernel θ w (collisionEmbedding γ) id))) :=
      measurable_laplaceTimeKernel rate
        (measurable_pathTimeKernel θ w (measurable_collisionEmbedding γ) measurable_id)
    have hWeight : Measurable (fun z : FusedConfiguration γ => a * fusedOneNorm γ z) :=
      measurable_const.mul (measurable_fusedOneNorm γ)
    have hCollisionComp := WeightedFormBound.comp_conjugateExponent hp hWeight
      hCollisionMeas hPathMeas hCollision hrec
    have hSwapMeas : Measurable (Function.uncurry
        (laplaceTimeKernel rate (freeTimeKernel (collisionEmbedding β) (collisionEmbedding γ)))) :=
      measurable_laplaceTimeKernel rate
        (measurable_freeTimeKernel (measurable_collisionEmbedding β) (measurable_collisionEmbedding γ))
    have hCompMeas : Measurable (Function.uncurry
        (spatialKernelComp volume (laplaceTimeKernel rate (collisionTimeKernel γ θ))
          (laplaceTimeKernel rate (pathTimeKernel θ w (collisionEmbedding γ) id)))) :=
      measurable_spatialKernelComp volume hCollisionMeas hPathMeas
    have hCompose := WeightedFormBound.comp_conjugateExponent hp hWeight
      hSwapMeas hCompMeas hSwap hCollisionComp
    have hPathEq : laplaceTimeKernel rate (pathTimeKernel θ (γ :: w) (collisionEmbedding β) id) =
        spatialKernelComp volume
          (laplaceTimeKernel rate (freeTimeKernel (collisionEmbedding β) (collisionEmbedding γ)))
          (spatialKernelComp volume (laplaceTimeKernel rate (collisionTimeKernel γ θ))
            (laplaceTimeKernel rate (pathTimeKernel θ w (collisionEmbedding γ) id))) := by
      funext z y
      exact laplaceTimeKernel_pathTimeKernel_cons θ rate γ w
        (measurable_collisionEmbedding β) measurable_id z y
    have hconst : S * (J * ((S * J) ^ w.length * I)) = (S * J) ^ (w.length + 1) * I := by
      rw [pow_succ]
      ac_rfl
    change WeightedFormBound volume volume (fun z => -(a * fusedOneNorm β z))
      (fun y => a * configurationOneNorm y) p (p / (p - 1)) _
      (S * (J * ((S * J) ^ w.length * I))) at hCompose
    rw [hconst] at hCompose
    rw [hPathEq]
    simpa only [List.length_cons] using hCompose

end Critical2DKPZ.SHF.Tsai

end
