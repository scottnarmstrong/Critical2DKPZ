/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedLaplaceWord
import Critical2DKPZ.SHF.Tsai.ConjugatedComposition
import Critical2DKPZ.SHF.Flow.WeightMeasurability
import Mathlib.Tactic

/-! # Conjugated Laplace bounds for complete nonempty diagrams -/

@[expose] public noncomputable section

open MeasureTheory Critical2DKPZ.DeltaBose Critical2DKPZ.SHF.Flow
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Compose the initial endpoint, first collision, and the admissible suffix.
Every coefficient is uniform over the collision labels and the word. -/
theorem weightedFormBound_laplace_diagram_conj {n : ℕ} (θ : ℝ) {p a rate : ℝ}
    (hp : 1 < p) (ha : 0 ≤ a)
    (hrEndpoint : conjugatedEndpointShift n hp ha < rate)
    (hrSwap : conjugatedSwappingThreshold n hp ha ≤ rate)
    (hrCollision : 2 * n * a ^ 2 < rate)
    (hθ : θ < Real.log (rate - 2 * n * a ^ 2))
    (α : CollisionPair n) (w : List (CollisionPair n)) (hword : collisionListNoAdjacentRepeat (α :: w)) :
    WeightedFormBound volume volume (fun x => -(a * configurationOneNorm x))
      (fun y => a * configurationOneNorm y) p (p / (p - 1))
      (laplaceTimeKernel rate (fun q : ℝ × Configuration n × Configuration n =>
        diagramKernel θ (α :: w) q.1 q.2.1 q.2.2))
      (conjugatedEndpointLaplaceFactor n hp ha rate (1 / p) *
        (conjugatedCollisionLaplaceFactor n θ a rate *
          ((ENNReal.ofReal (conjugatedSwappingConstant n hp ha) *
            conjugatedCollisionLaplaceFactor n θ a rate) ^ w.length *
              conjugatedEndpointLaplaceFactor n hp ha rate (1 - 1 / p)))) := by
  have hSuffix := weightedFormBound_laplace_path_conj θ hp ha hrEndpoint hrSwap hrCollision hθ α w hword
  have hCollision := weightedFormBound_laplace_collision_conj α θ hp ha hrCollision hθ
  have hOutgoing := weightedFormBound_laplace_free_outgoing_conj_uniform hp ha α hrEndpoint
  have hCollisionMeas : Measurable (Function.uncurry
      (laplaceTimeKernel rate (collisionTimeKernel α θ))) :=
    measurable_laplaceTimeKernel rate (measurable_collisionTimeKernel α θ)
  have hSuffixMeas : Measurable (Function.uncurry
      (laplaceTimeKernel rate (pathTimeKernel θ w (collisionEmbedding α) id))) :=
    measurable_laplaceTimeKernel rate
      (measurable_pathTimeKernel θ w (measurable_collisionEmbedding α) measurable_id)
  have hWeight : Measurable (fun z : FusedConfiguration α => a * fusedOneNorm α z) :=
    measurable_const.mul (measurable_fusedOneNorm α)
  have hCollisionComp := WeightedFormBound.comp_conjugateExponent hp hWeight
    hCollisionMeas hSuffixMeas hCollision hSuffix
  have hOutgoingMeas : Measurable (Function.uncurry
      (laplaceTimeKernel rate (freeTimeKernel id (collisionEmbedding α)))) :=
    measurable_laplaceTimeKernel rate (measurable_freeTimeKernel measurable_id (measurable_collisionEmbedding α))
  have hCompMeas : Measurable (Function.uncurry
      (spatialKernelComp volume (laplaceTimeKernel rate (collisionTimeKernel α θ))
        (laplaceTimeKernel rate (pathTimeKernel θ w (collisionEmbedding α) id)))) :=
    measurable_spatialKernelComp volume hCollisionMeas hSuffixMeas
  have hCompose := WeightedFormBound.comp_conjugateExponent hp hWeight
    hOutgoingMeas hCompMeas hOutgoing hCollisionComp
  have hPathEq : laplaceTimeKernel rate (pathTimeKernel θ (α :: w) id id) =
      spatialKernelComp volume (laplaceTimeKernel rate (freeTimeKernel id (collisionEmbedding α)))
        (spatialKernelComp volume (laplaceTimeKernel rate (collisionTimeKernel α θ))
          (laplaceTimeKernel rate (pathTimeKernel θ w (collisionEmbedding α) id))) := by
    funext x y
    exact laplaceTimeKernel_pathTimeKernel_cons θ rate α w measurable_id measurable_id x y
  rw [← hPathEq] at hCompose
  have hDiagramEq : laplaceTimeKernel rate (pathTimeKernel θ (α :: w) id id) =
      laplaceTimeKernel rate (fun q : ℝ × Configuration n × Configuration n =>
        diagramKernel θ (α :: w) q.1 q.2.1 q.2.2) := by
    funext x y
    rw [pathTimeKernel_eq_diagram θ (α :: w) measurable_id measurable_id,
      laplaceTimeKernel_causalKernel]
    rfl
  rw [hDiagramEq] at hCompose
  exact hCompose

end Critical2DKPZ.SHF.Tsai

end
