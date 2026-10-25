/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.TailLaplaceEndpoint
public import Critical2DKPZ.SHF.DeltaBose.LaplaceFormBounds
public import Critical2DKPZ.SHF.DeltaBose.ChainSummability
import Mathlib.Tactic

/-! # Laplace-domain weighted bounds for literal tail words -/

@[expose] public section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Chosen coefficient in the Laplace-weighted incoming estimate for one pair. -/
noncomputable def laplaceIncomingWordConstant {p a : ℝ}
    (hp : 2 < p) (ha : 0 < a) (α : CollisionPair 4) : ℝ :=
  Classical.choose (exists_weightedFormBound_laplace_incoming_to_L2 α hp ha)





/-- Chosen coefficient in the rate-scaled Laplace incoming estimate for one
four-particle collision pair. -/
noncomputable def laplaceIncomingScaledWordConstant {p a : ℝ}
    (hp : 2 < p) (ha : 0 < a) (α : CollisionPair 4) : ℝ :=
  Classical.choose (exists_weightedFormBound_laplace_incoming_to_L2_scaled α hp ha)

private theorem laplaceIncomingScaledWordConstant_spec {p a : ℝ}
    (hp : 2 < p) (ha : 0 < a) (α : CollisionPair 4) :
    0 < laplaceIncomingScaledWordConstant hp ha α ∧
      ∀ rate : ℝ, 0 < rate →
        WeightedFormBound volume volume (fun _ : FusedConfiguration α => 0)
          (fun x : Configuration 4 => a * configurationOneNorm x) p 2
          (laplaceTimeKernel rate (freeTimeKernel (collisionEmbedding α) id))
          (ENNReal.ofReal (laplaceIncomingScaledWordConstant hp ha α *
            (1 / rate) ^ (1 - 1 / p))) := by
  simpa [laplaceIncomingScaledWordConstant] using
    Classical.choose_spec (exists_weightedFormBound_laplace_incoming_to_L2_scaled α hp ha)

/-- Uniform-in-pair coefficient for the rate-scaled Laplace incoming bound. -/
noncomputable def laplaceIncomingScaledUniformConstant {p a : ℝ}
    (hp : 2 < p) (ha : 0 < a) : ℝ :=
  max 1 (∑ α : CollisionPair 4, laplaceIncomingScaledWordConstant hp ha α)

private theorem laplaceIncomingScaledWordConstant_le_uniform {p a : ℝ}
    (hp : 2 < p) (ha : 0 < a) (α : CollisionPair 4) :
    laplaceIncomingScaledWordConstant hp ha α ≤ laplaceIncomingScaledUniformConstant hp ha := by
  classical
  have hsum : laplaceIncomingScaledWordConstant hp ha α ≤
      ∑ β : CollisionPair 4, laplaceIncomingScaledWordConstant hp ha β := by
    exact Finset.single_le_sum
      (fun β hβ => (laplaceIncomingScaledWordConstant_spec hp ha β).1.le)
      (Finset.mem_univ α)
  exact hsum.trans (le_max_right _ _)

private theorem weightedFormBound_laplace_incoming_scaled_uniform {p a : ℝ}
    (hp : 2 < p) (ha : 0 < a) {rate : ℝ} (hrate : 0 < rate)
    (α : CollisionPair 4) :
    WeightedFormBound volume volume (fun _ : FusedConfiguration α => 0)
      (fun x : Configuration 4 => a * configurationOneNorm x) p 2
      (laplaceTimeKernel rate (freeTimeKernel (collisionEmbedding α) id))
      (ENNReal.ofReal (laplaceIncomingScaledUniformConstant hp ha *
        (1 / rate) ^ (1 - 1 / p))) := by
  apply WeightedFormBound.mono
    ((laplaceIncomingScaledWordConstant_spec hp ha α).2 rate hrate)
  · intro z y
    exact le_rfl
  · apply ENNReal.ofReal_le_ofReal
    have hpow : 0 < (1 / rate) ^ (1 - 1 / p) := by
      apply Real.rpow_pos_of_pos
      positivity
    exact mul_le_mul_of_nonneg_right
      (laplaceIncomingScaledWordConstant_le_uniform hp ha α) hpow.le

private theorem weightedFormBound_laplace_pathWord_of_endpoint
    {p a : ℝ} {θ rate : ℝ} (hrate : 0 < rate)
    (hθ : θ < Real.log rate) (E : ℝ≥0∞)
    (hEnd : ∀ α : CollisionPair 4,
      WeightedFormBound volume volume (fun _ : FusedConfiguration α => 0)
        (fun x : Configuration 4 => a * configurationOneNorm x) p 2
        (laplaceTimeKernel rate (freeTimeKernel (collisionEmbedding α) id)) E) :
    ∀ (β : CollisionPair 4) (w : List (CollisionPair 4)),
      collisionListNoAdjacentRepeat (β :: w) →
      WeightedFormBound volume volume (fun _ : FusedConfiguration β => 0)
        (fun y : Configuration 4 => a * configurationOneNorm y) p 2
        (laplaceTimeKernel rate (pathTimeKernel θ w (collisionEmbedding β) id))
        (integratedPotentialRowConstant ^ w.length *
          (laplaceCollisionResolventConstant θ rate ^ w.length * E)) := by
  intro β w
  induction w generalizing β with
  | nil =>
      intro hword
      change WeightedFormBound volume volume (fun _ : FusedConfiguration β => 0)
        (fun y : Configuration 4 => a * configurationOneNorm y) p 2
        (laplaceTimeKernel rate
          (causalKernel (freeTimeKernel (collisionEmbedding β) id)))
        (integratedPotentialRowConstant ^ 0 *
          (laplaceCollisionResolventConstant θ rate ^ 0 * E))
      have hKernelEq :
          laplaceTimeKernel rate (causalKernel
            (freeTimeKernel (collisionEmbedding β) id)) =
            laplaceTimeKernel rate (freeTimeKernel (collisionEmbedding β) id) := by
        funext z y
        exact laplaceTimeKernel_causalKernel rate _ z y
      rw [hKernelEq]
      simpa only [pow_zero, one_mul, mul_one] using hEnd β
  | cons γ w ih =>
      intro hword
      change β ≠ γ ∧ collisionListNoAdjacentRepeat (γ :: w) at hword
      have hrec := ih γ hword.2
      have hRateNonneg : 0 ≤ rate := hrate.le
      have hSwapForm := formBound_laplace_swapping β γ hword.1 hRateNonneg
      have hSwap : WeightedFormBound volume volume
          (fun _ : FusedConfiguration β => 0) (fun _ : FusedConfiguration γ => 0)
          2 2 (laplaceTimeKernel rate
            (freeTimeKernel (collisionEmbedding β) (collisionEmbedding γ)))
          integratedPotentialRowConstant :=
        WeightedFormBound.ofFormBound hSwapForm
      have hratePos : 0 < rate := hrate
      have hCollisionForm := formBound_laplace_collision γ hratePos hθ
      have hCollision : WeightedFormBound volume volume
          (fun _ : FusedConfiguration γ => 0) (fun _ => 0) 2 2
          (laplaceTimeKernel rate (collisionTimeKernel γ θ))
          (laplaceCollisionResolventConstant θ rate) := by
        apply WeightedFormBound.ofFormBound
        simpa [laplaceCollisionResolventConstant] using hCollisionForm
      have hCollisionMeas : Measurable (Function.uncurry
          (laplaceTimeKernel rate (collisionTimeKernel γ θ))) :=
        measurable_laplaceTimeKernel rate (measurable_collisionTimeKernel γ θ)
      have hPathMeas : Measurable (Function.uncurry
          (laplaceTimeKernel rate (pathTimeKernel θ w (collisionEmbedding γ) id))) :=
        measurable_laplaceTimeKernel rate
          (measurable_pathTimeKernel θ w (measurable_collisionEmbedding γ) measurable_id)
      have hCollisionComp := WeightedFormBound.comp_two hCollisionMeas hPathMeas
        hCollision hrec
      have hSwapMeas : Measurable (Function.uncurry
          (laplaceTimeKernel rate
            (freeTimeKernel (collisionEmbedding β) (collisionEmbedding γ)))) :=
        measurable_laplaceTimeKernel rate
          (measurable_freeTimeKernel (measurable_collisionEmbedding β)
            (measurable_collisionEmbedding γ))
      have hCollisionCompMeas : Measurable (Function.uncurry
          (spatialKernelComp volume
            (laplaceTimeKernel rate (collisionTimeKernel γ θ))
            (laplaceTimeKernel rate (pathTimeKernel θ w (collisionEmbedding γ) id)))) :=
        measurable_spatialKernelComp volume hCollisionMeas hPathMeas
      have hCompose := WeightedFormBound.comp_two hSwapMeas hCollisionCompMeas
        hSwap hCollisionComp
      have hPathEq :
          laplaceTimeKernel rate (pathTimeKernel θ (γ :: w) (collisionEmbedding β) id) =
            spatialKernelComp volume
              (laplaceTimeKernel rate
                (freeTimeKernel (collisionEmbedding β) (collisionEmbedding γ)))
              (spatialKernelComp volume
                (laplaceTimeKernel rate (collisionTimeKernel γ θ))
                (laplaceTimeKernel rate (pathTimeKernel θ w (collisionEmbedding γ) id))) := by
        funext z y
        exact laplaceTimeKernel_pathTimeKernel_cons θ rate γ w
          (measurable_collisionEmbedding β) measurable_id z y
      rw [hPathEq]
      have hconst :
          integratedPotentialRowConstant *
              (laplaceCollisionResolventConstant θ rate *
                (integratedPotentialRowConstant ^ w.length *
                  (laplaceCollisionResolventConstant θ rate ^ w.length * E))) =
            integratedPotentialRowConstant ^ (w.length + 1) *
              (laplaceCollisionResolventConstant θ rate ^ (w.length + 1) * E) := by
        rw [pow_succ, pow_succ]
        ac_rfl
      rw [hconst] at hCompose
      rw [List.length_cons]
      exact hCompose



/-- The Laplace transform of an admissible tail word with the rate decay of
its terminal incoming factor retained. This is the form used when a collision
or swapping interval is selected as the longest time interval. -/
theorem weightedFormBound_laplace_tailWord_scaled {p a θ rate : ℝ}
    (hp : 2 < p) (ha : 0 < a) (hrate : 0 < rate) (hθ : θ < Real.log rate)
    (β : CollisionPair 4) (w : List (CollisionPair 4))
    (hword : collisionListNoAdjacentRepeat (β :: w)) :
    WeightedFormBound volume volume (fun _ : FusedConfiguration β => 0)
      (fun y : Configuration 4 => a * configurationOneNorm y) p 2
      (laplaceTimeKernel rate (tailWordTimeKernel θ β w))
      (laplaceCollisionResolventConstant θ rate *
        (integratedPotentialRowConstant ^ w.length *
          (laplaceCollisionResolventConstant θ rate ^ w.length *
            ENNReal.ofReal (laplaceIncomingScaledUniformConstant hp ha *
              (1 / rate) ^ (1 - 1 / p))))) := by
  let E : ℝ≥0∞ := ENNReal.ofReal (laplaceIncomingScaledUniformConstant hp ha *
    (1 / rate) ^ (1 - 1 / p))
  have hPath := weightedFormBound_laplace_pathWord_of_endpoint (p := p) (a := a) hrate hθ E (by
    intro α
    exact weightedFormBound_laplace_incoming_scaled_uniform hp ha hrate α) β w hword
  have hCollisionForm := formBound_laplace_collision β hrate hθ
  have hCollision : WeightedFormBound volume volume
      (fun _ : FusedConfiguration β => 0) (fun _ => 0) 2 2
      (laplaceTimeKernel rate (collisionTimeKernel β θ))
      (laplaceCollisionResolventConstant θ rate) := by
    apply WeightedFormBound.ofFormBound
    simpa [laplaceCollisionResolventConstant] using hCollisionForm
  have hCollisionMeas : Measurable (Function.uncurry
      (laplaceTimeKernel rate (collisionTimeKernel β θ))) :=
    measurable_laplaceTimeKernel rate (measurable_collisionTimeKernel β θ)
  have hPathMeas : Measurable (Function.uncurry
      (laplaceTimeKernel rate (pathTimeKernel θ w (collisionEmbedding β) id))) :=
    measurable_laplaceTimeKernel rate
      (measurable_pathTimeKernel θ w (measurable_collisionEmbedding β) measurable_id)
  have hCompose := WeightedFormBound.comp_two hCollisionMeas hPathMeas hCollision hPath
  have hTailEq : laplaceTimeKernel rate (tailWordTimeKernel θ β w) =
      fun z y => spatialKernelComp volume
        (laplaceTimeKernel rate (collisionTimeKernel β θ))
        (laplaceTimeKernel rate (pathTimeKernel θ w (collisionEmbedding β) id)) z y := by
    funext z y
    unfold tailWordTimeKernel
    exact laplaceTimeKernel_timeKernelComp_causal volume
      (measurable_collisionTimeKernel β θ)
      (measurable_pathTimeKernel θ w (measurable_collisionEmbedding β) measurable_id)
      rate z y
  rw [hTailEq]
  exact hCompose

end Critical2DKPZ.SHF.Tsai

end
