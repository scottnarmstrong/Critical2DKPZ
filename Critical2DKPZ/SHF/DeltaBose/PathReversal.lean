/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.PathKernel
import Mathlib.Tactic

/-! # Reversal of chronological collision paths -/

public section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- Transposing a causal free time kernel exchanges its two configuration maps. -/
theorem freeTimeKernel_causal_transpose {n : ℕ} {X Y : Type}
    (eX : X → Configuration n) (eY : Y → Configuration n) :
    timeKernelTranspose (causalKernel (freeTimeKernel eX eY)) =
      causalKernel (freeTimeKernel eY eX) := by
  funext ⟨t, y, x⟩
  by_cases ht : 0 < t
  · simp only [timeKernelTranspose, causalKernel, ht, ite_true, freeTimeKernel]
    exact congrArg ENNReal.ofReal (freeKernel_symm n t _ _)
  · simp only [timeKernelTranspose, causalKernel, ht, ite_false]

/-- A causal collision time kernel is symmetric in its endpoints. -/
theorem collisionTimeKernel_causal_transpose {n : ℕ} (α : CollisionPair n) (θ : ℝ) :
    timeKernelTranspose (causalKernel (collisionTimeKernel α θ)) =
      causalKernel (collisionTimeKernel α θ) := by
  funext ⟨t, z, w⟩
  by_cases ht : 0 < t
  · simp only [timeKernelTranspose, causalKernel, ht, ite_true, collisionTimeKernel]
    exact congrArg ENNReal.ofReal (collisionKernel_symm α θ t _ _)
  · simp only [timeKernelTranspose, causalKernel, ht, ite_false]

/-- Split the last collision from a chronological path. -/
theorem pathTimeKernel_append_singleton {n : ℕ} (θ : ℝ) (w : List (CollisionPair n))
    (α : CollisionPair n) :
    ∀ {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
      {eX : X → Configuration n} {eY : Y → Configuration n},
      Measurable eX → Measurable eY →
      pathTimeKernel θ (w ++ [α]) eX eY =
        timeKernelComp volume (pathTimeKernel θ w eX (collisionEmbedding α))
          (timeKernelComp volume (causalKernel (collisionTimeKernel α θ))
            (causalKernel (freeTimeKernel (collisionEmbedding α) eY))) := by
  induction w with
  | nil => intro X Y _ _ eX eY hX hY; rfl
  | cons β w ih =>
    intro X Y _ _ eX eY hX hY
    have hE := measurable_causalKernel (measurable_freeTimeKernel hX (measurable_collisionEmbedding β))
    have hJ := measurable_causalKernel (measurable_collisionTimeKernel β θ)
    have hT := measurable_pathTimeKernel θ w (measurable_collisionEmbedding β) (measurable_collisionEmbedding α)
    have hS := measurable_timeKernelComp volume
      (measurable_causalKernel (measurable_collisionTimeKernel α θ))
      (measurable_causalKernel (measurable_freeTimeKernel (measurable_collisionEmbedding α) hY))
    simp only [List.cons_append, pathTimeKernel]
    rw [ih (measurable_collisionEmbedding β) hY]
    symm
    rw [timeKernelComp_assoc volume volume hE (measurable_timeKernelComp volume hJ hT) hS,
      timeKernelComp_assoc volume volume hJ hT hS]

/-- Transposing a collision path reverses the collision word and both endpoint spaces. -/
theorem pathTimeKernel_transpose {n : ℕ} (θ : ℝ) (w : List (CollisionPair n)) :
    ∀ {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
      {eX : X → Configuration n} {eY : Y → Configuration n},
      Measurable eX → Measurable eY →
      timeKernelTranspose (pathTimeKernel θ w eX eY) = pathTimeKernel θ w.reverse eY eX := by
  induction w with
  | nil =>
    intro X Y _ _ eX eY hX hY
    exact freeTimeKernel_causal_transpose eX eY
  | cons α w ih =>
    intro X Y _ _ eX eY hX hY
    have hE := measurable_causalKernel (measurable_freeTimeKernel hX (measurable_collisionEmbedding α))
    have hJ := measurable_causalKernel (measurable_collisionTimeKernel α θ)
    have hT := measurable_pathTimeKernel θ w (measurable_collisionEmbedding α) hY
    change timeKernelTranspose
      (timeKernelComp volume (causalKernel (freeTimeKernel eX (collisionEmbedding α)))
        (timeKernelComp volume (causalKernel (collisionTimeKernel α θ))
          (pathTimeKernel θ w (collisionEmbedding α) eY))) = _
    rw [timeKernelComp_transpose volume hE (measurable_timeKernelComp volume hJ hT),
      timeKernelComp_transpose volume hJ hT,
      ih (measurable_collisionEmbedding α) hY, collisionTimeKernel_causal_transpose,
      freeTimeKernel_causal_transpose, List.reverse_cons,
      pathTimeKernel_append_singleton θ w.reverse α hY hX]
    exact timeKernelComp_assoc volume volume
      (measurable_pathTimeKernel θ w.reverse hY (measurable_collisionEmbedding α)) hJ
      (measurable_causalKernel (measurable_freeTimeKernel (measurable_collisionEmbedding α) hX))

end Critical2DKPZ.DeltaBose
