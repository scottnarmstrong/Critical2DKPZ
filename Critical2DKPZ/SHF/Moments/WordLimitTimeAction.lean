/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.PathKernel
public import Critical2DKPZ.SHF.DeltaBose.KernelCompositionL2

/-! # Terminal testing commutes with positive time-kernel composition -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

/-- Move nonnegative terminal testing through a chronological kernel
composition. Tonelli applies even when a starting point is on a diagonal. -/
theorem lintegral_timeKernelComp_mul {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Y) (ρ : Measure Z) [SFinite ν] [SFinite ρ]
    {K : TimeKernel X Y} {L : TimeKernel Y Z}
    (hK : Measurable K) (hL : Measurable L)
    {f : Z → ℝ≥0∞} (hf : Measurable f) (t : ℝ) (x : X) :
    (∫⁻ z, timeKernelComp ν K L (t, x, z) * f z ∂ρ) =
      ∫⁻ q : ℝ × Y, K (q.1, x, q.2) *
        (∫⁻ z, L (t - q.1, q.2, z) * f z ∂ρ) ∂volume.prod ν := by
  exact spatialKernelComp_action_eq (volume.prod ν) ρ
    (K := fun x q => K (q.1, x, q.2))
    (L := fun q z => L (t - q.1, q.2, z))
    (hK.comp (by fun_prop)) (hL.comp (by fun_prop)) hf x

/-- At positive elapsed time, testing the chronological kernel equals testing the diagram kernel. -/
theorem lintegral_diagramKernel_eq_pathTimeKernel {h : ℕ}
    (θ t : ℝ) (ht : 0 < t) (w : List (CollisionPair h))
    (f : Configuration h → ℝ≥0∞) (x : Configuration h) :
    (∫⁻ y : Configuration h, diagramKernel θ w t x y * f y) =
      ∫⁻ y : Configuration h, pathTimeKernel θ w id id (t, x, y) * f y := by
  have heq := pathTimeKernel_eq_diagram θ w
    (eX := id) (eY := id) measurable_id measurable_id
  apply lintegral_congr
  intro y
  have hp := congrFun heq (t, x, y)
  rw [causalKernel_of_pos _ ht] at hp
  exact congrArg (fun k => k * f y) hp.symm

/-- The continuum terminal functional peels its first free strand and
collision run with the same order as the lattice recursion. -/
theorem lintegral_pathTimeKernel_cons_mul {h : ℕ}
    (θ t : ℝ) (α : CollisionPair h) (w : List (CollisionPair h))
    {f : Configuration h → ℝ≥0∞} (hf : Measurable f) (x : Configuration h) :
    (∫⁻ y : Configuration h, pathTimeKernel θ (α :: w) id id (t, x, y) * f y) =
      ∫⁻ q : ℝ × FusedConfiguration α,
        causalKernel (freeTimeKernel id (collisionEmbedding α)) (q.1, x, q.2) *
        ∫⁻ p : ℝ × FusedConfiguration α,
          causalKernel (collisionTimeKernel α θ) (p.1, q.2, p.2) *
          ∫⁻ y : Configuration h,
            pathTimeKernel θ w (collisionEmbedding α) id
              (t - q.1 - p.1, p.2, y) * f y := by
  have hfree := measurable_causalKernel
    (measurable_freeTimeKernel measurable_id (measurable_collisionEmbedding α))
  have hrun := measurable_causalKernel (measurable_collisionTimeKernel α θ)
  have htail := measurable_pathTimeKernel θ w (measurable_collisionEmbedding α) measurable_id
  rw [pathTimeKernel, lintegral_timeKernelComp_mul volume volume hfree
    (measurable_timeKernelComp volume hrun htail) hf]
  apply lintegral_congr
  intro q
  rw [lintegral_timeKernelComp_mul volume volume hrun htail hf]
  simp only [Measure.volume_eq_prod]

end Critical2DKPZ.SHF.Moments
