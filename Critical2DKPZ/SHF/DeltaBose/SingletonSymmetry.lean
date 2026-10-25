/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.TimeReversal
public import Critical2DKPZ.SHF.DeltaBose.TwoParticle
import Mathlib.Tactic

/-! # Endpoint exchange for a single resummed collision and the two-particle kernel -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- Spatially integrated single-collision contribution at fixed ordered times. -/
noncomputable def collisionSlice {n : ℕ} (α : CollisionPair n) (θ h : ℝ)
    (x y : Configuration n) (r u : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : FusedConfiguration α, ∫⁻ w : FusedConfiguration α,
    ENNReal.ofReal (incomingKernel α r z x) *
    ENNReal.ofReal (collisionKernel α θ (u - r) z w) *
    ENNReal.ofReal (freeKernel n (h - u) (collisionEmbedding α w) y)

/-- The spatially integrated collision slice is jointly measurable in its two time variables. -/
theorem measurable_collisionSlice {n : ℕ} (α : CollisionPair n) (θ h : ℝ)
    (x y : Configuration n) : Measurable (Function.uncurry (collisionSlice α θ h x y)) := by
  apply Measurable.lintegral_prod_right
  apply Measurable.lintegral_prod_right
  let R := ((ℝ × ℝ) × FusedConfiguration α) × FusedConfiguration α
  have hr : Measurable (fun p : R => p.1.1.1) := by fun_prop
  have hu : Measurable (fun p : R => p.1.1.2) := by fun_prop
  have hz : Measurable (fun p : R => p.1.2) := by fun_prop
  have hw : Measurable (fun p : R => p.2) := measurable_snd
  have hi : Measurable (fun p : R => ENNReal.ofReal (incomingKernel α p.1.1.1 p.1.2 x)) :=
    ((measurable_incomingKernel α).comp
    (hr.prodMk (hz.prodMk measurable_const))).ennreal_ofReal
  have hc : Measurable (fun p : R => ENNReal.ofReal
      (collisionKernel α θ (p.1.1.2 - p.1.1.1) p.1.2 p.2)) :=
    ((measurable_collisionKernel α).comp
    ((measurable_const.prodMk (hu.sub hr)).prodMk (hz.prodMk hw))).ennreal_ofReal
  have ho : Measurable (fun p : R => ENNReal.ofReal
      (freeKernel n (h - p.1.1.2) (collisionEmbedding α p.2) y)) :=
    ((measurable_freeKernel n).comp
    ((measurable_const.sub hu).prodMk
      (((measurable_collisionEmbedding α).comp hw).prodMk measurable_const))).ennreal_ofReal
  exact (hi.mul hc).mul ho

/-- The fixed-time spatial contribution reverses under exchange of its collision coordinates. -/
theorem collisionSlice_reverse {n : ℕ} (α : CollisionPair n) (θ h : ℝ)
    (x y : Configuration n) (r u : ℝ) :
    collisionSlice α θ h x y (h - u) (h - r) = collisionSlice α θ h y x r u := by
  have hm : Measurable (fun p : FusedConfiguration α × FusedConfiguration α =>
      ENNReal.ofReal (incomingKernel α (h - u) p.1 x) *
      ENNReal.ofReal (collisionKernel α θ (u - r) p.1 p.2) *
      ENNReal.ofReal (freeKernel n r (collisionEmbedding α p.2) y)) := by
    have hi : Measurable (fun p : FusedConfiguration α × FusedConfiguration α =>
        ENNReal.ofReal (incomingKernel α (h - u) p.1 x)) :=
      ((measurable_incomingKernel α).comp
      (measurable_const.prodMk (measurable_fst.prodMk measurable_const))).ennreal_ofReal
    have hc := ((measurable_collisionKernel α).comp
      (show Measurable (fun p : FusedConfiguration α × FusedConfiguration α =>
        ((θ, u - r), p)) from measurable_const.prodMk measurable_id)).ennreal_ofReal
    have ho : Measurable (fun p : FusedConfiguration α × FusedConfiguration α =>
        ENNReal.ofReal (freeKernel n r (collisionEmbedding α p.2) y)) :=
      ((measurable_freeKernel n).comp
      (measurable_const.prodMk
        (((measurable_collisionEmbedding α).comp measurable_snd).prodMk measurable_const))).ennreal_ofReal
    exact (hi.mul hc).mul ho
  unfold collisionSlice
  rw [show (h - r) - (h - u) = u - r by ring, sub_sub_cancel]
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr
  intro w
  apply lintegral_congr
  intro z
  rw [collisionKernel_symm α θ (u - r) z w]
  have hi : incomingKernel α (h - u) z x = freeKernel n (h - u) (collisionEmbedding α z) x :=
    freeKernel_symm n (h - u) _ _
  have ho : freeKernel n r (collisionEmbedding α w) y = incomingKernel α r w y :=
    freeKernel_symm n r _ _
  rw [hi, ho]
  ac_rfl

/-- Endpoint exchange preserves the single-collision diagram. -/
theorem diagramKernel_singleton_symm {n : ℕ} (α : CollisionPair n) (θ h : ℝ)
    (x y : Configuration n) : diagramKernel θ [α] h x y = diagramKernel θ [α] h y x := by
  change (∫⁻ r in Ioo 0 h, ∫⁻ u in Ioo r h, collisionSlice α θ h x y r u) =
    ∫⁻ r in Ioo 0 h, ∫⁻ u in Ioo r h, collisionSlice α θ h y x r u
  rw [lintegral_orderedPair_reverse h (measurable_collisionSlice α θ h x y)]
  apply lintegral_congr
  intro r
  apply lintegral_congr
  intro u
  exact collisionSlice_reverse α θ h x y r u

/-- The two-particle correction kernel is symmetric in its initial and terminal configurations. -/
theorem twoParticleCorrection_symm (θ h : ℝ) (x y : Configuration 2) :
    twoParticleCorrection θ h x y = twoParticleCorrection θ h y x :=
  diagramKernel_singleton_symm pairTwo θ h x y

/-- Endpoint symmetry of the complete two-particle moment kernel. -/
theorem momentKernel_two_symm (θ h : ℝ) (x y : Configuration 2) :
    momentKernel 2 θ h x y = momentKernel 2 θ h y x := by
  rw [momentKernel_two, momentKernel_two, twoParticleCorrection_symm θ h x y]
  congr 1
  have he := freeKernel_symm 2 h x y
  simp only [freeKernel, Fin.prod_univ_two] at he
  exact congrArg ENNReal.ofReal he

end Critical2DKPZ.DeltaBose
