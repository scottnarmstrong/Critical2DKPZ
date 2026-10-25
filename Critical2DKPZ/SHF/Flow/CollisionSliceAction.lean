/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.SingletonSymmetry
public import Critical2DKPZ.SHF.Flow.SingleCollisionAction
public import Critical2DKPZ.SHF.Flow.KernelActionMixture

/-! # Collision-slice kernels and three-block actions -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- Joint measurability of the canonical collision slice under substitutions. -/
theorem measurable_collisionSlice_comp {n : ℕ} (α : CollisionPair n)
    {X : Type*} [MeasurableSpace X] {θ h r u : X → ℝ} {x y : X → Configuration n}
    (hθ : Measurable θ) (hh : Measurable h) (hr : Measurable r) (hu : Measurable u)
    (hx : Measurable x) (hy : Measurable y) :
    Measurable (fun p => collisionSlice α (θ p) (h p) (x p) (y p) (r p) (u p)) := by
  unfold collisionSlice
  apply Measurable.lintegral_prod_right
  apply Measurable.lintegral_prod_right
  let R := (X × FusedConfiguration α) × FusedConfiguration α
  have hb : Measurable (fun p : R => p.1.1) := measurable_fst.fst
  have hz : Measurable (fun p : R => p.1.2) := measurable_fst.snd
  have hw : Measurable (fun p : R => p.2) := measurable_snd
  have hi := ((measurable_incomingKernel α).comp
    ((hr.comp hb).prodMk (hz.prodMk (hx.comp hb)))).ennreal_ofReal
  have hc := ((measurable_collisionKernel α).comp
    (((hθ.comp hb).prodMk ((hu.comp hb).sub (hr.comp hb))).prodMk (hz.prodMk hw))).ennreal_ofReal
  have ho := ((measurable_freeKernel n).comp
    (((hh.comp hb).sub (hu.comp hb)).prodMk
      (((measurable_collisionEmbedding α).comp hw).prodMk (hy.comp hb)))).ennreal_ofReal
  exact (hi.mul hc).mul ho

/-- Integrating the collision-slice kernel against a nonnegative measurable test gives its three-block action. -/
theorem collisionSlice_action_eq {n : ℕ} (α : CollisionPair n) (θ v r u : ℝ)
    {f : Configuration n → ℝ≥0∞} (hf : Measurable f) (x : Configuration n) :
    (∫⁻ y : Configuration n, collisionSlice α θ v x y r u * f y) =
      singleCollisionAction α θ r (u - r) (v - u) f x := by
  let F : FusedConfiguration α → FusedConfiguration α → Configuration n → ℝ≥0∞ :=
    fun z w y => ENNReal.ofReal (incomingKernel α r z x) *
      ENNReal.ofReal (collisionKernel α θ (u - r) z w) *
      ENNReal.ofReal (incomingKernel α (v - u) w y)
  have hm : Measurable (fun p : (FusedConfiguration α × Configuration n) × FusedConfiguration α =>
      F p.1.1 p.2 p.1.2) := by
    have hpi : Measurable (fun p : (FusedConfiguration α × Configuration n) × FusedConfiguration α =>
        (r, p.1.1, x)) := measurable_const.prodMk (measurable_fst.fst.prodMk measurable_const)
    have hi := ((measurable_incomingKernel α).comp hpi).ennreal_ofReal
    have hc := ((measurable_collisionKernel α).comp
      (show Measurable (fun p : (FusedConfiguration α × Configuration n) × FusedConfiguration α =>
        ((θ, u - r), p.1.1, p.2)) from
          measurable_const.prodMk (measurable_fst.fst.prodMk measurable_snd))).ennreal_ofReal
    have hpo : Measurable (fun p : (FusedConfiguration α × Configuration n) × FusedConfiguration α =>
        (v - u, p.2, p.1.2)) := measurable_const.prodMk (measurable_snd.prodMk measurable_fst.snd)
    have ho := ((measurable_incomingKernel α).comp hpo).ennreal_ofReal
    exact (hi.mul hc).mul ho
  have houter : Measurable (fun p : FusedConfiguration α × Configuration n =>
      ∫⁻ w : FusedConfiguration α, F p.1 w p.2) := hm.lintegral_prod_right'
  have hinner (z : FusedConfiguration α) : Measurable
      (fun p : FusedConfiguration α × Configuration n => F z p.1 p.2) := by
    have hp : Measurable (fun p : FusedConfiguration α × Configuration n => ((z, p.2), p.1)) :=
      (measurable_const.prodMk measurable_snd).prodMk measurable_fst
    exact Measurable.comp (g := fun p : (FusedConfiguration α × Configuration n) × FusedConfiguration α =>
      F p.1.1 p.2 p.1.2) (f := fun p : FusedConfiguration α × Configuration n => ((z, p.2), p.1)) hm hp
  have he : (fun y => collisionSlice α θ v x y r u) =
      fun y => ∫⁻ z : FusedConfiguration α, ∫⁻ w : FusedConfiguration α, F z w y := by
    funext y
    unfold collisionSlice F
    simp only [incomingKernel, freeKernel_symm n (v - u) y]
  have hep (y : Configuration n) := congrFun he y
  simp_rw [hep]
  rw [lintegral_kernelMixture_action volume volume houter hf]
  unfold singleCollisionAction
  apply lintegral_congr
  intro z
  rw [lintegral_kernelMixture_action volume volume (hinner z) hf]
  calc
    _ = ∫⁻ w : FusedConfiguration α,
        ENNReal.ofReal (incomingKernel α r z x) *
          (ENNReal.ofReal (collisionKernel α θ (u - r) z w) *
            ∫⁻ y : Configuration n, ENNReal.ofReal (incomingKernel α (v - u) w y) * f y) := by
      apply lintegral_congr
      intro w
      simp only [F, mul_assoc]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end Critical2DKPZ.SHF.Flow

end
