/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SingleCollisionAction

/-! # Joint measurability of the single-collision action -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- The single-collision action is measurable under measurable time and configuration substitutions. -/
theorem measurable_singleCollisionAction_comp {n : ℕ} (α : CollisionPair n)
    {X : Type*} [MeasurableSpace X] {θ r s q : X → ℝ} {x : X → Configuration n}
    (hθ : Measurable θ) (hr : Measurable r) (hs : Measurable s) (hq : Measurable q)
    (hx : Measurable x) {f : Configuration n → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun p => singleCollisionAction α (θ p) (r p) (s p) (q p) f (x p)) := by
  let g : X × FusedConfiguration α → ℝ≥0∞ := fun p =>
    ∫⁻ y : Configuration n, ENNReal.ofReal (incomingKernel α (q p.1) p.2 y) * f y
  have hg : Measurable g := by
    apply measurable_kernelAction volume _ hf
    have hp : Measurable (fun a : (X × FusedConfiguration α) × Configuration n =>
        (q a.1.1, a.1.2, a.2)) := by fun_prop
    exact ((measurable_incomingKernel α).comp hp).ennreal_ofReal
  let h : X × FusedConfiguration α → ℝ≥0∞ := fun p =>
    ∫⁻ z' : FusedConfiguration α, ENNReal.ofReal (collisionKernel α (θ p.1) (s p.1) p.2 z') * g (p.1, z')
  have hh : Measurable h := by
    apply Measurable.lintegral_prod_right
    have hp : Measurable (fun a : (X × FusedConfiguration α) × FusedConfiguration α =>
        ((θ a.1.1, s a.1.1), a.1.2, a.2)) := by fun_prop
    exact (((measurable_collisionKernel α).comp hp).ennreal_ofReal).mul
      (hg.comp (measurable_fst.fst.prodMk measurable_snd))
  change Measurable (fun p => ∫⁻ z : FusedConfiguration α,
    ENNReal.ofReal (incomingKernel α (r p) z (x p)) * h (p, z))
  apply Measurable.lintegral_prod_right
  have hp : Measurable (fun a : X × FusedConfiguration α => (r a.1, a.2, x a.1)) := by fun_prop
  exact (((measurable_incomingKernel α).comp hp).ennreal_ofReal).mul hh

end Critical2DKPZ.SHF.Flow

end
