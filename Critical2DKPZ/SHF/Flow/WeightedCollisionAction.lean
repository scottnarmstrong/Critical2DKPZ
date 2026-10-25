/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.WeightedCollisionCoefficient
public import Critical2DKPZ.SHF.Flow.CollisionSliceAction

/-! # Measurable weighted actions of the canonical collision slice -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- Relate the two canonical spatial-slice presentations at arbitrary elapsed times. -/
theorem oneCollisionSpatialSlice_eq_collisionSlice {n : ℕ} (α : CollisionPair n)
    (θ r s q : ℝ) (x y : Configuration n) :
    oneCollisionSpatialSlice α θ r s q x y = collisionSlice α θ (r + s + q) x y r (r + s) := by
  rw [oneCollisionSpatialSlice_eq_integral, collisionSlice]
  rw [show r + s - r = s by ring, show r + s + q - (r + s) = q by ring]

/-- The spatial single-collision slice is measurable under measurable parameter substitutions. -/
theorem measurable_oneCollisionSpatialSlice_comp {n : ℕ} (α : CollisionPair n)
    {X : Type*} [MeasurableSpace X] {θ r s q : X → ℝ} {x y : X → Configuration n}
    (hθ : Measurable θ) (hr : Measurable r) (hs : Measurable s) (hq : Measurable q)
    (hx : Measurable x) (hy : Measurable y) :
    Measurable (fun p => oneCollisionSpatialSlice α (θ p) (r p) (s p) (q p) (x p) (y p)) := by
  simp_rw [oneCollisionSpatialSlice_eq_collisionSlice]
  exact measurable_collisionSlice_comp α hθ ((hr.add hs).add hq) hr (hr.add hs) hx hy

/-- Action of the canonical spatial slice on the exponentially weighted space. -/
def weightedCollisionSliceAction {n : ℕ} (α : CollisionPair n) (θ a r s q : ℝ)
    (f : Configuration n → ℝ≥0∞) (x : Configuration n) : ℝ≥0∞ :=
  ∫⁻ y : Configuration n,
    expConjugate (fun x => a * configurationOneNorm x) (fun y => a * configurationOneNorm y)
      (oneCollisionSpatialSlice α θ r s q) x y * f y

/-- The weighted collision-slice action is measurable under measurable parameter substitutions. -/
theorem measurable_weightedCollisionSliceAction_comp {n : ℕ} (α : CollisionPair n) (a : ℝ)
    {X : Type*} [MeasurableSpace X] {θ r s q : X → ℝ} {x : X → Configuration n}
    (hθ : Measurable θ) (hr : Measurable r) (hs : Measurable s) (hq : Measurable q)
    (hx : Measurable x) {f : Configuration n → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun p => weightedCollisionSliceAction α (θ p) a (r p) (s p) (q p) f (x p)) := by
  unfold weightedCollisionSliceAction expConjugate
  apply Measurable.lintegral_prod_right
  have hK := measurable_oneCollisionSpatialSlice_comp α (hθ.comp measurable_fst)
    (hr.comp measurable_fst) (hs.comp measurable_fst) (hq.comp measurable_fst)
    (hx.comp measurable_fst) (show Measurable (fun p : X × Configuration n => p.2) from measurable_snd)
  have hnx : Measurable (fun p : X × Configuration n => configurationOneNorm (x p.1)) :=
    (measurable_configurationOneNorm n).comp (hx.comp measurable_fst)
  have hny : Measurable (fun p : X × Configuration n => configurationOneNorm p.2) :=
    (measurable_configurationOneNorm n).comp measurable_snd
  exact (hK.mul ((measurable_const.mul hnx).sub (measurable_const.mul hny)).exp.ennreal_ofReal).mul
    (hf.comp measurable_snd)

end Critical2DKPZ.SHF.Flow

end
