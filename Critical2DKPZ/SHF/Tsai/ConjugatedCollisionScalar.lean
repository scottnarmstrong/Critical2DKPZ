/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedFormTransport
public import Critical2DKPZ.SHF.Tsai.ConjugatedCollisionLp
import Mathlib.Tactic

/-! # Global scalar-density bounds for conjugated collision blocks -/

@[expose] public section

open MeasureTheory Critical2DKPZ.DeltaBose Critical2DKPZ.SHF.Flow
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Conjugation costs only Gaussian exponential growth in the collision
block's exact scalar-density bound. This estimate holds at every positive time. -/
theorem weightedFormBound_collision_conj_scalar {n : ℕ} (α : CollisionPair n) (θ : ℝ)
    {p a t : ℝ} (hp : 1 < p) (ha : 0 ≤ a) (ht : 0 < t) :
    WeightedFormBound volume volume (fun y => -(a * fusedOneNorm α y))
      (fun z => a * fusedOneNorm α z) p (p / (p - 1))
      (fun y z => ENNReal.ofReal (collisionKernel α θ t y z))
      (ENNReal.ofReal (weightGrowth n a t * (4 * Real.pi * scalarDensity θ t))) := by
  have ht2 : 0 < 2 * t := by positivity
  have hj : 0 < scalarDensity θ t := scalarDensity_pos θ ht
  have hj2 : 0 < scalarDensity θ (2 * t) := scalarDensity_pos θ ht2
  let d : ℝ := weightGrowth n a t * (scalarDensity θ t / scalarDensity θ (2 * t))
  have hd : 0 < d := mul_pos (weightGrowth_pos n a t) (div_pos hj hj2)
  have hbase := weightedFormBound_collisionKernel_lp α θ ht2 hp
  have hscaled := weightedFormBound_const_mul (d := ENNReal.ofReal d) ENNReal.ofReal_ne_top hbase
  have hpoint (y z : FusedConfiguration α) :
      expConjugate (fun y => a * fusedOneNorm α y) (fun z => a * fusedOneNorm α z)
        (fun y z => ENNReal.ofReal (collisionKernel α θ t y z)) y z ≤
      ENNReal.ofReal d * ENNReal.ofReal (collisionKernel α θ (2 * t) y z) := by
    rw [expConjugate_ofReal, ← ENNReal.ofReal_mul hd.le]
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_sub, d] using collisionKernel_mul_exp_weight_le α θ ha ht y z
  have hbar := hscaled.mono hpoint le_rfl
  have hw : Measurable (fun y : FusedConfiguration α => a * fusedOneNorm α y) :=
    measurable_const.mul (measurable_fusedOneNorm α)
  have hK : Measurable (Function.uncurry
      (fun y z : FusedConfiguration α => ENNReal.ofReal (collisionKernel α θ t y z))) :=
    (Measurable.comp
      (g := fun q : (ℝ × ℝ) × FusedConfiguration α × FusedConfiguration α =>
        collisionKernel α q.1.1 q.1.2 q.2.1 q.2.2)
      (f := fun q : FusedConfiguration α × FusedConfiguration α => ((θ, t), q))
      (measurable_collisionKernel α) (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hform := WeightedFormBound.of_expConjugate hw hw hK hbar
  have hcoef : ENNReal.ofReal d * ENNReal.ofReal (4 * Real.pi * scalarDensity θ (2 * t)) =
      ENNReal.ofReal (weightGrowth n a t * (4 * Real.pi * scalarDensity θ t)) := by
    rw [← ENNReal.ofReal_mul hd.le]
    congr 1
    dsimp [d]
    field_simp [hj2.ne']
  rw [hcoef] at hform
  exact hform

end Critical2DKPZ.SHF.Tsai

end
