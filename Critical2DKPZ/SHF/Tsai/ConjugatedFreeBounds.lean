/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedFreeLp
public import Critical2DKPZ.SHF.Tsai.ConjugatedFormTransport
public import Critical2DKPZ.SHF.DeltaBose.WeightedBlockL2
import Critical2DKPZ.SHF.Tsai.ConjugatedCollisionLp
import Critical2DKPZ.SHF.Flow.WeightMeasurability
import Mathlib.Tactic

/-! # Conjugated free heat flow in every finite `Lᵖ` space -/

@[expose] public section

open MeasureTheory Critical2DKPZ.DeltaBose Critical2DKPZ.SHF.Flow
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- The conjugated free heat flow has the canonical Gaussian exponential
weight growth as its `Lᵖ` bilinear bound. -/
theorem weightedFormBound_freeKernel_conj (n : ℕ) {p a t : ℝ}
    (hp : 1 < p) (ha : 0 ≤ a) (ht : 0 < t) :
    WeightedFormBound volume volume (fun x => -(a * configurationOneNorm x))
      (fun y => a * configurationOneNorm y) p (p / (p - 1))
      (fun x y => ENNReal.ofReal (freeKernel n t x y))
      (ENNReal.ofReal (weightGrowth n a t)) := by
  have hbase := weightedFormBound_freeKernel_lp n hp (show 0 < 2 * t by positivity)
  have hscaled := weightedFormBound_const_mul
    (d := ENNReal.ofReal (weightGrowth n a t)) ENNReal.ofReal_ne_top hbase
  have hpoint (x y : Configuration n) :
      expConjugate (fun x => a * configurationOneNorm x) (fun y => a * configurationOneNorm y)
        (fun x y => ENNReal.ofReal (freeKernel n t x y)) x y ≤
        ENNReal.ofReal (weightGrowth n a t) * ENNReal.ofReal (freeKernel n (2 * t) x y) := by
    rw [expConjugate_ofReal, ← ENNReal.ofReal_mul (weightGrowth_pos n a t).le]
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_sub, weightGrowth] using freeKernel_mul_exp_weight_le n ha ht x y
  have hbar := hscaled.mono hpoint le_rfl
  have hw : Measurable (fun x : Configuration n => a * configurationOneNorm x) :=
    measurable_const.mul (Critical2DKPZ.SHF.Flow.measurable_configurationOneNorm n)
  have hK : Measurable (Function.uncurry
      (fun x y : Configuration n => ENNReal.ofReal (freeKernel n t x y))) :=
    (Measurable.comp
      (g := fun q : ℝ × Configuration n × Configuration n => freeKernel n q.1 q.2.1 q.2.2)
      (f := fun q : Configuration n × Configuration n => (t, q))
      (measurable_freeKernel n) (measurable_const.prodMk measurable_id)).ennreal_ofReal
  simpa only [mul_one] using WeightedFormBound.of_expConjugate hw hw hK hbar

end Critical2DKPZ.SHF.Tsai

end
