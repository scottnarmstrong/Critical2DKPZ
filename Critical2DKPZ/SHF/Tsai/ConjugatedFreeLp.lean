/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedLpForm
public import Critical2DKPZ.SHF.Tsai.Tech
public import Critical2DKPZ.SHF.DeltaBose.FreeMass
import Mathlib.Tactic

/-! # Positive free heat flow on every finite `Lᵖ` space -/

@[expose] public section

open MeasureTheory Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- The free configuration heat flow is a contraction on `Lᵖ`, by its
canonical row and column mass-one identities and the positive Schur test. -/
theorem weightedFormBound_freeKernel_lp (n : ℕ) {p t : ℝ} (hp : 1 < p) (ht : 0 < t) :
    WeightedFormBound volume volume (fun _ : Configuration n => 0) (fun _ : Configuration n => 0)
      p (p / (p - 1)) (fun x y => ENNReal.ofReal (freeKernel n t x y)) 1 := by
  have hK : Measurable (Function.uncurry
      (fun x y : Configuration n => ENNReal.ofReal (freeKernel n t x y))) :=
    (Measurable.comp
      (g := fun q : ℝ × Configuration n × Configuration n => freeKernel n q.1 q.2.1 q.2.2)
      (f := fun q : Configuration n × Configuration n => (t, q))
      (measurable_freeKernel n) (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hrow (x : Configuration n) : (∫⁻ y, ENNReal.ofReal (freeKernel n t x y)) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_freeKernel_right n ht x)
      (Filter.Eventually.of_forall fun y => (freeKernel_pos n ht x y).le),
      integral_freeKernel_right n ht x, ENNReal.ofReal_one]
  have hcol (y : Configuration n) : (∫⁻ x, ENNReal.ofReal (freeKernel n t x y)) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_freeKernel_left n ht y)
      (Filter.Eventually.of_forall fun x => (freeKernel_pos n ht x y).le),
      integral_freeKernel_left n ht y, ENNReal.ofReal_one]
  have hpq : p.HolderConjugate (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl
  apply WeightedFormBound.of_rpow_action_bound hp hK
  intro f hf
  have h := lintegral_kernel_lp_schur hK hpq (fun x => (hrow x).le) (fun y => (hcol y).le) hf
  simpa only [ENNReal.one_rpow, one_mul] using h

end Critical2DKPZ.SHF.Tsai

end
