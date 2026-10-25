/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.TwoParticleSemigroupDecomposition
import Mathlib.MeasureTheory.Integral.Prod

/-! # Applying the two-particle kernel decomposition -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow


/-- Joint measurability of the fixed-parameter two-particle moment kernel. -/
theorem measurable_slabMomentKernelTwo (θ h : ℝ) :
    Measurable (Function.uncurry (fun x y : Configuration 2 => momentKernel 2 θ h x y)) := by
  have hparams : Measurable (fun p : Configuration 2 × Configuration 2 => ((θ, h), p)) :=
    measurable_const.prodMk measurable_id
  have hcomp := (measurable_momentKernel 2).comp hparams
  convert hcomp using 1
  funext p
  rfl



/-- At zero exponential weight, the positive-time weighted action is the explicit moment-kernel
integral. -/
theorem twoParticleWeightedAction_zeroWeight {θ t : ℝ}
    (ht : 0 < t) (f : Configuration 2 → ℝ≥0∞) (x : Configuration 2) :
    twoParticleWeightedAction θ 0 t f x =
      ∫⁻ y : Configuration 2, momentKernel 2 θ t x y * f y := by
  rw [twoParticleWeightedAction, ite_eq_right (ne_of_gt ht)]
  simp only [expConjugate, zero_mul, sub_self, Real.exp_zero, ENNReal.ofReal_one, mul_one]

/-- At zero exponential weight, the correction action is the explicit one-collision integral. -/
theorem twoParticleCorrectionWeightedAction_zeroWeight (θ v : ℝ)
    (f : Configuration 2 → ℝ≥0∞) (x : Configuration 2) :
    twoParticleCorrectionWeightedAction θ 0 v f x =
      ∫⁻ y : Configuration 2, twoParticleCorrection θ v x y * f y := by
  simp only [twoParticleCorrectionWeightedAction, expConjugate, zero_mul,
    sub_self, Real.exp_zero, ENNReal.ofReal_one, mul_one]


end Critical2DKPZ.SHF.Flow

end
