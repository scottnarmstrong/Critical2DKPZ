/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabMollifierBounds
public import Critical2DKPZ.SHF.Flow.TwoParticleKernelActions
import Mathlib.Tactic

/-! # Zero-weight specialization of the kernel actions -/

@[expose] public noncomputable section
open MeasureTheory Critical2DKPZ.DeltaBose
open scoped ENNReal
namespace Critical2DKPZ.SHF.Flow

/-- The zero-weight mollifier action is the explicit tensor-connector integral. -/
theorem slabMollifierWeightedAction_zero_weight (e : ℝ) (w : Plane → ℝ)
    (f : Configuration 2 → ℝ≥0∞) (x : Configuration 2) :
    slabMollifierWeightedAction 0 e w f x = ∫⁻ y, slabMollifierTensorKernel 2 e w x y * f y := by
  simp only [slabMollifierWeightedAction, expConjugate, zero_mul,
    sub_self, Real.exp_zero, ENNReal.ofReal_one, mul_one]

end Critical2DKPZ.SHF.Flow
end
