/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Seminorm
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-! The localized negative Sobolev energy has a real-valued square root on distributions of finite energy. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ

/-- The localized negative Sobolev seminorm of the zero distribution is zero. -/
@[simp] theorem localNegSobolevENorm_zero (a : ℝ) (χ : TestFn) :
    localNegSobolevENorm a 0 χ = 0 := by
  have he : localizedFourier 0 χ = 0 := by
    funext ξ
    simp only [localizedFourier, zero_apply, Complex.ofReal_zero, mul_zero, sub_zero, Pi.zero_apply]
  rw [localNegSobolevENorm, he, eLpNorm_zero]

/-- Negation leaves the localized negative Sobolev seminorm unchanged. -/
@[simp] theorem localNegSobolevENorm_neg (a : ℝ) (T : Distr) (χ : TestFn) :
    localNegSobolevENorm a (-T) χ = localNegSobolevENorm a T χ := by
  simpa only [neg_one_smul, abs_neg, abs_one, ENNReal.ofReal_one, one_mul] using
    localNegSobolevENorm_smul a T χ (-1)




end Critical2DKPZ

end
