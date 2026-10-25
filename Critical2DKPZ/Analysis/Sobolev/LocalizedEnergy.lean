/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Localization

/-! The localized negative Sobolev energy of a distribution multiplied by a smooth cutoff equals its energy at the product localizer. -/

@[expose] public section

open MeasureTheory Set

namespace Critical2DKPZ.Analysis.Sobolev

/-- Multiplication of a distribution by a smooth cutoff transfers to multiplication of the localizer in its negative Sobolev energy. -/
theorem localNegSobolevSq_localizeDistr (a : ℝ) (χ φ : TestFn) (T : Distr) :
    localNegSobolevSq a (localizeDistr χ T) φ =
      localNegSobolevSq a T (testFnMul χ φ) := by
  have hFourier (ξ : Plane) := localizedFourier_localizeDistr χ φ T ξ
  have hsum (ξ : Plane) :
      (localizeDistr χ T (φ.mulCos ξ)) ^ 2 + (localizeDistr χ T (φ.mulSin ξ)) ^ 2 =
        (T ((testFnMul χ φ).mulCos ξ)) ^ 2 + (T ((testFnMul χ φ).mulSin ξ)) ^ 2 := by
    have hnorm := congrArg norm (hFourier ξ)
    have hnorm2 := congrArg (fun z : ℝ => z ^ 2) hnorm
    rw [norm_localizedFourier_sq, norm_localizedFourier_sq] at hnorm2
    exact hnorm2
  unfold localNegSobolevSq
  congr 1
  apply lintegral_congr
  intro ξ
  rw [hsum ξ]

/-- Multiplication by a cutoff equal to one on a test function's support leaves that test function
unchanged. -/
theorem testFnMul_eq_self_of_eq_one_on_tsupport (χ ψ : TestFn)
    (hψ : ∀ x ∈ tsupport χ, ψ x = 1) :
    testFnMul ψ χ = χ := by
  ext x
  by_cases hx : x ∈ tsupport χ
  · rw [testFnMul_apply, hψ x hx, one_mul]
  · rw [testFnMul_apply, image_eq_zero_of_notMem_tsupport hx, mul_zero]

/-- Multiplication of a distribution by a cutoff equal to one on the test support preserves its local negative Sobolev energy at that test. -/
theorem localNegSobolevSq_eq_localizeDistr_of_eq_one_on_tsupport
    (a : ℝ) (T : Distr) (χ ψ : TestFn) (hψ : ∀ x ∈ tsupport χ, ψ x = 1) :
    localNegSobolevSq a (localizeDistr ψ T) χ = localNegSobolevSq a T χ := by
  rw [localNegSobolevSq_localizeDistr, testFnMul_eq_self_of_eq_one_on_tsupport χ ψ hψ]

end Critical2DKPZ.Analysis.Sobolev

end
