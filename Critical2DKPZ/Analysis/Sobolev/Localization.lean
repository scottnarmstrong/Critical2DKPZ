/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Localizers
public import Critical2DKPZ.Analysis.Sobolev.Seminorm
public import Mathlib.Analysis.Distribution.Support
import Mathlib.Tactic.Ring

/-! Multiplication by a smooth compactly supported function defines a continuous linear operator on distributions, with support contained in that of the multiplier. -/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Critical2DKPZ

/-- The pointwise product of two smooth compactly supported test functions. -/
def testFnMul (χ φ : TestFn) : TestFn :=
  TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) χ.contDiff φ

/-- The product of two test functions evaluates to the product of their values. -/
@[simp] theorem testFnMul_apply (χ φ : TestFn) (x : Plane) : testFnMul χ φ x = χ x * φ x :=
  mul_comm _ _

/-- Multiplication of test functions is commutative. -/
theorem testFnMul_comm (χ φ : TestFn) : testFnMul χ φ = testFnMul φ χ := by
  ext x
  simp only [testFnMul_apply, mul_comm]


/-- Multiplication of a real distribution by a smooth compact localizer. -/
def localizeDistr (χ : TestFn) : Distr →L[ℝ] Distr :=
  (TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) χ.contDiff).precompCompactConvergenceCLM ℝ

/-- A localized distribution acts by multiplying its test function by the localizer. -/
@[simp] theorem localizeDistr_apply (χ : TestFn) (T : Distr) (φ : TestFn) :
    localizeDistr χ T φ = T (testFnMul χ φ) := rfl



/-- Fourier localization composes exactly with pointwise multiplication of localizers. -/
theorem localizedFourier_localizeDistr (χ φ : TestFn) (T : Distr) (ξ : Plane) :
    localizedFourier (localizeDistr χ T) φ ξ = localizedFourier T (testFnMul χ φ) ξ := by
  have hc : testFnMul χ (φ.mulCos ξ) = (testFnMul χ φ).mulCos ξ := by
    ext x
    simp only [testFnMul_apply, TestFn.mulCos_apply, mul_assoc]
  have hs : testFnMul χ (φ.mulSin ξ) = (testFnMul χ φ).mulSin ξ := by
    ext x
    simp only [testFnMul_apply, TestFn.mulSin_apply, mul_assoc]
  simp only [localizedFourier, localizeDistr_apply, hc, hs]

/-- The countable localizers eventually act identically on every fixed test function. -/
theorem exists_testFnMul_localizer_eq (φ : TestFn) :
    ∃ N : ℕ, ∀ n ≥ N, testFnMul (localizer n) φ = φ := by
  obtain ⟨N, hN⟩ := exists_localizer_mul_testFn_eq φ
  refine ⟨N, fun n hn => ?_⟩
  ext x
  simpa only [testFnMul_apply] using hN n hn x

end Critical2DKPZ

end
