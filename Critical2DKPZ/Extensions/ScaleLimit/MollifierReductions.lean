/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SmallScales.Basic
public import Critical2DKPZ.Definitions.TestFnCompAffine
public import Critical2DKPZ.Definitions.TestFnScale
public import Critical2DKPZ.Definitions.TestFnDilate
import Critical2DKPZ.SmallScales.TestJensen
import Critical2DKPZ.SmallScales.DeterministicComparison
import Mathlib.Tactic

/-! # Centering mollifiers and commuting their spatial and parabolic dilations -/

@[expose] public noncomputable section

open MeasureTheory

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Translating a unit-mass test by its barycentre gives a centered test. -/
theorem exists_centered_mollifier (φ : TestFn) (hφ : ∀ y, 0 ≤ φ y)
    (hφ1 : (∫ y, φ y) = 1) :
    ∃ ψ : TestFn, (∀ y, 0 ≤ ψ y) ∧ (∫ y, ψ y) = 1 ∧ SmallScales.barycentre ψ = 0 := by
  let b := SmallScales.barycentre φ
  let ψ := φ.compAffine b (LinearIsometryEquiv.refl ℝ Plane)
  have hψ (y : Plane) : ψ y = φ (b + y) := rfl
  refine ⟨ψ, (fun y => hφ (b + y)), ?_, ?_⟩
  · change (∫ y, φ (b + y)) = 1
    rw [integral_add_left_eq_self]
    exact hφ1
  · change (∫ y, φ (b + y) • y) = 0
    have h := integral_add_left_eq_self (μ := (volume : Measure Plane))
      (fun y => φ y • (y - b)) b
    have heq (y : Plane) : b + y - b = y := by abel
    simp only [heq] at h
    exact h.trans (SmallScales.integral_testFn_smul_sub_barycentre φ hφ1)

/-- Positive dilation preserves nonnegativity and total mass. -/
theorem dilate_nonneg_mass (φ : TestFn) (hφ : ∀ y, 0 ≤ φ y)
    (hφ1 : (∫ y, φ y) = 1) {c : ℝ} (hc : 0 < c) (x : Plane) :
    (∀ y, 0 ≤ φ.dilate c x y) ∧ (∫ y, φ.dilate c x y) = 1 := by
  constructor
  · intro y
    change 0 ≤ c⁻¹ ^ 2 * φ (c⁻¹ • (y - x))
    exact mul_nonneg (sq_nonneg _) (hφ _)
  · simpa only [mul_one, hφ1] using
      SmallScales.integral_testFn_dilate_mul φ hc x (fun _ => (1 : ℝ))

/-- A centered spatial dilation can be absorbed into the mollifier. -/
theorem dilate_dilate_zero (φ : TestFn) (c ε : ℝ) (x : Plane) :
    (φ.dilate c 0).dilate ε x = φ.dilate (c * ε) x := by
  ext y
  change ε⁻¹ ^ 2 * (c⁻¹ ^ 2 * φ (c⁻¹ • (ε⁻¹ • (y - x) - 0))) =
    (c * ε)⁻¹ ^ 2 * φ ((c * ε)⁻¹ • (y - x))
  have hi : c⁻¹ * ε⁻¹ = (c * ε)⁻¹ := by rw [mul_inv_rev]; ring
  simp only [sub_zero, smul_smul, hi, mul_inv_rev, mul_pow]
  ring

/-- Parabolic scaling acts on both the width and the center by its square root. -/
theorem scale_dilate (φ : TestFn) {t : ℝ} (ht : 0 < t) (ε : ℝ) (x : Plane) :
    (φ.dilate ε x).scale t = φ.dilate (Real.sqrt t * ε) (Real.sqrt t • x) := by
  ext y
  have hr : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have harg : ε⁻¹ • ((Real.sqrt t)⁻¹ • y - x) =
      (Real.sqrt t * ε)⁻¹ • (y - Real.sqrt t • x) := by
    simp only [mul_inv_rev, smul_sub, smul_smul]
    rw [mul_assoc, inv_mul_cancel₀ hr, mul_one]
  change (Real.sqrt t)⁻¹ ^ 2 * (ε⁻¹ ^ 2 * φ (ε⁻¹ • ((Real.sqrt t)⁻¹ • y - x))) =
    (Real.sqrt t * ε)⁻¹ ^ 2 * φ ((Real.sqrt t * ε)⁻¹ • (y - Real.sqrt t • x))
  rw [harg, mul_inv_rev, mul_pow]
  ring

/-- The test used in the unit-horizon scaling law returns the original test. -/
theorem scale_dilate_div_sqrt (φ : TestFn) {t : ℝ} (ht : 0 < t) (ε : ℝ) (x : Plane) :
    (φ.dilate (ε / Real.sqrt t) ((Real.sqrt t)⁻¹ • x)).scale t = φ.dilate ε x := by
  rw [scale_dilate φ ht, smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr ht).ne', one_smul]
  congr 1
  field_simp [(Real.sqrt_pos.mpr ht).ne']

end Critical2DKPZ.Extensions.ScaleLimit
