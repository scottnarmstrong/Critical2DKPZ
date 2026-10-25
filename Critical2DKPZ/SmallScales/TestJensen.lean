/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SmallScales.GaussianJensen
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Jensen’s inequality at the test-function barycentre

For a nonnegative unit-mass test, averaging the Gaussian logarithmic ratio cancels
the linear term and leaves a lower bound given by half the negative centered second moment. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Critical2DKPZ.SmallScales

/-- The centred first spatial moment of a test function is integrable. -/
theorem integrable_testFn_smul_sub (φ : TestFn) (b : Plane) :
    Integrable (fun y => φ y • (y - b)) := by
  exact (continuous_id.sub continuous_const).locallyIntegrable
    |>.integrable_smul_left_of_hasCompactSupport φ.continuous φ.hasCompactSupport

/-- The centred second spatial moment of a test function is integrable. -/
theorem integrable_testFn_mul_norm_sub_sq (φ : TestFn) (b : Plane) :
    Integrable (fun y => φ y * ‖y - b‖ ^ 2) := by
  simpa only [smul_eq_mul] using
    (show Continuous (fun y : Plane => ‖y - b‖ ^ 2) by fun_prop).locallyIntegrable
      |>.integrable_smul_left_of_hasCompactSupport φ.continuous φ.hasCompactSupport

/-- Centring at the test-function barycentre cancels the linear term. -/
theorem integral_testFn_smul_sub_barycentre (φ : TestFn) (hφ₁ : ∫ y, φ y = 1) :
    (∫ y, φ y • (y - barycentre φ)) = 0 := by
  have hv : Integrable (fun y : Plane => φ y • y) :=
    continuous_id.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
      φ.continuous φ.hasCompactSupport
  have hc : Integrable (fun y : Plane => φ y • barycentre φ) :=
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).smul_const _
  simp_rw [smul_sub]
  rw [integral_sub hv hc, integral_smul_const, hφ₁, one_smul]
  exact sub_self _

/-- The test average of the Gaussian logarithmic ratio is bounded below by half the negative centered second test moment. -/
theorem heatRatioLog_testFn_average_lower_bound (Q : Measure Plane) [IsProbabilityMeasure Q]
    (φ : TestFn) (hφ : ∀ y, 0 ≤ φ y) (hφ₁ : ∫ y, φ y = 1)
    (x : Plane) {ε : ℝ} (hε : 0 < ε) (hQ : Integrable (fun u : Plane => u) Q)
    (hexp : ∀ z : Plane, Integrable (fun u => Real.exp
      (inner ℝ ((x + ε • z) - (x + ε • barycentre φ))
        (u - (x + ε • barycentre φ)) / ε ^ 2)) Q)
    (hlog : Integrable (fun z => φ z *
      heatRatioLog Q (ε ^ 2) (x + ε • barycentre φ) (x + ε • z))) :
    -(∫ z, φ z * ‖z - barycentre φ‖ ^ 2) / 2 ≤
      ∫ z, φ z * heatRatioLog Q (ε ^ 2) (x + ε • barycentre φ) (x + ε • z) := by
  let c : Plane := (∫ u, u ∂Q) - (x + ε • barycentre φ)
  have hvec := integrable_testFn_smul_sub φ (barycentre φ)
  have hquad := integrable_testFn_mul_norm_sub_sq φ (barycentre φ)
  have hlin : Integrable (fun z => inner ℝ c (φ z • (z - barycentre φ)) / ε) :=
    (hvec.const_inner c).div_const ε
  have hpt : ∀ z : Plane,
      -(φ z * ‖z - barycentre φ‖ ^ 2) / 2 +
        inner ℝ c (φ z • (z - barycentre φ)) / ε ≤
          φ z * heatRatioLog Q (ε ^ 2) (x + ε • barycentre φ) (x + ε • z) := by
    intro z
    have h := mul_le_mul_of_nonneg_left
      (heatRatioLog_lower_bound Q (sq_pos_of_pos hε)
        (x + ε • barycentre φ) (x + ε • z) hQ (hexp z)) (hφ z)
    have hdiff : (x + ε • z) - (x + ε • barycentre φ) = ε • (z - barycentre φ) := by
      module
    rw [hdiff, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left] at h
    have halg : φ z * (-(ε ^ 2 * ‖z - barycentre φ‖ ^ 2) / (2 * ε ^ 2) +
        ε * inner ℝ (z - barycentre φ) c / ε ^ 2) =
        -(φ z * ‖z - barycentre φ‖ ^ 2) / 2 +
          inner ℝ c (φ z • (z - barycentre φ)) / ε := by
      rw [real_inner_smul_right, real_inner_comm c]
      field_simp
    change φ z * (-(ε ^ 2 * ‖z - barycentre φ‖ ^ 2) / (2 * ε ^ 2) +
      ε * inner ℝ (z - barycentre φ) c / ε ^ 2) ≤ _ at h
    rwa [halg] at h
  have hle := integral_mono_ae ((hquad.neg.div_const 2).add hlin) hlog
    (Filter.Eventually.of_forall hpt)
  change (∫ z, -(φ z * ‖z - barycentre φ‖ ^ 2) / 2 +
    inner ℝ c (φ z • (z - barycentre φ)) / ε) ≤ _ at hle
  rw [integral_add (f := fun z => -(φ z * ‖z - barycentre φ‖ ^ 2) / 2)
      (hquad.neg.div_const 2) hlin, integral_div, integral_neg] at hle
  have hzero : (∫ z, inner ℝ c (φ z • (z - barycentre φ)) / ε) = 0 := by
    rw [integral_div, integral_inner hvec, integral_testFn_smul_sub_barycentre φ hφ₁]
    simp
  simpa only [hzero, add_zero] using hle

end Critical2DKPZ.SmallScales
