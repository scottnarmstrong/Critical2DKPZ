/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BandAverageFactorization
import Mathlib.Tactic

/-! # Sharp low-frequency estimates for a spatial band average -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The finite first absolute spatial moment of a compact test. -/
def testFirstMoment (φ : TestFn) : ℝ := ∫ z : Plane, |φ z| * ‖z‖

/-- Compact support makes the first absolute moment integrable. -/
theorem integrable_testFirstMoment (φ : TestFn) :
    Integrable (fun z : Plane => |φ z| * ‖z‖) := by
  apply (φ.continuous.abs.mul continuous_norm).integrable_of_hasCompactSupport
  exact φ.hasCompactSupport.abs.mul_right

/-- Nonnegativity of the first absolute moment. -/
theorem testFirstMoment_nonneg (φ : TestFn) : 0 ≤ testFirstMoment φ :=
  integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)

/-- The averaged phase differs from the central phase by at most the radius
of its frequency ball times the spatial displacement moment. -/
theorem norm_compactPhase_average_sub_le (K : ℝ) (hK : 0 ≤ K)
    (φ : TestFn) (hφ : (∫ z, φ z) = 1) (x : Plane) (r : ℝ) :
    ‖(∫ z : Plane, φ z • compactPhase K hK (x + r • z)) - compactPhase K hK x‖ ≤
      K * |r| * testFirstMoment φ := by
  have hi := compactPhase_average_integrable K hK φ x r
  have hc : Integrable (fun z : Plane => φ z • compactPhase K hK x) :=
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).smul_const _
  have heq : (∫ z : Plane, φ z • compactPhase K hK (x + r • z)) - compactPhase K hK x =
      ∫ z : Plane, φ z • (compactPhase K hK (x + r • z) - compactPhase K hK x) := by
    simp_rw [smul_sub]
    rw [integral_sub hi hc, integral_smul_const, hφ, one_smul]
  rw [heq]
  calc
    _ ≤ ∫ z : Plane, (K * |r|) * (|φ z| * ‖z‖) := by
      apply norm_integral_le_of_norm_le ((integrable_testFirstMoment φ).const_mul _)
      filter_upwards [] with z
      rw [norm_smul, Real.norm_eq_abs]
      have hh := (compactPhase_lipschitz K hK).norm_sub_le (x + r • z) x
      change ‖compactPhase K hK (x + r • z) - compactPhase K hK x‖ ≤
        K * ‖x + r • z - x‖ at hh
      have hh' : ‖compactPhase K hK (x + r • z) - compactPhase K hK x‖ ≤
          K * (|r| * ‖z‖) := by
        simpa only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] using hh
      calc
        _ ≤ |φ z| * (K * (|r| * ‖z‖)) :=
          mul_le_mul_of_nonneg_left hh' (abs_nonneg _)
        _ = _ := by ring
    _ = _ := by rw [integral_const_mul]; rfl

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {D : Ω → Distr} {ν : Measure Plane}

/-- The low-frequency remainder has the sharp single-radius L2 bound.
No small-scale restriction on the coarse band is required. -/
theorem norm_bandLowRemainder_le (hD : StationarySpectralData P D ν)
    (φ : TestFn) (hφ : (∫ z, φ z) = 1) (x : Plane) {b : ℝ} (hb : 0 < b) (r : ℝ) :
    ‖bandLowRemainder hD b φ x r‖ ≤
      Real.sqrt (specMass ν (2 / b)) * ((2 / b) * |r| * testFirstMoment φ) := by
  let : IsLocallyFiniteMeasure ν := hD.locFin
  let : ν.HasTemperateGrowth := temperateGrowth_of_spectralData P D ν hD
  obtain ⟨S, hSn, hS⟩ := exists_band_phase_factorization P ν
    (schwartzExt hD) (schwartzExt_covariance hD) b hb
  rw [bandLowRemainder, bandAverage_eq_phase_average hD b hb S hS, hS x, ← map_sub]
  calc
    _ ≤ ‖S‖ * ‖(∫ z : Plane, φ z • compactPhase (2 / b) (by positivity) (x + r • z)) -
        compactPhase (2 / b) (by positivity) x‖ := S.le_opNorm _
    _ ≤ _ := mul_le_mul hSn (norm_compactPhase_average_sub_le _ (by positivity) φ hφ x r)
      (norm_nonneg _) (Real.sqrt_nonneg _)

end Critical2DKPZ.Extensions.ScaleLimit
