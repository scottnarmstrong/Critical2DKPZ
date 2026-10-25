/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.ProfileCovariance
import Mathlib.Tactic

/-! # Second moments of differences of finite polymer profiles -/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal
open Critical2DKPZ.Polymer

namespace Critical2DKPZ.Smoothing

/-- An integrable square controls the `L²` seminorm by the square root of its integral. -/
theorem eLpNorm_le_of_integral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {F : Ω → ℝ} (hF : MemLp F 2 μ) {B : ℝ}
    (hbound : (∫ ω, F ω ^ 2 ∂μ) ≤ B) :
    eLpNorm F 2 μ ≤ ENNReal.ofReal (Real.sqrt B) := by
  have hnormPow :
      (∫ ω, ‖F ω‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂μ) ^
          (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ = (eLpNorm F 2 μ).toReal := by
    rw [hF.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    have hnonneg : 0 ≤
        (∫ ω, ‖F ω‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂μ) ^
          (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ := by positivity
    exact (ENNReal.toReal_ofReal hnonneg).symm
  have hsq :
      ∫ ω, ‖F ω‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂μ =
        ∫ ω, F ω ^ 2 ∂μ := by
    simp [ENNReal.toReal_ofNat, Real.norm_eq_abs, sq_abs]
  have htoReal : (eLpNorm F 2 μ).toReal = Real.sqrt (∫ ω, F ω ^ 2 ∂μ) := by
    calc
      _ = (∫ ω, ‖F ω‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂μ) ^
            (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ := hnormPow.symm
      _ = Real.sqrt (∫ ω, F ω ^ 2 ∂μ) := by
        rw [hsq, Real.sqrt_eq_rpow]
        congr 1
        norm_num [ENNReal.toReal_ofNat]
  calc
    eLpNorm F 2 μ = ENNReal.ofReal (eLpNorm F 2 μ).toReal :=
      (ENNReal.ofReal_toReal hF.eLpNorm_ne_top).symm
    _ = ENNReal.ofReal (Real.sqrt (∫ ω, F ω ^ 2 ∂μ)) := by rw [htoReal]
    _ ≤ ENNReal.ofReal (Real.sqrt B) := ENNReal.ofReal_le_ofReal
      (Real.sqrt_le_sqrt hbound)


end Critical2DKPZ.Smoothing

end
