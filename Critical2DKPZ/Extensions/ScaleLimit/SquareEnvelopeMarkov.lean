/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Markov bounds for the remainder square envelopes -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- An integrable nonnegative square envelope controls the probability of
crossing its square threshold, without a measurability assumption on a supremum. -/
theorem measure_square_envelope_lt_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZi : Integrable Z P)
    (hZ0 : ∀ ω, 0 ≤ Z ω) {Λ : ℝ} (hΛ : 0 < Λ) :
    P {ω | Λ ^ 2 < Z ω} ≤ ENNReal.ofReal ((∫ ω, Z ω ∂P) / Λ ^ 2) := by
  have hmark := mul_meas_ge_le_integral_of_nonneg (ae_of_all P hZ0) hZi (Λ ^ 2)
  have hp : (P {ω | Λ ^ 2 ≤ Z ω}).toReal ≤ (∫ ω, Z ω ∂P) / Λ ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hΛ)).mpr
    simpa only [Measure.real, mul_comm] using hmark
  calc
    _ ≤ P {ω | Λ ^ 2 ≤ Z ω} := measure_mono (fun ω (h : Λ ^ 2 < Z ω) => h.le)
    _ = ENNReal.ofReal (P {ω | Λ ^ 2 ≤ Z ω}).toReal :=
      (ENNReal.ofReal_toReal (measure_ne_top P _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hp

/-- The threshold used in the three-term window decomposition gives the
factor 36 and consumes the normalized envelope budget directly. -/
theorem measure_window_square_envelope_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZi : Integrable Z P)
    (hZ0 : ∀ ω, 0 ≤ Z ω) {η L K : ℝ} (hη : 0 < η) (hL : 0 < L)
    (hbudget : L⁻¹ * (∫ ω, Z ω ∂P) ≤ K) :
    P {ω | (η * Real.sqrt L / 6) ^ 2 < Z ω} ≤ ENNReal.ofReal (36 * K / η ^ 2) := by
  have hΛ : 0 < η * Real.sqrt L / 6 := by positivity
  apply (measure_square_envelope_lt_le P Z hZi hZ0 hΛ).trans
  apply ENNReal.ofReal_le_ofReal
  have hsq : (η * Real.sqrt L / 6) ^ 2 = η ^ 2 * L / 36 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hL.le]
    norm_num
  calc
    _ = (36 / η ^ 2) * (L⁻¹ * (∫ ω, Z ω ∂P)) := by rw [hsq]; field_simp
    _ ≤ (36 / η ^ 2) * K := mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = _ := by ring

end Critical2DKPZ.Extensions.ScaleLimit
