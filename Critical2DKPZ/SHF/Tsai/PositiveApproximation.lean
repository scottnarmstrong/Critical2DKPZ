/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.Plane
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! # Increasing `L²` approximations of nonnegative tests

Truncation in value and restriction to an increasing finite-measure exhaustion give
nonnegative `L²` approximants increasing pointwise to any nonnegative measurable test.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- A bounded positive test on the canonical finite-measure exhaustion of the plane. -/
def positiveTruncation (f : Plane → ℝ≥0∞) (N : ℕ) : Plane → ℝ≥0∞ :=
  (spanningSets (volume : Measure Plane) N).indicator (fun x => min (f x) (N : ℝ≥0∞))

/-- The positive truncation of a measurable function is measurable. -/
theorem measurable_positiveTruncation {f : Plane → ℝ≥0∞} (hf : Measurable f) (N : ℕ) :
    Measurable (positiveTruncation f N) :=
  (hf.min measurable_const).indicator (measurableSet_spanningSets volume N)

/-- The `N`-th positive truncation is bounded by `N`. -/
theorem positiveTruncation_le_nat (f : Plane → ℝ≥0∞) (N : ℕ) (x : Plane) :
    positiveTruncation f N x ≤ N := by
  by_cases hx : x ∈ spanningSets (volume : Measure Plane) N
  · simpa only [positiveTruncation, Set.indicator_of_mem hx] using min_le_right (f x) (N : ℝ≥0∞)
  · simp only [positiveTruncation, Set.indicator_of_notMem hx, zero_le]

/-- Positive truncations take only finite values. -/
theorem positiveTruncation_ne_top (f : Plane → ℝ≥0∞) (N : ℕ) (x : Plane) :
    positiveTruncation f N x ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (positiveTruncation_le_nat f N x)

/-- Converting a positive truncation to a real number and back recovers it. -/
theorem ofReal_positiveTruncation_toReal (f : Plane → ℝ≥0∞) (N : ℕ) (x : Plane) :
    ENNReal.ofReal (positiveTruncation f N x).toReal = positiveTruncation f N x :=
  ENNReal.ofReal_toReal (positiveTruncation_ne_top f N x)

/-- The positive truncations increase with the truncation level. -/
theorem monotone_positiveTruncation (f : Plane → ℝ≥0∞) : Monotone (positiveTruncation f) := by
  intro N M hNM x
  by_cases hx : x ∈ spanningSets (volume : Measure Plane) N
  · have hxM := monotone_spanningSets volume hNM hx
    simp only [positiveTruncation, Set.indicator_of_mem hx, Set.indicator_of_mem hxM]
    exact min_le_min_left _ (by exact_mod_cast hNM)
  · simp only [positiveTruncation, Set.indicator_of_notMem hx, zero_le]

/-- The truncations increase to the original positive test at every point, including infinite values. -/
theorem iSup_positiveTruncation (f : Plane → ℝ≥0∞) (x : Plane) :
    (⨆ N, positiveTruncation f N x) = f x := by
  apply le_antisymm
  · apply iSup_le
    intro N
    by_cases hx : x ∈ spanningSets (volume : Measure Plane) N
    · simpa only [positiveTruncation, Set.indicator_of_mem hx] using min_le_left (f x) (N : ℝ≥0∞)
    · simp only [positiveTruncation, Set.indicator_of_notMem hx, zero_le]
  · have hcover : x ∈ ⋃ N, spanningSets (volume : Measure Plane) N := by
      rw [iUnion_spanningSets]
      exact Set.mem_univ x
    obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hcover
    have hsup : (⨆ k : ℕ, min (f x) (k : ℝ≥0∞)) = f x := by
      rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
    rw [← hsup]
    apply iSup_le
    intro k
    apply le_iSup_of_le (max N k)
    have hx := monotone_spanningSets volume (le_max_left N k) hN
    simp only [positiveTruncation, Set.indicator_of_mem hx]
    exact min_le_min_left _ (by exact_mod_cast le_max_right N k)

/-- Each real truncation is in `L²`, with no integrability premise on the untruncated test. -/
theorem memLp_positiveTruncation_toReal {f : Plane → ℝ≥0∞} (hf : Measurable f) (N : ℕ) :
    MemLp (fun x => (positiveTruncation f N x).toReal) 2 := by
  have hdom : MemLp ((spanningSets (volume : Measure Plane) N).indicator
      (fun _ : Plane => (N : ℝ))) 2 :=
    memLp_indicator_const 2 (measurableSet_spanningSets volume N) _
      (Or.inr (measure_spanningSets_lt_top volume N).ne)
  apply hdom.mono' (measurable_positiveTruncation hf N).ennreal_toReal.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  by_cases hx : x ∈ spanningSets (volume : Measure Plane) N
  · rw [Set.indicator_of_mem hx]
    have h := ENNReal.toReal_mono (by simp : (N : ℝ≥0∞) ≠ ⊤) (positiveTruncation_le_nat f N x)
    simpa only [ENNReal.toReal_natCast] using h
  · simp only [positiveTruncation, Set.indicator_of_notMem hx, ENNReal.toReal_zero, le_refl]

end Critical2DKPZ.SHF.Tsai

end
