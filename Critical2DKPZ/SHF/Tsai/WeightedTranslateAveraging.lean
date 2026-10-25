/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.FiniteTranslateAveraging
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Integrable signed weights in spatial translate averages

The absolute weight defines a finite measure. Dividing the signed weight by
its absolute value gives a bounded coefficient and recovers the actual
signed integral, including absolute convergence of almost every spatial row.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- A finite absolute weight yields an actual spatial `L²` average of translated kernels,
with absolute convergence of almost every row. -/
theorem memLp_weighted_translate_average {Y : Type*} [MeasurableSpace Y] (A : Measure Y)
    (a : Y → Plane) (ha : Measurable a)
    (g : Y → ℝ) (hg : Measurable g)
    (hM : (∫⁻ p, ENNReal.ofReal |g p| ∂A) < ⊤)
    (w : Plane → ℝ) (hwm : Measurable w) (hw : MemLp w 2) :
    MemLp (fun y => ∫ p, g p * w (a p - y) ∂A) 2 ∧
    (∀ᵐ y ∂volume, Integrable (fun p : Y => g p * w (a p - y)) A) := by
  let d (p : Y) := ENNReal.ofReal |g p|
  have hdm : Measurable d := by
    simpa only [d, Function.comp_def, Real.norm_eq_abs] using hg.norm.ennreal_ofReal
  have hdfin : ∀ᵐ p ∂A, d p < ⊤ := Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  let ν := A.withDensity d
  have hνfin : ν Set.univ < ⊤ := by
    dsimp only [ν]
    rw [withDensity_apply _ MeasurableSet.univ]
    simpa only [Measure.restrict_univ] using hM
  let : IsFiniteMeasure ν := ⟨hνfin⟩
  let c (p : Y) := g p / |g p|
  have hcm : Measurable c := by
    have habs : Measurable (fun p : Y => |g p|) := by
      simpa only [Function.comp_def, Real.norm_eq_abs] using hg.norm
    exact hg.div habs
  have hc (p : Y) : |c p| ≤ 1 := by
    dsimp only [c]
    by_cases h : g p = 0
    · simp only [h, abs_zero, zero_div, zero_le_one]
    · rw [abs_div, abs_abs, div_self (abs_ne_zero.mpr h)]
  have hd (p : Y) : (d p).toReal * c p = g p := by
    dsimp only [d, c]
    rw [ENNReal.toReal_ofReal (abs_nonneg _)]
    by_cases h : g p = 0
    · simp only [h, abs_zero, zero_div, mul_zero]
    · rw [mul_comm, div_mul_cancel₀ _ (abs_ne_zero.mpr h)]
  have h := memLp_integral_bounded_translates_finite ν a ha c hcm hc w hwm hw
  have heq (y : Plane) : (∫ p, c p * w (a p - y) ∂ν) = ∫ p, g p * w (a p - y) ∂A := by
    rw [integral_withDensity_eq_integral_toReal_smul hdm hdfin]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro p
    simp only [smul_eq_mul, ← mul_assoc, hd]
  have heqfun : (fun y => ∫ p, c p * w (a p - y) ∂ν) =
      fun y => ∫ p, g p * w (a p - y) ∂A := funext heq
  refine ⟨heqfun ▸ h.1, ?_⟩
  filter_upwards [h.2.1] with y hy
  have hraw := (integrable_withDensity_iff_integrable_smul' hdm hdfin).1 hy
  simpa only [smul_eq_mul, ← mul_assoc, hd] using hraw

end Critical2DKPZ.SHF.Tsai

end
