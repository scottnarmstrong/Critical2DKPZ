/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.L2ProductHelpers
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! # Averaging `L²` functions over a finite measure

The finite-measure embedding `L² → L¹` bounds each row integral. Squaring
and applying Tonelli proves that averaging preserves `L²`, and also proves
absolute integrability of almost every row.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Averaging over a finite factor preserves `L²`; the row integrals are absolutely convergent
almost everywhere, and the squared seminorm has the finite-measure bound. -/
theorem memLp_integral_finite_right {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [IsFiniteMeasure ν]
    {f : X × Y → ℝ} (hfm : Measurable f) (hf : MemLp f 2 (μ.prod ν)) :
    MemLp (fun x => ∫ y, f (x, y) ∂ν) 2 μ ∧
    (∀ᵐ x ∂μ, Integrable (fun y => f (x, y)) ν) ∧
    eLpNorm (fun x => ∫ y, f (x, y) ∂ν) 2 μ ^ (2 : ℕ) ≤
      ν Set.univ * eLpNorm f 2 (μ.prod ν) ^ (2 : ℕ) := by
  have hmrow (x : X) : AEStronglyMeasurable (fun y => f (x, y)) ν :=
    (hfm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hmavg : AEStronglyMeasurable (fun x => ∫ y, f (x, y) ∂ν) μ :=
    hfm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  have hroot : (ν Set.univ ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = ν Set.univ := by
    rw [← ENNReal.rpow_ofNat _ 2, ← ENNReal.rpow_mul]
    norm_num
  have hpoint (x : X) : ‖∫ y, f (x, y) ∂ν‖ₑ ^ (2 : ℕ) ≤
      ν Set.univ * ∫⁻ y, ‖f (x, y)‖ₑ ^ (2 : ℕ) ∂ν := by
    have hb : ‖∫ y, f (x, y) ∂ν‖ₑ ≤
        eLpNorm (fun y => f (x, y)) 2 ν * ν Set.univ ^ (1 / 2 : ℝ) := by
      refine (enorm_integral_le_lintegral_enorm _).trans ?_
      rw [← eLpNorm_one_eq_lintegral_enorm (hmrow x)]
      have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hmrow x)
      norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat] at h
      convert h using 2
    have hs := pow_le_pow_left' hb 2
    rw [mul_pow, hroot, sq_eLpNorm_two_eq_lintegral_enorm (hmrow x), mul_comm] at hs
    exact hs
  have hdouble : (∫⁻ x, ∫⁻ y, ‖f (x, y)‖ₑ ^ (2 : ℕ) ∂ν ∂μ) =
      eLpNorm f 2 (μ.prod ν) ^ (2 : ℕ) := by
    rw [sq_eLpNorm_two_eq_lintegral_enorm hfm.aestronglyMeasurable,
      lintegral_prod _ (hfm.enorm.pow_const (2 : ℕ)).aemeasurable]
  have hbound : eLpNorm (fun x => ∫ y, f (x, y) ∂ν) 2 μ ^ (2 : ℕ) ≤
      ν Set.univ * eLpNorm f 2 (μ.prod ν) ^ (2 : ℕ) := by
    rw [sq_eLpNorm_two_eq_lintegral_enorm hmavg]
    apply (lintegral_mono hpoint).trans_eq
    rw [lintegral_const_mul' _ _ (measure_ne_top ν Set.univ), hdouble]
  have hfin : eLpNorm (fun x => ∫ y, f (x, y) ∂ν) 2 μ ^ (2 : ℕ) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (measure_ne_top ν Set.univ)
      (ENNReal.pow_ne_top hf.eLpNorm_ne_top)) hbound
  have havg : MemLp (fun x => ∫ y, f (x, y) ∂ν) 2 μ :=
    ((ENNReal.pow_ne_top_iff.1 hfin).resolve_right (by norm_num : (2 : ℕ) ≠ 0)).lt_top
  refine ⟨havg, ?_, hbound⟩
  have hrowfinite : ∀ᵐ x ∂μ, (∫⁻ y, ‖f (x, y)‖ₑ ^ (2 : ℕ) ∂ν) < ⊤ := by
    apply ae_lt_top ((hfm.enorm.pow_const (2 : ℕ)).lintegral_prod_right')
    rw [hdouble]
    exact ENNReal.pow_ne_top hf.eLpNorm_ne_top
  filter_upwards [hrowfinite] with x hx
  have hrownorm : eLpNorm (fun y => f (x, y)) 2 ν ≠ ⊤ := by
    rw [← sq_eLpNorm_two_eq_lintegral_enorm (hmrow x)] at hx
    exact (ENNReal.pow_ne_top_iff.1 hx.ne).resolve_right (by norm_num : (2 : ℕ) ≠ 0)
  exact (show MemLp (fun y => f (x, y)) 2 ν from hrownorm.lt_top).integrable (by norm_num)

end Critical2DKPZ.SHF.Tsai

end
