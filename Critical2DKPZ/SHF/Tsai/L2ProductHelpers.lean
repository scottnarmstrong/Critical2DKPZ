/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! # Scalar `L²` fibers on product measure spaces

The squared seminorm identity is a specialization of Mathlib's general power
formula. Tonelli identifies the squared norm with the integral of the fiber
squared norms, and yields `L²` membership of almost every fiber.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Mathlib's power formula at exponent two, written with natural squares. -/
theorem sq_eLpNorm_two_eq_lintegral_enorm {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {F : X → ℝ} (hF : AEStronglyMeasurable F ν) :
    (eLpNorm F 2 ν) ^ (2 : ℕ) = ∫⁻ x, ‖F x‖ₑ ^ (2 : ℕ) ∂ν := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hF
  norm_num at h
  exact h

/-- Tonelli expresses the squared product-space norm through its left-coordinate fibers. -/
theorem lintegral_fiber_eLpNorm_sq_eq {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) (μ : Measure Y) [SigmaFinite ν] [SigmaFinite μ]
    {F : X × Y → ℝ} (hF : Measurable F) :
    (∫⁻ y, (eLpNorm (fun x => F (x, y)) 2 ν) ^ (2 : ℕ) ∂μ) =
      (eLpNorm F 2 (ν.prod μ)) ^ (2 : ℕ) := by
  rw [sq_eLpNorm_two_eq_lintegral_enorm hF.aestronglyMeasurable,
    lintegral_prod_symm _ (hF.enorm.pow_const (2 : ℕ)).aemeasurable]
  apply lintegral_congr
  intro y
  exact sq_eLpNorm_two_eq_lintegral_enorm
    (hF.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable

/-- Almost every fiber of a measurable scalar `L²` function belongs to `L²`. -/
theorem ae_memLp_prod_left {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) (μ : Measure Y) [SigmaFinite ν] [SigmaFinite μ]
    {F : X × Y → ℝ} (hFm : Measurable F) (hF : MemLp F 2 (ν.prod μ)) :
    ∀ᵐ y ∂μ, MemLp (fun x => F (x, y)) 2 ν := by
  have hm : Measurable (fun y => ∫⁻ x, ‖F (x, y)‖ₑ ^ (2 : ℕ) ∂ν) :=
    ((hFm.enorm.pow_const (2 : ℕ)).comp measurable_swap).lintegral_prod_right'
  have hfinite : (∫⁻ y, ∫⁻ x, ‖F (x, y)‖ₑ ^ (2 : ℕ) ∂ν ∂μ) ≠ ⊤ := by
    rw [← lintegral_prod_symm _ (hFm.enorm.pow_const (2 : ℕ)).aemeasurable,
      ← sq_eLpNorm_two_eq_lintegral_enorm hFm.aestronglyMeasurable]
    exact ENNReal.pow_ne_top hF.eLpNorm_ne_top
  filter_upwards [ae_lt_top hm hfinite] with y hy
  change eLpNorm (fun x => F (x, y)) 2 ν < ⊤
  have hslice : Measurable (fun x => F (x, y)) :=
    hFm.comp (measurable_id.prodMk measurable_const)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hslice.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hy.ne

end Critical2DKPZ.SHF.Tsai

end
