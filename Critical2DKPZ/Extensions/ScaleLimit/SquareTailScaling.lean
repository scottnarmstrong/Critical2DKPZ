/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SquareTail
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Scaling the truncated maximal second moment -/

@[expose] public section
noncomputable section
open MeasureTheory
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A positive change of scale multiplies the truncated square by its square. -/
theorem squareTail_mul_pos {a : ℝ} (ha : 0 < a) (c x : ℝ) :
    squareTail (a * c) (a * x) = a ^ 2 * squareTail c x := by
  unfold squareTail
  have heq : a * c < |a * x| ↔ c < |x| := by
    rw [abs_mul, abs_of_pos ha, mul_lt_mul_iff_right₀ ha]
  by_cases hx : c < |x|
  · have hxmem : x ∈ {u : ℝ | c < |u|} := hx
    have hm : a * x ∈ {u : ℝ | a * c < |u|} := heq.mpr hx
    simp only [Set.indicator_of_mem hm, Set.indicator_of_mem hxmem, Pi.one_apply, mul_one, mul_pow]
  · have hxmem : x ∉ {u : ℝ | c < |u|} := hx
    have hm : a * x ∉ {u : ℝ | a * c < |u|} := fun h => hx (heq.mp h)
    simp only [Set.indicator_of_notMem hm, Set.indicator_of_notMem hxmem, mul_zero]

/-- The maximal term at threshold `η sqrt(L)/6` is exactly the truncated
second moment of the normalized band variable, with coefficient `36 C/η²`. -/
theorem squareTail_window_normalization {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Ω → ℝ) (C c : ℝ) {L η : ℝ} (hL : 0 < L) (hη : 0 < η) :
    C / (η * Real.sqrt L / 6) ^ 2 * (∫ ω, squareTail (c * (η * Real.sqrt L / 6)) (F ω) ∂P) =
      (36 * C / η ^ 2) * (∫ ω, squareTail (c * η / 6) ((Real.sqrt L)⁻¹ * F ω) ∂P) := by
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hpoint (ω : Ω) : squareTail (c * (η * Real.sqrt L / 6)) (F ω) =
      L * squareTail (c * η / 6) ((Real.sqrt L)⁻¹ * F ω) := by
    have hq : c * (η * Real.sqrt L / 6) = Real.sqrt L * (c * η / 6) := by ring
    have hx : F ω = Real.sqrt L * ((Real.sqrt L)⁻¹ * F ω) := by
      rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
    conv_lhs => rw [hq, hx]
    rw [squareTail_mul_pos hs, Real.sq_sqrt hL.le]
  simp_rw [hpoint]
  rw [integral_const_mul]
  have hsq : (η * Real.sqrt L / 6) ^ 2 = η ^ 2 * L / 36 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hL.le]
    norm_num
  rw [hsq]
  field_simp

end Critical2DKPZ.Extensions.ScaleLimit
