/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Weighted Cauchy–Schwarz for the remainder integral -/

public section

open MeasureTheory

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Weighted Cauchy–Schwarz with explicit integrability. Applied to the derivative
of the high-frequency remainder, the weight `a / r²` avoids a window-length loss. -/
theorem integral_sq_le_weighted {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f g : α → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hq : Integrable (fun x => f x ^ 2 / g x) μ)
    (hpos : ∀ᵐ x ∂μ, 0 < g x) (hG : 0 < ∫ x, g x ∂μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ (∫ x, g x ∂μ) * (∫ x, f x ^ 2 / g x ∂μ) := by
  let c := (∫ x, f x ∂μ) / (∫ x, g x ∂μ)
  have hpoint : ∀ᵐ x ∂μ, 0 ≤ f x ^ 2 / g x - (2 * c) * f x + c ^ 2 * g x := by
    filter_upwards [hpos] with x hx
    have hh : 0 ≤ (f x - c * g x) ^ 2 / g x := div_nonneg (sq_nonneg _) hx.le
    convert hh using 1
    field_simp
    ring
  have hlinear : Integrable (fun x => (2 * c) * f x) μ := hf.const_mul _
  have hquad : Integrable (fun x => c ^ 2 * g x) μ := hg.const_mul _
  have hsub : Integrable (fun x => f x ^ 2 / g x - (2 * c) * f x) μ := hq.sub hlinear
  have hnonneg := integral_nonneg_of_ae hpoint
  rw [integral_add hsub hquad, integral_sub hq hlinear,
    integral_const_mul, integral_const_mul] at hnonneg
  have heq : (∫ x, f x ^ 2 / g x ∂μ) - (2 * c) * (∫ x, f x ∂μ) +
      c ^ 2 * (∫ x, g x ∂μ) =
      ((∫ x, g x ∂μ) * (∫ x, f x ^ 2 / g x ∂μ) - (∫ x, f x ∂μ) ^ 2) /
        (∫ x, g x ∂μ) := by
    dsimp [c]
    field_simp
    ring
  rw [heq] at hnonneg
  have hh := mul_nonneg hnonneg hG.le
  rw [div_mul_cancel₀ _ hG.ne'] at hh
  exact sub_nonneg.mp hh

end Critical2DKPZ.Extensions.ScaleLimit
