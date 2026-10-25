/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.MaximalDomination

/-! # Maximal estimates with a bounded offset -/

public section

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A pointwise norm majorant with a bounded offset gives the same maximal
majorant. No finiteness of the maximal functions is assumed. -/
theorem maximalFn_le_const_add (f h : Plane → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hbound : ∀ z, ‖f z‖ ≤ t + ‖h z‖) (y : Plane) :
    maximalFn f y ≤ ENNReal.ofReal t + maximalFn h y := by
  have hp (z : Plane) : ‖f z‖ₑ ≤ ENNReal.ofReal t + ‖h z‖ₑ := by
    calc
      ‖f z‖ₑ = ENNReal.ofReal ‖f z‖ := by rw [ofReal_norm]
      _ ≤ ENNReal.ofReal (t + ‖h z‖) := ENNReal.ofReal_le_ofReal (hbound z)
      _ = ENNReal.ofReal t + ‖h z‖ₑ := by
        rw [ENNReal.ofReal_add ht (norm_nonneg _), ofReal_norm]
  apply iSup_le
  intro r
  have hB0 : volume (ball y r.1) ≠ 0 := (measure_ball_pos volume y r.2).ne'
  have hBt : volume (ball y r.1) ≠ ⊤ := measure_ball_lt_top.ne
  have hav : ballAverage f y r ≤ ENNReal.ofReal t + ballAverage h y r := by
    calc
      ballAverage f y r ≤ (volume (ball y r.1))⁻¹ *
          ∫⁻ z in ball y r.1, (ENNReal.ofReal t + ‖h z‖ₑ) :=
        mul_le_mul' le_rfl (lintegral_mono hp)
      _ = (volume (ball y r.1))⁻¹ *
          (ENNReal.ofReal t * volume (ball y r.1) + ∫⁻ z in ball y r.1, ‖h z‖ₑ) := by
        rw [lintegral_add_left measurable_const _, setLIntegral_const]
      _ = ENNReal.ofReal t + ballAverage h y r := by
        rw [mul_add]
        apply congrArg (fun a => a + ballAverage h y r)
        calc
          (volume (ball y r.1))⁻¹ * (ENNReal.ofReal t * volume (ball y r.1)) =
              ENNReal.ofReal t * ((volume (ball y r.1))⁻¹ * volume (ball y r.1)) := by ac_rfl
          _ = ENNReal.ofReal t := by rw [ENNReal.inv_mul_cancel hB0 hBt, mul_one]
  exact hav.trans (add_le_add le_rfl (le_iSup_of_le ⟨r.1, r.2⟩ le_rfl))

/-- Smooth averages inherit a norm majorant with a bounded offset, with a
positive constant depending only on the averaging kernel. -/
theorem maximal_domination_with_offset (φ : TestFn) : ∃ A : ℝ, 0 < A ∧
    ∀ (f h : Plane → ℝ) (t : ℝ), 0 ≤ t → (∀ z, ‖f z‖ ≤ t + ‖h z‖) →
      ∀ (y : Plane) (r : ℝ), 0 < r →
        ENNReal.ofReal |∫ z, φ z * f (y + r • z)| ≤
          ENNReal.ofReal A * (ENNReal.ofReal t + maximalFn h y) := by
  obtain ⟨A, hA, hdom⟩ := maximal_domination φ
  refine ⟨A, hA, fun f h t ht hb y r hr => ?_⟩
  exact (hdom f y r hr).trans (mul_le_mul' le_rfl (maximalFn_le_const_add f h ht hb y))

end Critical2DKPZ.Extensions.ScaleLimit

end
