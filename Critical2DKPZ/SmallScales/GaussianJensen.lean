/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SmallScales.Basic
public import Critical2DKPZ.Analysis.Heat.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.L2Space

/-! # The Gaussian Jensen comparison

A heat-kernel ratio is exponential affine after removal of a quadratic term; averaging
at the test-function barycentre cancels the affine contribution to Jensen’s lower bound. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Critical2DKPZ.SmallScales

/-- The Gaussian ratio identity used to tilt the heat-start measure. -/
theorem heatKernel_ratio_eq_exp {δ : ℝ} (hδ : 0 < δ) (b y u : Plane) :
    heatKernel δ (u - y) / heatKernel δ (u - b) =
      Real.exp (-‖y - b‖ ^ 2 / (2 * δ) + inner ℝ (y - b) (u - b) / δ) := by
  have hn : ‖u - y‖ ^ 2 = ‖u - b‖ ^ 2 + ‖y - b‖ ^ 2 -
      2 * inner ℝ (y - b) (u - b) := by
    rw [show u - y = (u - b) - (y - b) by abel, norm_sub_sq_real]
    rw [real_inner_comm]
    ring
  rw [heatKernel, heatKernel, mul_div_mul_left _ _
    (ne_of_gt (inv_pos.mpr (by positivity : 0 < 2 * Real.pi * δ))), ← Real.exp_sub, hn]
  congr 1
  field_simp
  ring

/-- A log Laplace transform dominates its first moment. -/
theorem integral_le_log_integral_exp {α : Type*} [MeasurableSpace α]
    (Q : Measure α) [IsProbabilityMeasure Q] (f : α → ℝ)
    (hf : Integrable f Q) (hexp : Integrable (fun u => Real.exp (f u)) Q) :
    (∫ u, f u ∂Q) ≤ Real.log (∫ u, Real.exp (f u) ∂Q) := by
  have h := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hf hexp
  exact (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) h)).2 h

/-- The logarithm of a Gaussian kernel ratio averaged against a probability measure. -/
def heatRatioLog (Q : Measure Plane) (δ : ℝ) (b y : Plane) : ℝ :=
  Real.log (∫ u, heatKernel δ (u - y) / heatKernel δ (u - b) ∂Q)

/-- The pointwise Gaussian Jensen lower bound. -/
theorem heatRatioLog_lower_bound (Q : Measure Plane) [IsProbabilityMeasure Q]
    {δ : ℝ} (hδ : 0 < δ) (b y : Plane) (hQ : Integrable (fun u : Plane => u) Q)
    (hexp : Integrable (fun u => Real.exp (inner ℝ (y - b) (u - b) / δ)) Q) :
    -‖y - b‖ ^ 2 / (2 * δ) + inner ℝ (y - b) ((∫ u, u ∂Q) - b) / δ ≤
      heatRatioLog Q δ b y := by
  have hlin : Integrable (fun u => inner ℝ (y - b) (u - b) / δ) Q :=
    ((hQ.sub (integrable_const b)).const_inner (y - b)).div_const δ
  have hj := integral_le_log_integral_exp Q _ hlin hexp
  have hint : (∫ u, inner ℝ (y - b) (u - b) / δ ∂Q) =
      inner ℝ (y - b) ((∫ u, u ∂Q) - b) / δ := by
    rw [integral_div, integral_inner (f := fun u : Plane => u - b) (hQ.sub (integrable_const b)),
      integral_sub hQ (integrable_const b), integral_const]
    simp
  rw [hint] at hj
  have hepos : 0 < ∫ u, Real.exp (inner ℝ (y - b) (u - b) / δ) ∂Q := by
    exact integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le) hexp |>.2
      (by simp [Function.support, ne_of_gt (Real.exp_pos _)])
  unfold heatRatioLog
  simp_rw [heatKernel_ratio_eq_exp hδ, Real.exp_add]
  rw [integral_const_mul, Real.log_mul (ne_of_gt (Real.exp_pos _)) hepos.ne', Real.log_exp]
  linarith


end Critical2DKPZ.SmallScales
