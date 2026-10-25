/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SoftTail
import Mathlib.MeasureTheory.Function.L2Space

/-! # Integrability of the square-tail moment -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The square of a real value restricted to a strict norm tail. -/
def squareTail (q x : ℝ) : ℝ := x ^ 2 * {u : ℝ | q < |u|}.indicator 1 x

/-- Square tails are nonnegative. -/
theorem squareTail_nonneg (q x : ℝ) : 0 ≤ squareTail q x := by
  classical
  by_cases hx : x ∈ {u : ℝ | q < |u|}
  · rw [squareTail, indicator_of_mem hx, Pi.one_apply, mul_one]
    exact sq_nonneg x
  · rw [squareTail, indicator_of_notMem hx, mul_zero]

/-- The square tail is bounded by the full square. -/
theorem squareTail_le_sq (q x : ℝ) : squareTail q x ≤ x ^ 2 := by
  classical
  by_cases hx : x ∈ {u : ℝ | q < |u|}
  · rw [squareTail, indicator_of_mem hx, Pi.one_apply, mul_one]
  · rw [squareTail, indicator_of_notMem hx, mul_zero]
    exact sq_nonneg x

/-- The strict cutoff is a Borel function. -/
theorem measurable_squareTail (q : ℝ) : Measurable (squareTail q) := by
  have hs : MeasurableSet {u : ℝ | q < |u|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  exact (measurable_id.pow_const 2).mul (measurable_const.indicator hs)

/-- A square-integrable random variable has integrable strict square tails. -/
theorem integrable_squareTail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℝ} (hf : Measurable f) (hf₂ : Integrable (fun ω => f ω ^ 2) P) (q : ℝ) :
    Integrable (fun ω => squareTail q (f ω)) P := by
  apply hf₂.mono' ((measurable_squareTail q).comp hf).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    change ‖squareTail q (f ω)‖ ≤ f ω ^ 2
    rw [Real.norm_of_nonneg (squareTail_nonneg q (f ω))]
    exact squareTail_le_sq q (f ω)

/-- The continuous tail is controlled by its integrable square-tail moment. -/
theorem integral_softTail_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℝ} (hf : Measurable f) (hf₂ : Integrable (fun ω => f ω ^ 2) P)
    {t : ℝ} (ht : 0 < t) (hh : Integrable (fun ω => softTail t (f ω)) P) :
    (∫ ω, softTail t (f ω) ∂P) ≤ (4 / t) * ∫ ω, squareTail (t / 2) (f ω) ∂P := by
  have hs := integrable_squareTail hf hf₂ (t / 2)
  have hle := integral_mono hh (hs.const_mul (4 / t))
    (fun ω => softTail_le_sq_tail ht (f ω))
  rwa [integral_const_mul] at hle

end Critical2DKPZ.Extensions.ScaleLimit

end
