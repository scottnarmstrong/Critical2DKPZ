/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.AssociatedLog
public import Critical2DKPZ.Extensions.ScaleLimit.NormalizedArrayCLT
import Mathlib.Analysis.Real.Sqrt

/-! # The fourth-moment Lyapunov summation step for the CCR array -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- A fourth moment gives the absolute third moment needed by the library CLT. -/
theorem integral_abs_cube_le_second_fourth {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 4 P) :
    (∫ ω, |X ω| ^ 3 ∂P) ≤ Real.sqrt (∫ ω, X ω ^ 2 ∂P) * Real.sqrt (∫ ω, X ω ^ 4 ∂P) := by
  have hX2 : MemLp X 2 P := hX.mono_exponent (by norm_num)
  have hsq : MemLp (fun ω => X ω ^ 2) 2 P := by
    apply (memLp_two_iff_integrable_sq (hX.aestronglyMeasurable.pow 2)).mpr
    have hi := hX.integrable_norm_pow'
    apply hi.congr
    filter_upwards [] with ω
    change ‖X ω‖ ^ 4 = (X ω ^ 2) ^ 2
    rw [Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq_abs]
  have hh := abs_integral_mul_le_sqrt_sq P hX2.abs hsq
  change |∫ ω, |X ω| * X ω ^ 2 ∂P| ≤ Real.sqrt (∫ ω, |X ω| ^ 2 ∂P) *
    Real.sqrt (∫ ω, (X ω ^ 2) ^ 2 ∂P) at hh
  have he (ω : Ω) : |X ω| * X ω ^ 2 = |X ω| ^ 3 := by
    rw [← sq_abs (X ω)]
    ring
  have hnonneg : 0 ≤ ∫ ω, |X ω| ^ 3 ∂P := integral_nonneg fun ω => pow_nonneg (abs_nonneg _) 3
  simpa only [he, sq_abs, ← pow_mul, show (2 * 2 : ℕ) = 4 by norm_num,
    abs_of_nonneg hnonneg] using hh


end Critical2DKPZ.Extensions.GffTangent
