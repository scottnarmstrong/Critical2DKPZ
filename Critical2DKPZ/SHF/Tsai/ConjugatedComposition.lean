/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.WeightedFormBound
import Mathlib.Tactic

/-! # Composition of conjugated positive kernel bounds -/

@[expose] public section

open MeasureTheory Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Composition of weighted positive kernel forms cancels the opposite middle exponential weights. Measurability of the middle weight ensures measurability of the dual test functions. -/
theorem WeightedFormBound.comp_conjugateExponent {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] {μ : Measure X} {ν : Measure Y} {ρ : Measure Z} [SFinite μ] [SigmaFinite ν]
    [SFinite ρ] {wX : X → ℝ} {wY : Y → ℝ} {wZ : Z → ℝ} {p : ℝ} (hp : 1 < p)
    (hwY : Measurable wY) {K : X → Y → ℝ≥0∞} {L : Y → Z → ℝ≥0∞} {c d : ℝ≥0∞}
    (hKm : Measurable (Function.uncurry K)) (hLm : Measurable (Function.uncurry L))
    (hK : WeightedFormBound μ ν wX wY p (p / (p - 1)) K c)
    (hL : WeightedFormBound ν ρ (fun y => -wY y) wZ p (p / (p - 1)) L d) :
    WeightedFormBound μ ρ wX wZ p (p / (p - 1)) (spatialKernelComp ν K L) (c * d) := by
  have hpq : p.HolderConjugate (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  exact hK.comp hpq hwY hKm hLm hL

end Critical2DKPZ.SHF.Tsai

end
