/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CollisionLpBounds
public import Critical2DKPZ.SHF.Tsai.ConjugatedBounds
public import Critical2DKPZ.SHF.DeltaBose.CollisionWeight
public import Critical2DKPZ.SHF.DeltaBose.ScalarEnvelope
import Mathlib.Tactic

/-! # Scaling weighted kernel form bounds

Multiplication of a nonnegative kernel by a finite nonnegative scalar multiplies its
weighted bilinear form constant by the same scalar.
-/

@[expose] public section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open Critical2DKPZ.SHF.Flow
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai


/-- Scaling a positive kernel and its form constant preserves a weighted
bilinear estimate. -/
theorem weightedFormBound_const_mul {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    {wX : X → ℝ} {wY : Y → ℝ} {p p' : ℝ}
    {K : X → Y → ℝ≥0∞} {c d : ℝ≥0∞} (hd : d ≠ ⊤)
    (h : WeightedFormBound μ ν wX wY p p' K c) :
    WeightedFormBound μ ν wX wY p p' (fun x y => d * K x y) (d * c) := by
  intro f g hf hg
  have hinner (x : X) :
      (∫⁻ y, d * K x y * f y ∂ν) = d * (∫⁻ y, K x y * f y ∂ν) := by
    calc
      _ = ∫⁻ y, d * (K x y * f y) ∂ν := by
        apply lintegral_congr
        intro y
        ac_rfl
      _ = _ := lintegral_const_mul' d _ hd
  calc
    (∫⁻ x, g x * (∫⁻ y, d * K x y * f y ∂ν) ∂μ)
        = d * (∫⁻ x, g x * (∫⁻ y, K x y * f y ∂ν) ∂μ) := by
          calc
            _ = ∫⁻ x, d * (g x * (∫⁻ y, K x y * f y ∂ν)) ∂μ := by
              apply lintegral_congr
              intro x
              rw [hinner x]
              ac_rfl
            _ = _ := lintegral_const_mul' d _ hd
    _ ≤ d * (c *
          (∫⁻ y, (f y * ENNReal.ofReal (Real.exp (wY y))) ^ p ∂ν) ^ (1 / p) *
          (∫⁻ x, (g x * ENNReal.ofReal (Real.exp (wX x))) ^ p' ∂μ) ^ (1 / p')) :=
        mul_le_mul' le_rfl (h f g hf hg)
    _ = d * c *
          (∫⁻ y, (f y * ENNReal.ofReal (Real.exp (wY y))) ^ p ∂ν) ^ (1 / p) *
          (∫⁻ x, (g x * ENNReal.ofReal (Real.exp (wX x))) ^ p' ∂μ) ^ (1 / p') := by
        ac_rfl


end Critical2DKPZ.SHF.Tsai

end
