/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.KernelCompositionL2
import Mathlib.Tactic.Ring

/-! # Exponential conjugation of positive spatial kernels -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- Conjugate a positive kernel by finite real exponential endpoint weights. -/
def expConjugate {X Y : Type*} (a : X → ℝ) (b : Y → ℝ) (K : X → Y → ℝ≥0∞)
    (x : X) (y : Y) : ℝ≥0∞ := K x y * ENNReal.ofReal (Real.exp (a x - b y))

/-- Conjugating an `ofReal` kernel is the explicit weighted real kernel. -/
theorem expConjugate_ofReal {X Y : Type*} (a : X → ℝ) (b : Y → ℝ) (K : X → Y → ℝ)
    (x : X) (y : Y) :
    expConjugate a b (fun x y => ENNReal.ofReal (K x y)) x y =
      ENNReal.ofReal (K x y * Real.exp (a x - b y)) := by
  unfold expConjugate
  rw [mul_comm (ENNReal.ofReal (K x y)), ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    mul_comm (Real.exp _) (K x y)]

/-- Exponential conjugation by measurable weights preserves joint kernel measurability. -/
theorem measurable_expConjugate {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {a : X → ℝ} {b : Y → ℝ} {K : X → Y → ℝ≥0∞}
    (ha : Measurable a) (hb : Measurable b) (hK : Measurable (Function.uncurry K)) :
    Measurable (Function.uncurry (expConjugate a b K)) :=
  hK.mul (((ha.comp measurable_fst).sub (hb.comp measurable_snd)).exp.ennreal_ofReal)

private theorem expConjugate_mul {k l : ℝ≥0∞} (a b c : ℝ) :
    (k * ENNReal.ofReal (Real.exp (a - b))) *
      (l * ENNReal.ofReal (Real.exp (b - c))) =
        (k * l) * ENNReal.ofReal (Real.exp (a - c)) := by
  calc
    _ = (k * l) * (ENNReal.ofReal (Real.exp (a - b)) *
        ENNReal.ofReal (Real.exp (b - c))) := by ac_rfl
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 3
      ring

/-- The intermediate weight cancels inside an spatial composition. -/
theorem expConjugate_spatialKernelComp {X Y Z : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (a : X → ℝ) (b : Y → ℝ) (c : Z → ℝ)
    (K : X → Y → ℝ≥0∞) (L : Y → Z → ℝ≥0∞) (x : X) (z : Z) :
    spatialKernelComp ν (expConjugate a b K) (expConjugate b c L) x z =
      expConjugate a c (spatialKernelComp ν K L) x z := by
  unfold spatialKernelComp expConjugate
  calc
    _ = ∫⁻ y, (K x y * L y z) * ENNReal.ofReal (Real.exp (a x - c z)) ∂ν := by
      apply lintegral_congr
      intro y
      exact expConjugate_mul (a x) (b y) (c z)
    _ = _ := lintegral_mul_const' _ _ ENNReal.ofReal_ne_top

/-- Squared operator bounds compose after exponential conjugation. -/
theorem expConjugate_spatialKernelComp_l2_sq_le {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) (ρ : Measure Z)
    [SFinite μ] [SFinite ν] [SFinite ρ]
    {a : X → ℝ} {b : Y → ℝ} {c : Z → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    {K : X → Y → ℝ≥0∞} {L : Y → Z → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) (hL : Measurable (Function.uncurry L))
    {A B : ℝ≥0∞}
    (hKA : ∀ {g : Y → ℝ≥0∞}, Measurable g →
      (∫⁻ x, (∫⁻ y, expConjugate a b K x y * g y ∂ν) ^ 2 ∂μ) ≤ A * ∫⁻ y, g y ^ 2 ∂ν)
    (hLB : ∀ {f : Z → ℝ≥0∞}, Measurable f →
      (∫⁻ y, (∫⁻ z, expConjugate b c L y z * f z ∂ρ) ^ 2 ∂ν) ≤ B * ∫⁻ z, f z ^ 2 ∂ρ)
    {f : Z → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, (∫⁻ z, expConjugate a c (spatialKernelComp ν K L) x z * f z ∂ρ) ^ 2 ∂μ) ≤
      (A * B) * ∫⁻ z, f z ^ 2 ∂ρ := by
  have h := spatialKernelComp_l2_sq_mul_le μ ν ρ
    (measurable_expConjugate ha hb hK) (measurable_expConjugate hb hc hL) hKA hLB hf
  simpa only [expConjugate_spatialKernelComp] using h


end Critical2DKPZ.SHF.Flow

end
