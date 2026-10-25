/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedBounds
public import Critical2DKPZ.SHF.Flow.KernelConjugation
import Mathlib.Tactic

/-! # Transport from canonical exponential kernel conjugation to weighted forms -/

@[expose] public section

open MeasureTheory Critical2DKPZ.SHF.Flow
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- An ordinary bilinear bound for the canonical exponential conjugate gives
the corresponding conjugated weighted form estimate. -/
theorem WeightedFormBound.of_expConjugate {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    {a : X → ℝ} {b : Y → ℝ} {K : X → Y → ℝ≥0∞} {p p' : ℝ} {c : ℝ≥0∞}
    (ha : Measurable a) (hb : Measurable b) (hK : Measurable (Function.uncurry K))
    (h : WeightedFormBound μ ν (fun _ => 0) (fun _ => 0) p p' (expConjugate a b K) c) :
    WeightedFormBound μ ν (fun x => -a x) b p p' K c := by
  apply WeightedFormBound.conjugate ha.neg hb (measurable_expConjugate ha hb hK) h
  intro x y
  have he : ENNReal.ofReal (Real.exp (a x - b y)) *
      ENNReal.ofReal (Real.exp (-a x)) * ENNReal.ofReal (Real.exp (b y)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le,
      ← Real.exp_add, ← Real.exp_add]
    rw [show (a x - b y) + -a x + b y = 0 by ring, Real.exp_zero, ENNReal.ofReal_one]
  dsimp [expConjugate]
  calc
    K x y = K x y * 1 := (mul_one _).symm
    _ = K x y * (ENNReal.ofReal (Real.exp (a x - b y)) *
        ENNReal.ofReal (Real.exp (-a x)) * ENNReal.ofReal (Real.exp (b y))) := by rw [he]
    _ = _ := by ac_rfl

end Critical2DKPZ.SHF.Tsai

end
