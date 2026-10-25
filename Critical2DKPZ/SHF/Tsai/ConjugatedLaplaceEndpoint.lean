/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedIntegralBounds
public import Critical2DKPZ.SHF.Tsai.ConjugatedLaplacePowers
public import Critical2DKPZ.SHF.DeltaBose.LaplaceComposition
import Critical2DKPZ.SHF.Tsai.ConjugatedCollisionLp
import Mathlib.Tactic

/-! # Laplace bounds for weighted endpoint power estimates -/

@[expose] public noncomputable section

open MeasureTheory Set Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Laplace integration of an integrable endpoint power, retaining the
precise inverse-rate power required when two endpoints are composed. -/
theorem WeightedFormBound.laplace_of_power_bound {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SigmaFinite ν] {wX : X → ℝ} {wY : Y → ℝ} {p p' : ℝ}
    {K : TimeKernel X Y} (hK : Measurable K) {C c₀ b rate : ℝ}
    (hC : 0 ≤ C) (hb : -1 < b) (hrate : c₀ < rate)
    (hbound : ∀ t : ℝ, 0 < t → WeightedFormBound μ ν wX wY p p'
      (fun x y => K (t, x, y)) (ENNReal.ofReal (C * Real.exp (c₀ * t) * t ^ b))) :
    WeightedFormBound μ ν wX wY p p' (laplaceTimeKernel rate K)
      (ENNReal.ofReal (C * Real.Gamma (b + 1) * (1 / (rate - c₀)) ^ (b + 1))) := by
  let L : ℝ → X → Y → ℝ≥0∞ := fun t x y => laplaceTimeWeight rate t * K (t, x, y)
  let c : ℝ → ℝ≥0∞ := fun t => laplaceTimeWeight rate t *
    ENNReal.ofReal (C * Real.exp (c₀ * t) * t ^ b)
  have hw : Measurable (fun t : ℝ => laplaceTimeWeight rate t) := by
    unfold laplaceTimeWeight
    fun_prop
  have hLm : Measurable (fun q : ℝ × X × Y => L q.1 q.2.1 q.2.2) :=
    (hw.comp measurable_fst).mul hK
  have hcm : Measurable c := by
    dsimp [c, laplaceTimeWeight]
    fun_prop
  have hLbound (t : ℝ) (ht : t ∈ Ioi 0) : WeightedFormBound μ ν wX wY p p' (L t) (c t) :=
    weightedFormBound_const_mul (d := laplaceTimeWeight rate t) ENNReal.ofReal_ne_top (hbound t ht)
  have h := WeightedFormBound.setLIntegral_param (κ := volume) measurableSet_Ioi hLm hcm hLbound
  have hpoint (t : ℝ) : c t = ENNReal.ofReal C *
      ENNReal.ofReal (Real.exp (-((rate - c₀) * t)) * t ^ b) := by
    dsimp [c, laplaceTimeWeight]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul hC]
    congr 1
    have he : Real.exp (-(rate * t)) * Real.exp (c₀ * t) =
        Real.exp (-((rate - c₀) * t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = C * ((Real.exp (-(rate * t)) * Real.exp (c₀ * t)) * t ^ b) := by ring
      _ = _ := by rw [he]
  have hc : (∫⁻ t in Ioi 0, c t) =
      ENNReal.ofReal (C * Real.Gamma (b + 1) * (1 / (rate - c₀)) ^ (b + 1)) := by
    calc
      _ = ∫⁻ t in Ioi 0, ENNReal.ofReal C *
          ENNReal.ofReal (Real.exp (-((rate - c₀) * t)) * t ^ b) := lintegral_congr hpoint
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          (integrableOn_and_lintegral_exp_mul_rpow hb (sub_pos.mpr hrate)).2,
          ← ENNReal.ofReal_mul hC]
        congr 1
        ring
  rw [hc] at h
  exact h

end Critical2DKPZ.SHF.Tsai

end
