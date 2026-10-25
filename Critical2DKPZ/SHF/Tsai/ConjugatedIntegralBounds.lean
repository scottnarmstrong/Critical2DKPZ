/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.WeightedFormBoundIntegral
import Mathlib.Tactic

/-! # Integrating weighted form bounds over a measurable time domain -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Integrating nonnegative kernels over a measurable time domain integrates their weighted bilinear form bounds. -/
theorem WeightedFormBound.setLIntegral_param {T X Y : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [MeasurableSpace Y]
    {κ : Measure T} {μ : Measure X} {ν : Measure Y}
    [SigmaFinite κ] [SFinite μ] [SigmaFinite ν]
    {wX : X → ℝ} {wY : Y → ℝ} {p p' : ℝ}
    {K : T → X → Y → ℝ≥0∞} {c : T → ℝ≥0∞} {s : Set T} (hs : MeasurableSet s)
    (hKm : Measurable (fun q : T × X × Y => K q.1 q.2.1 q.2.2)) (hcm : Measurable c)
    (hbound : ∀ t ∈ s, WeightedFormBound μ ν wX wY p p' (K t) (c t)) :
    WeightedFormBound μ ν wX wY p p'
      (fun x y => ∫⁻ t in s, K t x y ∂κ) (∫⁻ t in s, c t ∂κ) := by
  classical
  let K' : T → X → Y → ℝ≥0∞ := fun t x y => if t ∈ s then K t x y else 0
  let c' : T → ℝ≥0∞ := s.indicator c
  have hK' : Measurable (fun q : T × X × Y => K' q.1 q.2.1 q.2.2) :=
    Measurable.ite (hs.preimage measurable_fst) hKm measurable_const
  have hc' : Measurable c' := hcm.indicator hs
  have hb' (t : T) : WeightedFormBound μ ν wX wY p p' (K' t) (c' t) := by
    by_cases ht : t ∈ s
    · simpa only [K', c', ite_eq_left ht, indicator_of_mem ht] using hbound t ht
    · intro f g hf hg
      simp only [K', c', ite_eq_right ht, indicator_of_notMem ht, zero_mul,
        mul_zero, lintegral_zero, le_refl]
  have h := WeightedFormBound.lintegral_param (κ := κ) hK' hc' hb'
  have he (x : X) (y : Y) : (∫⁻ t, K' t x y ∂κ) = ∫⁻ t in s, K t x y ∂κ := by
    change (∫⁻ t, s.indicator (fun t => K t x y) t ∂κ) = _
    exact lintegral_indicator hs _
  simp_rw [he] at h
  simpa only [c', lintegral_indicator hs] using h

end Critical2DKPZ.SHF.Tsai

end
