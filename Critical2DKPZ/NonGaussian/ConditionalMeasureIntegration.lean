/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.IndependentMeasureIntegration
public import Critical2DKPZ.NonGaussian.RandomMeasureParameterMeasurability
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic

/-! # Conditional integration of an independent random measure -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Critical2DKPZ.NonGaussian

/-- Replacing an independent random measure by its mean preserves nonnegative integrals
on events measurable with respect to the random parameter. -/
theorem setLIntegral_independent_measure_parameter {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → A) (hX : Measurable X)
    (B : Ω → Measure (Plane × Plane)) (hB : Measurable B)
    (hBLF : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (B ω)) (hind : IndepFun X B P)
    (H : A → (Plane × Plane) → ℝ≥0∞) (hH : Measurable (Function.uncurry H))
    [SigmaFinite (P.bind B)] (S : Set Ω)
    (hS : MeasurableSet[MeasurableSpace.comap X inferInstance] S) :
    (∫⁻ ω in S, ∫⁻ z, H (X ω) z ∂B ω ∂P) =
      ∫⁻ ω in S, ∫⁻ z, H (X ω) z ∂P.bind B ∂P := by
  classical
  obtain ⟨T, hT, rfl⟩ := hS
  let H' : A → (Plane × Plane) → ℝ≥0∞ := fun a z => if a ∈ T then H a z else 0
  have hH' : Measurable (Function.uncurry H') :=
    Measurable.ite (hT.preimage measurable_fst) hH measurable_const
  have havg := lintegral_independent_measure_parameter P X hX B hB hBLF hind H' hH'
  have hK : Measurable (fun a => ∫⁻ z, H' a z ∂P.bind B) := hH'.lintegral_prod_right
  rw [lintegral_map' hK.aemeasurable hX.aemeasurable] at havg
  have hIndicator (a : A) (μ : Measure (Plane × Plane)) :
      (∫⁻ z, H' a z ∂μ) = T.indicator (fun a => ∫⁻ z, H a z ∂μ) a := by
    by_cases ha : a ∈ T <;> simp [H', ha]
  simp_rw [hIndicator] at havg
  change (∫⁻ ω, (X ⁻¹' T).indicator (fun ω => ∫⁻ z, H (X ω) z ∂B ω) ω ∂P) =
    (∫⁻ ω, (X ⁻¹' T).indicator (fun ω => ∫⁻ z, H (X ω) z ∂P.bind B) ω ∂P) at havg
  simpa only [lintegral_indicator (hT.preimage hX)] using havg

end Critical2DKPZ.NonGaussian

end
