/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.ConditionalMeasureIntegration
import Mathlib.Tactic

/-! # Conditional expectation of an independent random-measure integral -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Critical2DKPZ.NonGaussian

/-- Averaging an independent random measure gives the conditional expectation
of its nonnegative integral, provided the averaged integral is finite.
Integrability of both real-valued functions is part of the conclusion. -/
theorem condExp_independent_measure_parameter {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → A) (hX : Measurable X)
    (B : Ω → Measure (Plane × Plane)) (hB : Measurable B)
    (hBLF : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (B ω)) (hind : IndepFun X B P)
    (H : A → (Plane × Plane) → ℝ≥0∞) (hH : Measurable (Function.uncurry H))
    [SigmaFinite (P.bind B)]
    (hfin : (∫⁻ a, ∫⁻ z, H a z ∂P.bind B ∂P.map X) ≠ ∞) :
    Integrable (fun ω => (∫⁻ z, H (X ω) z ∂B ω).toReal) P ∧
    Integrable (fun ω => (∫⁻ z, H (X ω) z ∂P.bind B).toReal) P ∧
    P[fun ω => (∫⁻ z, H (X ω) z ∂B ω).toReal |
        MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun ω => (∫⁻ z, H (X ω) z ∂P.bind B).toReal := by
  let F : Ω → ℝ≥0∞ := fun ω => ∫⁻ z, H (X ω) z ∂B ω
  let K : A → ℝ≥0∞ := fun a => ∫⁻ z, H a z ∂P.bind B
  have hF : AEMeasurable F P :=
    aemeasurable_lintegral_locallyFinite_randomMeasure P B hB hBLF
      (fun ω z => H (X ω) z) (hH.comp (hX.comp measurable_fst |>.prodMk measurable_snd))
  have hK : Measurable K := hH.lintegral_prod_right
  have hFfin : (∫⁻ ω, F ω ∂P) ≠ ∞ := by
    rw [lintegral_independent_measure_parameter P X hX B hB hBLF hind H hH]
    exact hfin
  have hKfin : (∫⁻ ω, K (X ω) ∂P) ≠ ∞ := by
    rw [← lintegral_map' hK.aemeasurable hX.aemeasurable]
    exact hfin
  have hFI := integrable_toReal_of_lintegral_ne_top hF hFfin
  have hKI := integrable_toReal_of_lintegral_ne_top (hK.comp hX).aemeasurable hKfin
  refine ⟨hFI, hKI, ?_⟩
  have hm : MeasurableSpace.comap X inferInstance ≤ ‹MeasurableSpace Ω› := hX.comap_le
  have hXm : Measurable[MeasurableSpace.comap X inferInstance] X :=
    Measurable.of_comap_le le_rfl
  have hEq := ae_eq_condExp_of_forall_setIntegral_eq hm hFI
    (fun S _ _ => hKI.integrableOn) (g := fun ω => (K (X ω)).toReal) ?_
    (hK.ennreal_toReal.comp hXm).aestronglyMeasurable
  · exact hEq.symm
  · intro S hS _
    have hNonneg := setLIntegral_independent_measure_parameter P X hX B hB hBLF hind H hH S hS
    have hFFinite := ae_lt_top' hF hFfin
    have hKFinite := ae_lt_top' (hK.comp hX).aemeasurable hKfin
    calc
      (∫ ω in S, (K (X ω)).toReal ∂P) = (∫⁻ ω in S, K (X ω) ∂P).toReal :=
        integral_toReal ((hK.comp hX).aemeasurable.restrict) (ae_restrict_of_ae hKFinite)
      _ = (∫⁻ ω in S, F ω ∂P).toReal := congrArg ENNReal.toReal hNonneg.symm
      _ = ∫ ω in S, (F ω).toReal ∂P :=
        (integral_toReal hF.restrict (ae_restrict_of_ae hFFinite)).symm

end Critical2DKPZ.NonGaussian

end
