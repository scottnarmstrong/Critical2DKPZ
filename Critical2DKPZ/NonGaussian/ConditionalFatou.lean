/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.NonnegativeFatou
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Tactic

/-! # Passing conditional upper bounds through nonnegative limits -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Critical2DKPZ.NonGaussian

/-- Set-integral upper bounds characterize a conditional-expectation upper
bound when the majorant is measurable in the conditioning sigma algebra. -/
theorem condExp_le_of_forall_setIntegral_le {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    (F Y : Ω → ℝ) (hF : Integrable F P) (hY : Integrable Y P)
    (hYm : StronglyMeasurable[m] Y)
    (hbound : ∀ S : Set Ω, MeasurableSet[m] S → (∫ ω in S, F ω ∂P) ≤ ∫ ω in S, Y ω ∂P) :
    P[F | m] ≤ᵐ[P] Y := by
  let : MeasurableSpace Ω := m₀
  apply ae_of_ae_trim hm
  apply ae_le_of_forall_setIntegral_le (integrable_condExp.trim hm stronglyMeasurable_condExp)
    (hY.trim hm hYm)
  intro S hS _
  rw [← setIntegral_trim hm stronglyMeasurable_condExp hS,
    ← setIntegral_trim hm hYm hS, setIntegral_condExp hm hF hS]
  exact hbound S hS

/-- An almost-everywhere limit of nonnegative integrable functions is integrable and obeys
the same conditional upper bound when the common majorant is integrable. -/
theorem integrable_and_condExp_le_of_ae_tendsto_nonneg {Ω : Type*}
    [m₀ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    (F : ℕ → Ω → ℝ) (hF : ∀ n, Integrable (F n) P) (hF0 : ∀ n, 0 ≤ᵐ[P] F n)
    (G : Ω → ℝ) (hG : AEMeasurable G P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (G ω)))
    (Y : Ω → ℝ) (hY : Integrable Y P) (hY0 : 0 ≤ᵐ[P] Y) (hYm : StronglyMeasurable[m] Y)
    (hbound : ∀ n, P[F n | m] ≤ᵐ[P] Y) :
    Integrable G P ∧ P[G | m] ≤ᵐ[P] Y := by
  let : MeasurableSpace Ω := m₀
  have hSets (S : Set Ω) (hS : MeasurableSet[m] S) :
      IntegrableOn G S P ∧ (∫ ω in S, G ω ∂P) ≤ ∫ ω in S, Y ω ∂P := by
    have hFatou := integrable_and_integral_le_of_ae_tendsto_nonneg (P.restrict S) F
      (fun n => (hF n).integrableOn) (fun n => ae_restrict_of_ae (hF0 n)) G hG.restrict
      (ae_restrict_of_ae hlim) (∫ ω in S, Y ω ∂P)
      (integral_nonneg_of_ae (ae_restrict_of_ae hY0)) (fun n => ?_)
    · exact hFatou.2
    · rw [← setIntegral_condExp hm (hF n) hS]
      exact integral_mono_ae integrable_condExp.integrableOn hY.integrableOn
        (ae_restrict_of_ae (hbound n))
  have hUniv := (hSets Set.univ MeasurableSet.univ).1
  simp only [IntegrableOn, Measure.restrict_univ] at hUniv
  exact ⟨hUniv, condExp_le_of_forall_setIntegral_le P m hm G Y hUniv hY hYm
    (fun S hS => (hSets S hS).2)⟩


end Critical2DKPZ.NonGaussian

end
