/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Critical2DKPZ.JointConvergence.MomentConvergence
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Tactic

/-! # Bounds transported by convergence in law

Nonnegative continuous moments pass in the lower-semicontinuity direction.
Open-event upper bounds pass in the same direction. These statements require
no uniform integrability and do not use indicators of closed good events.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- An eventual bound on a nonnegative continuous observable passes to the
limit law, with integrability of the limit included. -/
theorem integral_continuous_nonneg_le_of_tendstoInDistribution
    {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {X : ℕ → Ω → E} {Y : Ω' → E}
    (hX : TendstoInDistribution X atTop Y (fun _ => P) Q)
    (f : E → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) (C : ℝ)
    (hint : ∀ᶠ n in atTop, Integrable (fun ω => f (X n ω)) P)
    (hbound : ∀ᶠ n in atTop, (∫ ω, f (X n ω) ∂P) ≤ C) :
    Integrable (fun ω => f (Y ω)) Q ∧ (∫ ω, f (Y ω) ∂Q) ≤ C := by
  have habs (x : E) : |f x| = f x := abs_of_nonneg (hf0 x)
  have hi : ∀ᶠ n in atTop, Integrable (fun ω => |(f ∘ X n) ω| ^ (1 : ℝ)) P := by
    simpa only [Function.comp_def, Real.rpow_one, habs] using hint
  have hb : ∀ᶠ n in atTop, (∫ ω, |(f ∘ X n) ω| ^ (1 : ℝ) ∂P) ≤ C := by
    simpa only [Function.comp_def, Real.rpow_one, habs] using hbound
  have h := JointConvergence.integrable_rpow_limit_of_tendstoInDistribution
    (hX.continuous_comp hf) (by norm_num : (0 : ℝ) < 1) hi hb
  simpa only [Function.comp_def, Real.rpow_one, habs] using h

/-- A uniform eventual bound for an open event passes to the limit. -/
theorem measure_open_le_of_tendstoInDistribution
    {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {X : ℕ → Ω → E} {Y : Ω' → E}
    (hX : TendstoInDistribution X atTop Y (fun _ => P) Q)
    (G : Set E) (hG : IsOpen G) (C : ℝ≥0∞)
    (hb : ∀ᶠ n in atTop, P (X n ⁻¹' G) ≤ C) : Q (Y ⁻¹' G) ≤ C := by
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hX.tendsto hG
  have hmaps (n : ℕ) : (P.map (X n)) G = P (X n ⁻¹' G) :=
    Measure.map_apply_of_aemeasurable (hX.forall_aemeasurable n) hG.measurableSet
  change (Q.map Y) G ≤ atTop.liminf (fun n => (P.map (X n)) G) at hport
  rw [Measure.map_apply_of_aemeasurable hX.aemeasurable_limit hG.measurableSet] at hport
  apply hport.trans
  have hmapbound : ∀ᶠ n in atTop, (P.map (X n)) G ≤ C := by
    filter_upwards [hb] with n hn
    rw [hmaps]
    exact hn
  apply liminf_le_of_le (by isBoundedDefault)
  intro b hb'
  obtain ⟨n, hn, hnb⟩ := (hb'.and hmapbound).exists
  exact hn.trans hnb

end Critical2DKPZ.Extensions.ScaleLimit
