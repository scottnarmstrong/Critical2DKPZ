/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.StationaryLaw
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! # Spatial integration and random `L¹` classes

One-point stationarity suffices for integrability on bounded spatial sets.
The integration identity below identifies an `L¹`-valued integral with the
pathwise integral of any jointly integrable representative.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Spatial restrictions of a jointly measurable field with integrable stationary
one-point laws are jointly integrable whenever the spatial measure is finite. -/
theorem integrable_stationary_prod {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {g : α → Ω → ℝ} {g₀ : Ω → ℝ}
    (hg : Measurable (Function.uncurry g))
    (hstat : ∀ y, IdentDistrib (g y) g₀ P P) (hint : Integrable g₀ P) :
    Integrable (Function.uncurry g) (μ.prod P) := by
  apply (integrable_prod_iff hg.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (fun y => (hstat y).integrable_iff.mpr hint), ?_⟩
  have he : (fun y => ∫ ω, ‖g y ω‖ ∂P) = fun _ : α => ∫ ω, ‖g₀ ω‖ ∂P :=
    funext fun y => (hstat y).norm.integral_eq
  change Integrable (fun y => ∫ ω, ‖g y ω‖ ∂P) μ
  rw [he]
  exact integrable_const _

omit [IsProbabilityMeasure P] in
/-- The Bochner integral of `L¹` classes agrees with the pathwise integral of a
jointly integrable representative. -/
theorem integral_L1_ae_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] [SFinite P] {f : α → Ω → E} (F : α → Lp E 1 P)
    (hF : Integrable F μ) (hf : Integrable (Function.uncurry f) (μ.prod P))
    (hrep : ∀ y, (F y : Ω → E) =ᵐ[P] f y) :
    ((∫ y, F y ∂μ : Lp E 1 P) : Ω → E) =ᵐ[P] fun ω => ∫ y, f y ω ∂μ := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ (L1.integrable_coeFn _)
    hf.integral_prod_right
  intro s hs _
  let L : Lp E 1 P →L[ℝ] E :=
    L1.integralCLM.comp (LpToLpRestrictCLM Ω E ℝ P 1 s)
  have hL (X : Lp E 1 P) : L X = ∫ ω in s, X ω ∂P := by
    change L1.integralCLM (LpToLpRestrictCLM Ω E ℝ P 1 s X) = _
    rw [← L1.integral_eq, L1.integral_eq_integral]
    exact integral_congr_ae (LpToLpRestrictCLM_coeFn ℝ s X)
  have hfs : Integrable (Function.uncurry f) (μ.prod (P.restrict s)) :=
    hf.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  calc
    (∫ ω in s, (∫ y, F y ∂μ : Lp E 1 P) ω ∂P) = L (∫ y, F y ∂μ) :=
      (hL _).symm
    _ = ∫ y, L (F y) ∂μ := (L.integral_comp_comm hF).symm
    _ = ∫ y, ∫ ω in s, f y ω ∂P ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y => (hL _).trans
        (integral_congr_ae (ae_restrict_of_ae (hrep y)))
    _ = ∫ ω in s, ∫ y, f y ω ∂μ ∂P := integral_integral_swap hfs

end Critical2DKPZ.Extensions.ScaleLimit

end
