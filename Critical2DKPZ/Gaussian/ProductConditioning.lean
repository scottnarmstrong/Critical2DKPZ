/-
Copyright (c) 2026 Scott Armstrong, Ahmed Bou-Rabee and Tuomo Kuusi.
Released under Apache 2.0 license as described in the file LICENSE.
Modified for Critical2DKPZ, 2026.
Adapted from subdiffusive-process, commit 4c6b8fa60357a07fd5713e5104a6cc70f8e432dc.
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Conditional expectations under product decompositions -/

@[expose] public section

open MeasureTheory
open scoped MeasureTheory

namespace Critical2DKPZ.Gaussian

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Conditioning on the first coordinate integrates out the second coordinate. -/
theorem condExp_prod_fst_integral {f : A × B → ℝ} (hf : Integrable f (μ.prod ν)) :
    (μ.prod ν)[f | (inferInstance : MeasurableSpace A).comap Prod.fst] =ᵐ[μ.prod ν]
      fun p => ∫ b, f (p.1, b) ∂ν := by
  have hm : (inferInstance : MeasurableSpace A).comap (Prod.fst : A × B → A) ≤
      (inferInstance : MeasurableSpace (A × B)) :=
    (measurable_fst : Measurable (Prod.fst : A × B → A)).comap_le
  let h : A → ℝ := fun a => ∫ b, f (a, b) ∂ν
  have hh : Integrable h μ := hf.integral_prod_left
  have hg : Integrable (fun p : A × B => h p.1) (μ.prod ν) := hh.comp_fst ν
  have hgm : AEStronglyMeasurable[(inferInstance : MeasurableSpace A).comap Prod.fst]
      (fun p : A × B => h p.1) (μ.prod ν) := by
    refine ⟨fun p => hh.aestronglyMeasurable.mk h p.1, ?_, ?_⟩
    · exact hh.aestronglyMeasurable.stronglyMeasurable_mk.comp_measurable
        (comap_measurable Prod.fst)
    · exact Measure.quasiMeasurePreserving_fst.ae_eq_comp hh.aestronglyMeasurable.ae_eq_mk
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hf
  · intro s hs hfin
    exact hg.integrableOn
  · intro s hs hfin
    obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    have hset : Prod.fst ⁻¹' t = t ×ˢ (Set.univ : Set B) := by ext p; simp
    rw [hset, setIntegral_prod _ hg.integrableOn, setIntegral_prod _ hf.integrableOn]
    simp [h]
  · exact hgm

/-- Conditional expectation is compatible with a measure-preserving relabeling. -/
theorem condExp_comp_measurableEquiv {X Y : Type*}
    {m : MeasurableSpace Y} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
    {ξ : Measure X} {ζ : Measure Y} [IsFiniteMeasure ξ] [IsFiniteMeasure ζ]
    (e : X ≃ᵐ Y) (he : MeasurePreserving e ξ ζ)
    (hm : m ≤ mY)
    {f : Y → ℝ} (hf : Integrable f ζ) :
    ξ[f ∘ e | m.comap e] =ᵐ[ξ] (ζ[f | m]) ∘ e := by
  have hle : m.comap e ≤ mX := (MeasurableSpace.comap_mono hm).trans e.measurable.comap_le
  have hfc : Integrable (f ∘ e) ξ := he.integrable_comp_of_integrable hf
  have hgc : Integrable ((ζ[f | m]) ∘ e) ξ :=
    he.integrable_comp_of_integrable integrable_condExp
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hle hfc
  · intro s hs hfin
    exact hgc.integrableOn
  · intro s hs hfin
    obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    have het := he.restrict_preimage (hm t ht)
    change (∫ x in e ⁻¹' t, (ζ[f | m]) (e x) ∂ξ) =
      ∫ x in e ⁻¹' t, f (e x) ∂ξ
    rw [het.integral_comp' _, het.integral_comp' _]
    exact setIntegral_condExp hm hf ht
  · exact (stronglyMeasurable_condExp.comp_measurable
      (comap_measurable e)).aestronglyMeasurable

/-- Integrate the discarded coordinate after a measure-preserving product decomposition. -/
theorem condExp_equiv_fst_integral {X : Type*} [MeasurableSpace X]
    {ξ : Measure X} [IsProbabilityMeasure ξ]
    (e : X ≃ᵐ A × B) (he : MeasurePreserving e ξ (μ.prod ν))
    {f : X → ℝ} (hf : Integrable f ξ) :
    ξ[f | (inferInstance : MeasurableSpace A).comap (fun x => (e x).1)] =ᵐ[ξ]
      fun x => ∫ b, f (e.symm ((e x).1, b)) ∂ν := by
  have hfi : Integrable (f ∘ e.symm) (μ.prod ν) :=
    (he.symm e).integrable_comp_of_integrable hf
  have hce := condExp_comp_measurableEquiv e he
    (measurable_fst : Measurable (Prod.fst : A × B → A)).comap_le hfi
  have hav := he.quasiMeasurePreserving.ae_eq_comp (condExp_prod_fst_integral hfi)
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, e.symm_apply_apply] using
    hce.trans hav

end Critical2DKPZ.Gaussian

end
