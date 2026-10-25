/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.Definitions.IsCriticalKPZ
public import Critical2DKPZ.Extensions.ScaleLimit.MollifierReductions
import Critical2DKPZ.Extensions.ScaleLimit.FiniteFamilyLaw
import Critical2DKPZ.Extensions.ScaleLimit.Centring
import Critical2DKPZ.Provider.CriticalKPZInvariance
import Critical2DKPZ.Provider.CriticalKPZMain
import Critical2DKPZ.Assembly.Final
import Mathlib.Tactic

/-! # Reduction of finite-dimensional laws to unit time

The parabolically rescaled flow and its associated KPZ version can be chosen
on the original probability space. Only finite tested laws are transported.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction ENNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Scaling transports every finite family of dilated tests to any associated
unit-time field of the shifted-parameter flow. -/
theorem scaling_dilate_law (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {t : ℝ} (ht : 0 < t)
    (Z' : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ' : IsCriticalSHF (ϑ + Real.log t) P Z')
    (H' : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH' : IsCriticalKPZ P Z' H')
    {I : Type*} [Fintype I] (φ : TestFn) (x : Plane) (ε : I → ℝ) :
    P.map (fun ω i => H t 0 ω (φ.dilate (ε i) x)) =
      P.map (fun ω i => H' 1 0 ω (φ.dilate (ε i / Real.sqrt t) ((Real.sqrt t)⁻¹ • x))) := by
  have hXm : AEMeasurable (fun ω i => H t 0 ω (φ.dilate (ε i) x)) P :=
    aemeasurable_pi_iff.mpr fun i => (memLp_kpz_two ϑ P Z hZ H hH t ht _).aemeasurable
  have hYm : AEMeasurable (fun ω i => H' 1 0 ω
      (φ.dilate (ε i / Real.sqrt t) ((Real.sqrt t)⁻¹ • x))) P :=
    aemeasurable_pi_iff.mpr fun i =>
      (memLp_kpz_two (ϑ + Real.log t) P Z' hZ' H' hH' 1 zero_lt_one _).aemeasurable
  apply map_fintype_eq_of_fin_laws P P _ _ hXm hYm
  intro k f
  let ψ : Fin k → TestFn := fun i => φ.dilate (ε (f i) / Real.sqrt t) ((Real.sqrt t)⁻¹ • x)
  have h := (Provider.criticalKPZ_invariance ϑ P Z hZ H hH k (fun _ => 1)
    (fun _ => zero_lt_one) ψ).2.2 t ht P Z' hZ' H' hH'
  simpa only [mul_one, ψ, scale_dilate_div_sqrt φ ht] using h

/-- An associated shifted-parameter flow and unit-time field exist on the same
probability space, and their dilated finite-dimensional laws satisfy scaling. -/
theorem scaling_reduction (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {I : Type*} [Fintype I] {t : ℝ} (ht : 0 < t) (φ : TestFn) (x : Plane) :
    ∃ (Z' : ℝ → ℝ → Ω → Measure (Plane × Plane))
      (H' : ℝ → (Plane →ᵇ ℝ) → Ω → Distr),
      IsCriticalSHF (ϑ + Real.log t) P Z' ∧ IsCriticalKPZ P Z' H' ∧
      ∀ ε : I → ℝ, P.map (fun ω i => H t 0 ω (φ.dilate (ε i) x)) =
        P.map (fun ω i => H' 1 0 ω (φ.dilate (ε i / Real.sqrt t) ((Real.sqrt t)⁻¹ • x))) := by
  let Z' : ℝ → ℝ → Ω → Measure (Plane × Plane) := fun s u ω =>
    ENNReal.ofReal t⁻¹ • (Z (t * s) (t * u) ω).map
      (fun p => ((Real.sqrt t)⁻¹ • p.1, (Real.sqrt t)⁻¹ • p.2))
  have hZ' : IsCriticalSHF (ϑ + Real.log t) P Z' :=
    (Assembly.shfSymmetriesAt ϑ P Z hZ).2.2.2.1 t ht
  obtain ⟨H', hH', _hRest⟩ := Provider.criticalKPZ_main (ϑ + Real.log t) P Z' hZ'
  exact ⟨Z', H', hZ', hH', scaling_dilate_law ϑ P Z hZ H hH ht Z' hZ' H' hH' φ x⟩

end Critical2DKPZ.Extensions.ScaleLimit
