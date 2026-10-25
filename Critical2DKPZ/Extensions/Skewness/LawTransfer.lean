/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.Convex.Function
public import Critical2DKPZ.Definitions.IsCriticalKPZ
public import Critical2DKPZ.Definitions.IsCriticalSHF
import Critical2DKPZ.Extensions.Common.Moments
import Critical2DKPZ.Provider.CriticalKPZIsEhrhardType
import Critical2DKPZ.EhrhardType.Characterization

/-! # Convex Gaussian representation and law transport for strict skewness -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.Skewness

universe u

/-- The tested flat critical KPZ field admits a nondecreasing convex Gaussian
representative, and its pairing is almost everywhere measurable. -/
theorem exists_convex_representative (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x) :
    AEMeasurable (fun ω => H t 0 ω ψ) P ∧
      ∃ h : ℝ → ℝ, Monotone h ∧ ConvexOn ℝ univ h ∧
        P.map (fun ω => H t 0 ω ψ) = (gaussianReal 0 1).map h := by
  obtain ⟨hm, he⟩ := Critical2DKPZ.Provider.criticalKPZ_isEhrhardType ϑ P Z hZ H hH t ht ψ hψ
  have hp : IsProbabilityMeasure (P.map (fun ω => H t 0 ω ψ)) := inferInstance
  exact ⟨hm, (EhrhardType.isEhrhardType_iff_exists_monotone_convex _ hp).mp he⟩

/-- Equality of laws transports all Lᵖ memberships and the third central moment. -/
theorem memLp_centralMoment_of_map_eq {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : AEMeasurable X P) {h : ℝ → ℝ} (hh : Monotone h)
    (hmap : P.map X = (gaussianReal 0 1).map h) (p : ℝ≥0∞) :
    (MemLp X p P ↔ MemLp h p (gaussianReal 0 1)) ∧
      centralMoment X 3 P = centralMoment h 3 (gaussianReal 0 1) := by
  have hd : IdentDistrib X h P (gaussianReal 0 1) := ⟨hX, hh.measurable.aemeasurable, hmap⟩
  refine ⟨hd.memLp_iff, ?_⟩
  change (∫ x, (X x - ∫ y, X y ∂P) ^ 3 ∂P) =
    ∫ x, (h x - ∫ y, h y ∂gaussianReal 0 1) ^ 3 ∂gaussianReal 0 1
  rw [hd.integral_eq]
  exact hd.comp (u := fun y : ℝ => (y - ∫ x, h x ∂gaussianReal 0 1) ^ 3) (by fun_prop) |>.integral_eq

/-- Every affine image of a standard Gaussian has its expected Gaussian law,
including zero slope. -/
theorem map_affine_gaussian (a b : ℝ) :
    (gaussianReal 0 1).map (fun x => a * x + b) =
      gaussianReal b ⟨a ^ 2, sq_nonneg a⟩ := by
  have hf : (fun x : ℝ => a * x + b) = (fun y : ℝ => y + b) ∘ (fun x : ℝ => a * x) := rfl
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_add_const]
  simp only [mul_zero, zero_add, mul_one]
  congr 1

/-- A law excluding all Gaussian distributions excludes affine representatives. -/
theorem not_affine_of_map_ne_gaussian {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {h : ℝ → ℝ} (hmap : P.map X = (gaussianReal 0 1).map h)
    (hng : ∀ (m : ℝ) (v : NNReal), P.map X ≠ gaussianReal m v) :
    ¬ ∃ a b : ℝ, 0 ≤ a ∧ ∀ x, h x = a * x + b := by
  rintro ⟨a, b, _, hh⟩
  apply hng b ⟨a ^ 2, sq_nonneg a⟩
  rw [hmap, funext hh, map_affine_gaussian]

/-- The flat tested field has a finite third absolute moment. -/
theorem memLp_three_flat (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) (ψ : TestFn) :
    MemLp (fun ω => H t 0 ω ψ) (3 : ℝ≥0∞) P := by
  exact Common.memLp_criticalKPZ_pairing ϑ P Z hZ H hH t ht 0 ψ 3
    (by norm_num) (by norm_num)


end Critical2DKPZ.Extensions.Skewness
