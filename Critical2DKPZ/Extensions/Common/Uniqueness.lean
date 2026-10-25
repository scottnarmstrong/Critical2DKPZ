/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.IsCriticalKPZ

/-! # Uniqueness of tested critical KPZ limits

Limits in probability of the same regularisations agree almost everywhere, separately
for each positive time, initial condition and test function.
-/

@[expose] public section

open MeasureTheory Filter TopologicalSpace
open scoped BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.Common

/-- Two critical KPZ fields over the same flow have a.e. equal tested values. -/
theorem ae_eq_of_isCriticalKPZ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (H H' : ℝ → (Plane →ᵇ ℝ) → Ω → Distr)
    (hH : IsCriticalKPZ P Z H) (hH' : IsCriticalKPZ P Z H')
    (t : ℝ) (ht : 0 < t) (h₀ : Plane →ᵇ ℝ) (φ : TestFn) :
    (fun ω => H t h₀ ω φ) =ᵐ[P] (fun ω => H' t h₀ ω φ) := by
  exact tendstoInMeasure_ae_unique (hH t ht h₀ φ) (hH' t ht h₀ φ)


end Critical2DKPZ.Extensions.Common
