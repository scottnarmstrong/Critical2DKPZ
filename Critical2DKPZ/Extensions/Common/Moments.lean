/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.Common.Canonical
public import Critical2DKPZ.Extensions.Common.FiniteWidth
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! # All finite moments of tested critical KPZ fields

Choose one regularization width where both the regularization and its difference
from the limit have finite Lᵖ norm. Their difference is the tested KPZ limit.
-/

@[expose] public section

open MeasureTheory Filter TopologicalSpace
open scoped BoundedContinuousFunction ENNReal

namespace Critical2DKPZ.Extensions.Common

/-- Every tested critical KPZ value belongs to Lᵖ for every finite p ≥ 1 and
any bounded continuous initial condition. -/
theorem memLp_criticalKPZ_pairing (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) (h₀ : Plane →ᵇ ℝ) (φ : TestFn)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp_top : p ≠ ⊤) :
    MemLp (fun ω => H t h₀ ω φ) p P := by
  have hconv := tendsto_eLpNorm_kpzRegularized_isCriticalKPZ
    ϑ P Z hZ H hH t ht h₀ φ p hp hp_top
  have hfinite : ∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0),
      eLpNorm (fun ω => (∫ x, φ x * kpzRegularized P Z t δ h₀ x ω) -
        H t h₀ ω φ) p P < ⊤ :=
    hconv.eventually (Iio_mem_nhds ENNReal.zero_lt_top)
  have hsmall : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), δ < t :=
    (eventually_lt_nhds ht).filter_mono nhdsWithin_le_nhds
  obtain ⟨δ, hnorm, hδt, hδ⟩ :=
    (hfinite.and (hsmall.and self_mem_nhdsWithin)).exists
  have hY := memLp_kpzRegularized_pairing ϑ P Z hZ t δ ht hδ hδt h₀ φ p hp hp_top
  have hdiff : MemLp (fun ω => (∫ x, φ x * kpzRegularized P Z t δ h₀ x ω) -
      H t h₀ ω φ) p P := hnorm
  have h := hY.sub hdiff
  change MemLp (fun ω => (∫ x, φ x * kpzRegularized P Z t δ h₀ x ω) -
    ((∫ x, φ x * kpzRegularized P Z t δ h₀ x ω) - H t h₀ ω φ)) p P at h
  simpa only [sub_sub_cancel] using h

end Critical2DKPZ.Extensions.Common
