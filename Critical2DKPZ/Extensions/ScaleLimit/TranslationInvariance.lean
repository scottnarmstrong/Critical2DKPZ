/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.TestFnDilate
public import Critical2DKPZ.Definitions.TestFnCompAffine
public import Critical2DKPZ.Definitions.IsCriticalKPZ
public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Mathlib.Probability.IdentDistrib
import Critical2DKPZ.Extensions.ScaleLimit.KPZSpectralData
import Mathlib.Tactic

/-! # Translation invariance of finite families of flat KPZ tests -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction
namespace Critical2DKPZ.Extensions.ScaleLimit


/-- Every finite family of flat critical KPZ pairings is translation invariant in law. -/
theorem identDistrib_kpz_translate (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {t : ℝ} (ht : 0 < t) (n : ℕ) (f : Fin n → TestFn) (z : Plane) :
    IdentDistrib (fun ω i => H t 0 ω ((f i).dilate 1 z)) (fun ω i => H t 0 ω (f i)) P P := by
  exact criticalKPZ_stationary ϑ P Z hZ H hH t ht n f z

end Critical2DKPZ.Extensions.ScaleLimit
