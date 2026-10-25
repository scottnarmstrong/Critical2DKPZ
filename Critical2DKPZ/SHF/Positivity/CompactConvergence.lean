/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Positivity.CutoffTests
import Mathlib.Tactic

/-! # Compact heat-start tests and their joint convergence -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai
open scoped BoundedContinuousFunction CompactlySupported Topology

namespace Critical2DKPZ.SHF.Positivity


/-- `IsCriticalSHF` gives joint convergence of every finite family of compact pairings. -/
theorem isCriticalSHF_compact_pairings_tendsto {ϑ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) {k : ℕ} (s t : Fin k → ℝ)
    (htimes : ∀ i, 0 ≤ s i ∧ s i < t i) (φ : Fin k → C_c(Plane × Plane, ℝ)) :
    TendstoInDistribution
      (fun N ω i => ∫ p, φ i p ∂(polymerMeasure ϑ N (s i) (t i) ω)) atTop
      (fun ω i => ∫ p, φ i p ∂(Z (s i) (t i) ω))
      (fun _ => disorderLaw) P := by
  let ψ : Fin k → C_c(Plane, ℝ) := fun _ => 0
  have hvec := hZ.2.2 k s t htimes φ ψ
  have hscalar := hvec.continuous_comp
    (g := fun v : Fin k → ℝ × ℝ => fun i => (v i).1) (by fun_prop)
  simpa only [Function.comp_def, ψ, integral_polymerMeasure] using hscalar

end Critical2DKPZ.SHF.Positivity

end
