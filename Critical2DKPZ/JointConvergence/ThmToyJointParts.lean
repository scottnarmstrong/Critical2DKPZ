/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.JointConvergence.ThmToyJointConvergence
public import Critical2DKPZ.RandomMeasure.PlanePairInterface
import Critical2DKPZ.Smoothing.Measurability
import Mathlib.Tactic

/-! # Measurability of tested reversed lattice fields -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit
open scoped BoundedContinuousFunction ENNReal Topology

namespace Critical2DKPZ.JointConvergence

/-- The tested reversed lattice fields are measurable under the disorder law. -/
theorem aemeasurable_integral_kpzLatticeReversed (ϑ : ℝ) (N : ℕ) (t T : ℝ)
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn) :
    AEMeasurable (fun ω => ∫ x, φ x * kpzLatticeReversed ϑ N t T h₀ x ω)
      disorderLaw := by
  let β : ℝ := criticalBeta ϑ N
  let a : ℕ := evenCeil (N * t)
  let b : ℕ := evenCeil (N * T)
  let f : Site → ℝ := cellAverage N fun y => Real.exp (h₀ y)
  let ν : Disorder × Plane → Site → ℝ := fun q w =>
    if w = latticePoint N q.2 then 1 else 0
  have hν (w : Site) : Measurable (fun q : Disorder × Plane => ν q w) := by
    dsimp [ν]
    exact Measurable.ite (measurableSet_eq_fun measurable_const
      ((measurable_latticePoint N).comp measurable_snd)) measurable_const measurable_const
  have hξ : Measurable (fun q : Disorder × Plane => q.1) := measurable_fst
  have hraw : Measurable (fun q : Disorder × Plane =>
      kpzLatticeReversed ϑ N t T h₀ q.2 q.1) := by
    have h := Smoothing.measurable_centered_profile_log_param β a b f hν hξ
    simpa only [kpzLatticeReversed, β, a, b, f, ν] using h
  have hφ : Measurable (φ : Plane → ℝ) := φ.continuous.measurable
  have hG : Measurable (fun q : Disorder × Plane =>
      φ q.2 * kpzLatticeReversed ϑ N t T h₀ q.2 q.1) :=
    (hφ.comp measurable_snd).mul hraw
  exact hG.stronglyMeasurable.integral_prod_right'.aemeasurable

end Critical2DKPZ.JointConvergence

end
