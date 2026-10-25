/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Limit.FirstMoment
import Mathlib.MeasureTheory.Measure.Prod

/-! # Measurability of the polymer random measure -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Critical2DKPZ.SHF.Limit

/-- At each fixed pair of times, the polymer measure is a measurable random measure. -/
theorem measurable_polymerMeasure (ϑ : ℝ) (N : ℕ) (s t : ℝ) :
    Measurable (polymerMeasure ϑ N s t) := by
  classical
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have hpair : Measurable (fun q : (Plane × Plane) × Disorder =>
      rescaledP2P ϑ N s t q.1 q.2) :=
    SHF.Moments.measurable_uncurry_rescaledP2P ϑ N s t
  have hres : Measurable (fun q : Disorder × (Plane × Plane) =>
      rescaledP2P ϑ N s t q.2 q.1) := measurable_swap_iff.mpr hpair
  have hset : MeasurableSet {q : Disorder × (Plane × Plane) | q.2 ∈ A} :=
    hA.preimage measurable_snd
  have hdens : Measurable (fun q : Disorder × (Plane × Plane) =>
      if q.2 ∈ A then ENNReal.ofReal (rescaledP2P ϑ N s t q.2 q.1) else 0) :=
    Measurable.ite hset (ENNReal.measurable_ofReal.comp hres) measurable_const
  have hlin : Measurable (fun ω : Disorder => ∫⁻ p : Plane × Plane,
      (if p ∈ A then ENNReal.ofReal (rescaledP2P ϑ N s t p ω) else 0)) :=
    hdens.lintegral_prod_right' (ν := (volume : Measure (Plane × Plane)))
  have hEq : (fun ω : Disorder => polymerMeasure ϑ N s t ω A) =
      fun ω => ∫⁻ p : Plane × Plane,
        (if p ∈ A then ENNReal.ofReal (rescaledP2P ϑ N s t p ω) else 0) := by
    funext ω
    simp only [polymerMeasure, withDensity_apply _ hA]
    rw [← lintegral_indicator hA]
    rfl
  rw [hEq]
  exact hlin

end Critical2DKPZ.SHF.Limit

end
