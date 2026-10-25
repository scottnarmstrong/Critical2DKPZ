/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.Endpoints
public import Critical2DKPZ.Gaussian.CoordinateConditioning
public import Critical2DKPZ.Gaussian.DisorderLaws
public import Critical2DKPZ.Extensions.GffTangent.GaussianSplitting
import Critical2DKPZ.Polymer.Locality
import Mathlib.Tactic

/-! # Independent parity contributions of the lattice polymer -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Critical2DKPZ.Extensions.GffTangent







/-- A finite spatial average at a fixed entrance time. -/
def finiteEntranceFluctuation (β c : ℝ) (a n : ℕ) (S : Finset Site)
    (ν : Site → ℝ) (ω : Disorder) : ℝ :=
  c * ∑ w ∈ S, ν w * (pointToPlane β a n w ω - 1)




/-- Global measurability of a finite entrance average. -/
theorem measurable_finiteEntranceFluctuation (β c : ℝ) (a n : ℕ)
    (S : Finset Site) (ν : Site → ℝ) : Measurable (finiteEntranceFluctuation β c a n S ν) := by
  unfold finiteEntranceFluctuation
  exact measurable_const.mul (Finset.measurable_sum _ fun w _ =>
    measurable_const.mul ((Polymer.measurable_pointToPlane β a n w).sub measurable_const))

/-- Translating every start and its weight by the same lattice vector gives
exact equality of laws at finite scale. -/
theorem law_finiteEntranceFluctuation_translate (β c : ℝ) (a n : ℕ)
    (S : Finset Site) (ν : Site → ℝ) (v : Site) :
    disorderLaw.map (fun ω => c * ∑ w ∈ S, ν w * (pointToPlane β a n (w + v) ω - 1)) =
      disorderLaw.map (finiteEntranceFluctuation β c a n S ν) := by
  let τ : Disorder → Disorder := fun ω p => ω (p.1, p.2 + v)
  have hτ : MeasurePreserving τ disorderLaw disorderLaw := Gaussian.measurePreserving_disorder_translation v
  have he : (fun ω => c * ∑ w ∈ S, ν w * (pointToPlane β a n (w + v) ω - 1)) =
      (finiteEntranceFluctuation β c a n S ν) ∘ τ := by
    funext ω
    simp only [finiteEntranceFluctuation, Function.comp_apply, Polymer.pointToPlane_translate, τ]
  rw [he, ← Measure.map_map (measurable_finiteEntranceFluctuation β c a n S ν) hτ.measurable, hτ.map_eq]


end Critical2DKPZ.Extensions.GffTangent
