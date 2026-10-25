/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.StationaryMaximalLaw
public import Critical2DKPZ.Extensions.ScaleLimit.MaximalJointMeasurability

/-! # Averaging stationary maximal events in space -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The indicator of a radius-truncated maximal event. -/
def maximalEvent (R : ℝ) (Λ : ℝ≥0∞) (g : Plane → Ω → ℝ) (p : Plane × Ω) : ℝ≥0∞ :=
  {q : Plane × Ω | Λ < maximalFnLe R (fun z => g z q.2) q.1}.indicator (fun _ => 1) p

/-- The event indicator is jointly measurable. -/
theorem measurable_maximalEvent {g : Plane → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (R : ℝ) (Λ : ℝ≥0∞) :
    Measurable (maximalEvent R Λ g) :=
  measurable_const.indicator (measurableSet_lt measurable_const (measurable_uncurry_maximalFnLe hg R))

/-- Integrating the event indicator over samples gives its probability. -/
theorem lintegral_maximalEvent {P : Measure Ω} {g : Plane → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (R : ℝ) (Λ : ℝ≥0∞) (y : Plane) :
    (∫⁻ ω, maximalEvent R Λ g (y, ω) ∂P) =
      P {ω | Λ < maximalFnLe R (fun z => g z ω) y} := by
  have hm : MeasurableSet {ω | Λ < maximalFnLe R (fun z => g z ω) y} :=
    measurableSet_lt measurable_const (measurable_maximalFnLe hg R y)
  change (∫⁻ ω, {ω | Λ < maximalFnLe R (fun z => g z ω) y}.indicator (fun _ => 1) ω ∂P) = _
  exact lintegral_indicator_one hm

/-- Integrating over centers gives the spatial volume of the restricted event. -/
theorem setLIntegral_maximalEvent {g : Plane → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (R : ℝ) (Λ : ℝ≥0∞) (s : Set Plane) (ω : Ω) :
    (∫⁻ y in s, maximalEvent R Λ g (y, ω)) =
      volume {y | y ∈ s ∧ Λ < maximalFnLe R (fun z => g z ω) y} := by
  let M : Plane → Ω → ℝ≥0∞ := fun y ω => maximalFnLe R (fun z => g z ω) y
  have hJM : Measurable (Function.uncurry M) := measurable_uncurry_maximalFnLe hg R
  have hM : Measurable (fun y => M y ω) := hJM.of_uncurry_right
  have hm : MeasurableSet {y | Λ < maximalFnLe R (fun z => g z ω) y} :=
    measurableSet_lt measurable_const hM
  change (∫⁻ y in s, {y | Λ < maximalFnLe R (fun z => g z ω) y}.indicator (fun _ => 1) y) = _
  calc
    _ = (volume.restrict s) {y | Λ < maximalFnLe R (fun z => g z ω) y} :=
      lintegral_indicator_one hm
    _ = volume ({y | Λ < maximalFnLe R (fun z => g z ω) y} ∩ s) := Measure.restrict_apply hm
    _ = volume {y | y ∈ s ∧ Λ < maximalFnLe R (fun z => g z ω) y} := by
      apply congrArg volume
      ext y
      exact and_comm

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Spatial averaging of a stationary maximal event equals its probability at
the origin times the spatial volume. -/
theorem expected_maximalEvent_volume {g : Plane → Ω → ℝ}
    (hg : Measurable (Function.uncurry g))
    (hstat : ∀ (n : ℕ) (y : Fin n → Plane) (z : Plane),
      IdentDistrib (fun ω i => g (y i + z) ω) (fun ω i => g (y i) ω) P P)
    (hcont : ∀ y₀, TendstoInMeasure P g (𝓝 y₀) (g y₀))
    (hint : Integrable (g 0) P) (R : ℝ) (Λ : ℝ≥0∞) (s : Set Plane) :
    (∫⁻ ω, ∫⁻ y in s, maximalEvent R Λ g (y, ω) ∂volume ∂P) =
      P {ω | Λ < maximalFnLe R (fun z => g z ω) 0} * volume s := by
  rw [← lintegral_lintegral_swap (μ := volume.restrict s) (ν := P)
    (f := fun y ω => maximalEvent R Λ g (y, ω)) (measurable_maximalEvent hg R Λ).aemeasurable]
  have he (y : Plane) : (∫⁻ ω, maximalEvent R Λ g (y, ω) ∂P) =
      P {ω | Λ < maximalFnLe R (fun z => g z ω) 0} := by
    rw [lintegral_maximalEvent hg]
    exact (maximalFnLe_identDistrib hg hstat hcont hint R y).measure_mem_eq measurableSet_Ioi
  simp_rw [he]
  exact setLIntegral_const _ _

/-- Expected absolute spatial mass uses only the one-point stationary laws. -/
theorem expected_spatial_mass {g : Plane → Ω → ℝ}
    (hg : Measurable (Function.uncurry g))
    (hstat : ∀ y, IdentDistrib (g y) (g 0) P P) (s : Set Plane) :
    (∫⁻ ω, ∫⁻ z in s, ‖g z ω‖ₑ ∂volume ∂P) =
      (∫⁻ ω, ‖g 0 ω‖ₑ ∂P) * volume s := by
  rw [← lintegral_lintegral_swap (μ := volume.restrict s) (ν := P)
    (f := fun z ω => ‖g z ω‖ₑ) hg.enorm.aemeasurable]
  have he (y : Plane) : (∫⁻ ω, ‖g y ω‖ₑ ∂P) = ∫⁻ ω, ‖g 0 ω‖ₑ ∂P :=
    ((hstat y).comp measurable_enorm).lintegral_eq
  simp_rw [he]
  exact setLIntegral_const _ _

end Critical2DKPZ.Extensions.ScaleLimit

end
