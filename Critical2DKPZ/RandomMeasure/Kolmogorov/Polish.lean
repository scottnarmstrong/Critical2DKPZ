/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.RandomMeasure.Kolmogorov.CompactCylinders
public import Critical2DKPZ.RandomMeasure.Kolmogorov.CompactContent
public import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
public import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent

/-! Every projectively consistent family of finite-dimensional probability laws on a fixed Polish state space extends to a probability measure on the product σ-algebra, for an arbitrary index set. -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.RandomMeasure.Kolmogorov

/-- Compact finite-dimensional inner approximation lifts to the cylinder content. -/
theorem projectiveFamilyContent_inner_compact {ι X : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (P : ∀ J : Finset ι, Measure (J → X)) [∀ J, IsProbabilityMeasure (P J)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : ι => X) P)
    (s : Set (ι → X)) (hs : s ∈ measurableCylinders (fun _ : ι => X))
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ k ∈ closedCompactCylinders (fun _ : ι => X), k ⊆ s ∧
      projectiveFamilyContent hP (s \ k) ≤ ε := by
  obtain ⟨J, S, hS, rfl⟩ := (mem_measurableCylinders s).mp hs
  obtain ⟨K, hKS, hK, herror⟩ :=
    hS.exists_isCompact_sdiff_lt (measure_ne_top (P J) S) hε.ne'
  refine ⟨cylinder J K, cylinder_mem_closedCompactCylinders (X := fun _ : ι => X) J K hK.isClosed hK,
    (fun x hx => hKS hx), ?_⟩
  rw [sdiff_cylinder_same, projectiveFamilyContent_cylinder hP (hS.diff hK.isClosed.measurableSet)]
  exact herror.le

/-- The projective cylinder content of Polish probability laws is countably subadditive. -/
theorem projectiveFamilyContent_isSigmaSubadditive_polish {ι X : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (P : ∀ J : Finset ι, Measure (J → X)) [∀ J, IsProbabilityMeasure (P J)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : ι => X) P) :
    (projectiveFamilyContent hP).IsSigmaSubadditive := by
  apply isSigmaSubadditive_of_compactSystem isSetRing_measurableCylinders
    isCompactSystem_closedCompactCylinders
    (fun s hs => mem_measurableCylinders_of_mem_closedCompactCylinders hs)
    (projectiveFamilyContent hP) (fun s _ => projectiveFamilyContent_ne_top hP)
  exact projectiveFamilyContent_inner_compact P hP

/-- A projectively consistent family of finite-dimensional probability laws on a fixed Polish space has a probability extension to an arbitrarily indexed product. -/
theorem exists_isProjectiveLimit_polish {ι X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] (P : ∀ J : Finset ι, Measure (J → X))
    [∀ J, IsProbabilityMeasure (P J)] (hP : IsProjectiveMeasureFamily (α := fun _ : ι => X) P) :
    ∃ μ : Measure (ι → X), IsProbabilityMeasure μ ∧ IsProjectiveLimit (α := fun _ : ι => X) μ P := by
  have hsub := projectiveFamilyContent_isSigmaSubadditive_polish P hP
  have hgen : (inferInstance : MeasurableSpace (ι → X)) =
      MeasurableSpace.generateFrom (measurableCylinders (fun _ : ι => X)) :=
    generateFrom_measurableCylinders.symm
  let μ : Measure (ι → X) := (projectiveFamilyContent hP).measure
    isSetSemiring_measurableCylinders hgen.le hsub
  have hμcylinder (J : Finset ι) (S : Set (J → X)) (hS : MeasurableSet S) :
      μ (cylinder J S) = P J S := by
    change (projectiveFamilyContent hP).measure isSetSemiring_measurableCylinders hgen.le hsub
      (cylinder J S) = P J S
    rw [AddContent.measure_eq _ _ hgen hsub (cylinder_mem_measurableCylinders J S hS),
      projectiveFamilyContent_cylinder hP hS]
  have hlimit : IsProjectiveLimit (α := fun _ : ι => X) μ P := by
    intro J
    apply Measure.ext
    intro S hS
    rw [Measure.map_apply J.measurable_restrict hS]
    exact hμcylinder J S hS
  exact ⟨μ, hlimit.isProbabilityMeasure, hlimit⟩

end Critical2DKPZ.RandomMeasure.Kolmogorov

end
