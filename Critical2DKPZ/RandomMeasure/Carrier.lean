/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.Plane
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.CompactlySupported

/-! Locally finite positive Borel measures on locally compact second-countable Hausdorff spaces are Radon measures and carry the vague topology. -/

public section

open MeasureTheory
open scoped CompactlySupported

namespace Critical2DKPZ.RandomMeasure


/-- A locally finite positive measure, represented by its underlying measure and its local-finiteness property. -/
abbrev PositiveRadonMeasure (X : Type*) [TopologicalSpace X] [MeasurableSpace X] :=
  { μ : Measure X // IsLocallyFiniteMeasure μ }


/-- Positive locally finite Borel measures on the Euclidean plane. -/
abbrev PlaneRadonMeasure := PositiveRadonMeasure Critical2DKPZ.Plane

/-- Positive locally finite Borel measures on ordered pairs of Euclidean plane points. -/
abbrev PlanePairRadonMeasure :=
  PositiveRadonMeasure (Critical2DKPZ.Plane × Critical2DKPZ.Plane)

namespace PositiveRadonMeasure

/-- The underlying locally finite positive measure. -/
abbrev measure {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : PositiveRadonMeasure X) : Measure X := μ.1


end PositiveRadonMeasure

end Critical2DKPZ.RandomMeasure

end
