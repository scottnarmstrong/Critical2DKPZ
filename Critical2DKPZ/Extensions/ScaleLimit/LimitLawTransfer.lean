/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! # Changing a distributional limit to a random variable with the same law -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A limiting law can be represented on any probability space, with
measurability and equality of laws explicit. -/
theorem tendstoInDistribution_of_limit_map_eq
    {κ E Ω Ω' Ω'' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace Ω'']
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {P : Measure Ω} {Q : Measure Ω'} {R : Measure Ω''}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    {l : Filter κ} {X : κ → Ω → E} {Y : Ω' → E} {Z : Ω'' → E}
    (hX : TendstoInDistribution X l Y (fun _ => P) Q)
    (hZ : AEMeasurable Z R) (hmap : Q.map Y = R.map Z) :
    TendstoInDistribution X l Z (fun _ => P) R := by
  refine ⟨hX.forall_aemeasurable, hZ, ?_⟩
  have heq : (⟨Q.map Y, inferInstance⟩ : ProbabilityMeasure E) = ⟨R.map Z, inferInstance⟩ :=
    Subtype.ext hmap
  rw [← heq]
  exact hX.tendsto

end Critical2DKPZ.Extensions.ScaleLimit
