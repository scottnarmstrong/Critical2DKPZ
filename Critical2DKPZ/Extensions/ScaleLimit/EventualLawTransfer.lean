/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! # Transfer of distributional limits under eventual equality of laws

Measurability is retained at every index, including indices outside the tail on
which the two laws agree.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Eventual equality of laws preserves a distributional limit. -/
theorem tendstoInDistribution_congr_of_eventually_map_eq
    {ι E Ω Ω' Ω'' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace Ω''] [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Q : Measure Ω''} [IsProbabilityMeasure Q]
    {μ : Measure Ω'} [IsProbabilityMeasure μ] {l : Filter ι}
    {X : ι → Ω → E} {Y : ι → Ω'' → E} {Z : Ω' → E}
    (hX : ∀ i, AEMeasurable (X i) P) (hY : ∀ i, AEMeasurable (Y i) Q)
    (hZ : AEMeasurable Z μ)
    (hmap : ∀ᶠ i in l, P.map (X i) = Q.map (Y i)) :
    TendstoInDistribution X l Z (fun _ => P) μ ↔
      TendstoInDistribution Y l Z (fun _ => Q) μ := by
  have heq : (fun i => (⟨P.map (X i), inferInstance⟩ : ProbabilityMeasure E)) =ᶠ[l]
      fun i => (⟨Q.map (Y i), inferInstance⟩ : ProbabilityMeasure E) :=
    hmap.mono (fun _ h => Subtype.ext h)
  exact ⟨fun h => ⟨hY, hZ, h.tendsto.congr' heq⟩,
    fun h => ⟨hX, hZ, h.tendsto.congr' heq.symm⟩⟩

end Critical2DKPZ.Extensions.ScaleLimit
