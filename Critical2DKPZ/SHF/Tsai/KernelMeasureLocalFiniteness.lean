/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.KernelMeasureRectangles

/-! # Local finiteness of positive form-bounded kernel measures

Closed endpoint balls have finite volume, and the indicator form estimate
makes their product have finite kernel mass. These products are neighborhoods
of every endpoint pair, so the actual kernel measure is locally finite.
-/

@[expose] public noncomputable section

open MeasureTheory Metric
open scoped ENNReal Topology
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- A measurable configuration kernel with a finite form bound defines a locally finite measure. -/
theorem locallyFinite_kernelMeasure {n : ℕ}
    {K : Configuration n → Configuration n → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hF : FormBound volume volume K c) :
    IsLocallyFiniteMeasure (volume.withDensity (Function.uncurry K)) := by
  constructor
  intro q
  refine ⟨closedBall q.1 1 ×ˢ closedBall q.2 1, ?_, ?_⟩
  · rw [nhds_prod_eq]
    exact Filter.prod_mem_prod (closedBall_mem_nhds q.1 (by norm_num))
      (closedBall_mem_nhds q.2 (by norm_num))
  · exact kernelMeasure_rectangle_lt_top hK hc hF measurableSet_closedBall measurableSet_closedBall
      (isCompact_closedBall q.1 1).measure_lt_top (isCompact_closedBall q.2 1).measure_lt_top

end Critical2DKPZ.SHF.Tsai

end
