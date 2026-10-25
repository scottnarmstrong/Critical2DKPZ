/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily

/-! # Scalar increment limits from the Brownian finite-dimensional family -/

public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Projecting a finite-dimensional Brownian limit to the difference of two
coordinates gives the centered Gaussian with the exact increment variance. -/
theorem brownian_increment_limit {ι Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {l : Filter ι}
    (I : Finset ℝ≥0) (s t : I) {X : ι → Ω → I → ℝ}
    (h : TendstoInDistribution X l id (fun _ => P) (BrownianReal.projectiveFamily I)) :
    TendstoInDistribution (fun i ω => X i ω s - X i ω t) l id (fun _ => P)
      (gaussianReal 0 (nndist s.1 t.1)) := by
  have hg : Continuous (fun p : I → ℝ => p s - p t) :=
    (continuous_apply s).sub (continuous_apply t)
  have hc := h.continuous_comp hg
  have hmap := (BrownianReal.measurePreserving_eval_sub_eval_projectiveFamily I s t).map_eq
  refine ⟨hc.forall_aemeasurable, aemeasurable_id, ?_⟩
  simpa only [Measure.map_id, hmap, Function.comp_def, id_eq] using hc.tendsto

/-- Projecting to a single positive-time coordinate gives its centered Gaussian law. -/
theorem brownian_coordinate_limit {ι Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {l : Filter ι}
    (I : Finset ℝ≥0) (s : I) {X : ι → Ω → I → ℝ}
    (h : TendstoInDistribution X l id (fun _ => P) (BrownianReal.projectiveFamily I)) :
    TendstoInDistribution (fun i ω => X i ω s) l id (fun _ => P)
      (gaussianReal 0 s.1) := by
  have hc := h.continuous_comp (continuous_apply s)
  have hmap := (BrownianReal.measurePreserving_eval_projectiveFamily s).map_eq
  refine ⟨hc.forall_aemeasurable, aemeasurable_id, ?_⟩
  simpa only [Measure.map_id, hmap, Function.comp_def, id_eq] using hc.tendsto

end Critical2DKPZ.Extensions.ScaleLimit
