/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.MaximalMeasurability
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Joint measurability of spatial maximal fields -/

public section

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Ball averages are jointly measurable in their center and the random input. -/
theorem measurable_uncurry_ballAverage {g : Plane → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (r : ℝ) :
    Measurable (fun p : Plane × Ω => ballAverage (fun z => g z p.2) p.1 r) := by
  classical
  have hm : Measurable (fun q : (Plane × Ω) × Plane => ‖g q.2 q.1.2‖ₑ) :=
    (hg.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).enorm
  have hs : MeasurableSet {q : (Plane × Ω) × Plane | dist q.2 q.1.1 < r} :=
    measurableSet_lt (measurable_snd.dist (measurable_fst.comp measurable_fst)) measurable_const
  have hlin := (hm.indicator hs).lintegral_prod_right' (ν := (volume : Measure Plane))
  have heq : (fun p : Plane × Ω => ballAverage (fun z => g z p.2) p.1 r) =
      fun p => (volume (ball (0 : Plane) r))⁻¹ *
        ∫⁻ z, {q : (Plane × Ω) × Plane | dist q.2 q.1.1 < r}.indicator
          (fun q => ‖g q.2 q.1.2‖ₑ) (p, z) := by
    funext p
    dsimp [ballAverage]
    rw [volume.addHaar_ball_center p.1 r]
    congr 1
    rw [← lintegral_indicator measurableSet_ball]
    apply lintegral_congr_ae
    exact Eventually.of_forall fun z => by
      change (ball p.1 r).indicator (fun z => ‖g z p.2‖ₑ) z =
        {q : (Plane × Ω) × Plane | dist q.2 q.1.1 < r}.indicator
          (fun q => ‖g q.2 q.1.2‖ₑ) (p, z)
      by_cases hz : z ∈ ball p.1 r
      · rw [indicator_of_mem hz, indicator_of_mem (show (p, z) ∈
          {q : (Plane × Ω) × Plane | dist q.2 q.1.1 < r} from hz)]
      · rw [indicator_of_notMem hz, indicator_of_notMem (show (p, z) ∉
          {q : (Plane × Ω) × Plane | dist q.2 q.1.1 < r} from hz)]
  rw [heq]
  exact measurable_const.mul hlin


/-- Joint measurability also holds with a bounded set of allowed radii. -/
theorem measurable_uncurry_maximalFnLe {g : Plane → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (R : ℝ) :
    Measurable (fun p : Plane × Ω => maximalFnLe R (fun z => g z p.2) p.1) := by
  classical
  simp only [maximalFnLe_eq_iSup_rat]
  have hq : Measurable (fun p : Plane × Ω =>
      ⨆ q : {q : ℚ // 0 < q ∧ (q : ℝ) < R}, ballAverage (fun z => g z p.2) p.1 (q : ℚ)) :=
    Measurable.iSup fun q => measurable_uncurry_ballAverage hg (q : ℚ)
  have he : Measurable (fun p : Plane × Ω =>
      if 0 < R then ballAverage (fun z => g z p.2) p.1 R else 0) := by
    split_ifs
    · exact measurable_uncurry_ballAverage hg R
    · exact measurable_const
  exact hq.max he

end Critical2DKPZ.Extensions.ScaleLimit

end
