/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.HardyLittlewood
import Mathlib.MeasureTheory.Measure.Prod

/-! # Countable radii and measurability of the maximal function

A slight enlargement of a witnessing ball reduces the maximal function to a
countable supremum. This works for every sample, including samples that are
not locally integrable, so the conclusion is measurability rather than only
almost everywhere measurability.
-/

public section

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A strict average inequality persists under sufficiently small enlargements. -/
theorem ballAverage_lt_eventually_right {g : Plane → ℝ} {y : Plane} {r : ℝ}
    {Λ : ℝ≥0∞} (hΛ : Λ < ballAverage g y r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, r ≤ s → s < r + ε → Λ < ballAverage g y s := by
  let I := ∫⁻ z in ball y r, ‖g z‖ₑ
  have hc : ContinuousAt (fun s : ℝ => (volume (ball y s))⁻¹ * I) r :=
    ENNReal.Tendsto.mul_const (continuous_volume_ball y).fun_inv.continuousAt
      (Or.inl (ENNReal.inv_ne_zero.mpr measure_ball_lt_top.ne))
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp
    (hc.eventually (Ioi_mem_nhds hΛ))
  refine ⟨ε, hε, fun s hrs hs => ?_⟩
  have hd : dist s r < ε := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hrs)]
    linarith only [hs]
  exact (he hd).trans_le (mul_le_mul' le_rfl (lintegral_mono_set (ball_subset_ball hrs)))

/-- Every strict witness can be replaced by a rational, slightly larger radius. -/
theorem exists_rat_radius_of_lt_average {g : Plane → ℝ} {y : Plane} {r : ℝ}
    (hr : 0 < r) {Λ : ℝ≥0∞} (hΛ : Λ < ballAverage g y r) :
    ∃ q : ℚ, 0 < q ∧ Λ < ballAverage g y q := by
  obtain ⟨ε, hε, he⟩ := ballAverage_lt_eventually_right hΛ
  obtain ⟨q, hrq, hqr⟩ := exists_rat_btwn (lt_add_of_pos_right r hε)
  refine ⟨q, ?_, he q hrq.le hqr⟩
  exact_mod_cast hr.trans hrq

/-- The full maximal function is a supremum over positive rational radii. -/
theorem maximalFn_eq_iSup_rat (g : Plane → ℝ) (y : Plane) :
    maximalFn g y = ⨆ q : {q : ℚ // 0 < q}, ballAverage g y (q : ℚ) := by
  apply le_antisymm
  · apply iSup_le
    intro r
    apply le_of_forall_lt
    intro Λ hΛ
    obtain ⟨q, hq, hh⟩ := exists_rat_radius_of_lt_average r.2 hΛ
    exact hh.trans_le (le_iSup (fun q : {q : ℚ // 0 < q} => ballAverage g y (q : ℚ)) ⟨q, hq⟩)
  · apply iSup_le
    intro q
    have hq : (0 : ℝ) < (q : ℚ) := by exact_mod_cast q.2
    exact le_iSup_of_le ⟨(q : ℚ), hq⟩ le_rfl

/-- Rational witnesses can also respect a strict upper bound on the radius. -/
theorem exists_rat_radius_lt_of_lt_average {g : Plane → ℝ} {y : Plane} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) {Λ : ℝ≥0∞} (hΛ : Λ < ballAverage g y r) :
    ∃ q : ℚ, 0 < q ∧ (q : ℝ) < R ∧ Λ < ballAverage g y q := by
  obtain ⟨ε, hε, he⟩ := ballAverage_lt_eventually_right hΛ
  have hδ : 0 < min ε (R - r) := lt_min hε (sub_pos.mpr hrR)
  obtain ⟨q, hrq, hqr⟩ := exists_rat_btwn (lt_add_of_pos_right r hδ)
  have hqε : (q : ℝ) < r + ε :=
    hqr.trans_le (add_le_add_right (min_le_left _ _) _)
  have hqR : (q : ℝ) < R := by
    have hh := hqr.trans_le (add_le_add_right (min_le_right ε (R - r)) r)
    linarith only [hh]
  refine ⟨q, ?_, hqR, he q hrq.le hqε⟩
  exact_mod_cast hr.trans hrq

/-- Countable description of a bounded maximal function, retaining the endpoint.
No local integrability assumption is needed. -/
theorem maximalFnLe_eq_iSup_rat (R : ℝ) (g : Plane → ℝ) (y : Plane) :
    maximalFnLe R g y =
      (⨆ q : {q : ℚ // 0 < q ∧ (q : ℝ) < R}, ballAverage g y (q : ℚ)) ⊔
        (if 0 < R then ballAverage g y R else 0) := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro r
    rcases r.2.2.eq_or_lt with hr | hr
    · have hR : 0 < R := hr ▸ r.2.1
      rw [hr, ite_eq_left hR]
      exact le_sup_right
    · apply le_trans (b := ⨆ q : {q : ℚ // 0 < q ∧ (q : ℝ) < R},
        ballAverage g y (q : ℚ)) _ le_sup_left
      apply le_of_forall_lt
      intro Λ hΛ
      obtain ⟨q, hq, hqR, hh⟩ := exists_rat_radius_lt_of_lt_average r.2.1 hr hΛ
      exact hh.trans_le (le_iSup (fun q : {q : ℚ // 0 < q ∧ (q : ℝ) < R} =>
        ballAverage g y (q : ℚ)) ⟨q, hq, hqR⟩)
  · apply sup_le
    · apply iSup_le
      intro q
      have hq : (0 : ℝ) < (q : ℚ) := by exact_mod_cast q.2.1
      exact le_iSup_of_le ⟨(q : ℚ), hq, q.2.2.le⟩ le_rfl
    · split_ifs with hR
      · exact le_iSup_of_le ⟨R, hR, le_rfl⟩ le_rfl
      · exact bot_le

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Ball averages of a jointly measurable field are measurable random variables. -/
theorem measurable_ballAverage {g : Plane → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (y : Plane) (r : ℝ) :
    Measurable (fun ω => ballAverage (fun z => g z ω) y r) := by
  have hm : Measurable (fun p : Ω × Plane => ‖g p.2 p.1‖ₑ) :=
    (hg.comp measurable_swap).enorm
  exact measurable_const.mul (hm.lintegral_prod_right' (ν := volume.restrict (ball y r)))

/-- The maximal random variable is measurable, including on exceptional samples. -/
theorem measurable_maximalFn {g : Plane → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (y : Plane) :
    Measurable (fun ω => maximalFn (fun z => g z ω) y) := by
  simp only [maximalFn_eq_iSup_rat]
  exact Measurable.iSup fun q => measurable_ballAverage hg y (q : ℚ)

/-- The radius-truncated maximal random variable is measurable as well. -/
theorem measurable_maximalFnLe {g : Plane → Ω → ℝ}
    (hg : Measurable (Function.uncurry g)) (R : ℝ) (y : Plane) :
    Measurable (fun ω => maximalFnLe R (fun z => g z ω) y) := by
  classical
  simp only [maximalFnLe_eq_iSup_rat]
  have hq : Measurable (fun ω =>
      ⨆ q : {q : ℚ // 0 < q ∧ (q : ℝ) < R}, ballAverage (fun z => g z ω) y (q : ℚ)) :=
    Measurable.iSup fun q => measurable_ballAverage hg y (q : ℚ)
  have he : Measurable (fun ω => if 0 < R then ballAverage (fun z => g z ω) y R else 0) := by
    split_ifs
    · exact measurable_ballAverage hg y R
    · exact measurable_const
  exact hq.max he

end Critical2DKPZ.Extensions.ScaleLimit

end
