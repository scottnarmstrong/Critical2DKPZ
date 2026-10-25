/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BoundedArrayCLT
public import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic

/-! # Bounded deterministic drifts between tight random variables

This is the tightness step in the centring lemma: a deterministic translate of
two tight sequences, up to an error vanishing in probability, must be bounded.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A deterministic difference of tight sequences is eventually bounded. The first
sequence is supplied with one uniform tail bound; the second has a Gaussian limit. -/
theorem eventually_abs_le_drift_of_tight {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X U E : ℕ → Ω → ℝ) (d : ℕ → ℝ)
    (hX : ∃ R : ℝ, 0 ≤ R ∧ ∀ n, P {ω | R < |X n ω|} ≤ (1 / 4 : ℝ≥0∞))
    (hU : TendstoInDistribution U atTop id (fun _ => P) (gaussianReal 0 1))
    (hE : TendstoInMeasure P E atTop (fun _ => 0))
    (hd : ∀ n ω, d n = X n ω - U n ω + E n ω) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ n in atTop, |d n| ≤ D := by
  obtain ⟨R, hR, hXR⟩ := hX
  have htight : IsTightMeasureSet (Set.range (fun n => P.map (U n))) :=
    isTightMeasureSet_of_tendsto_charFun continuous_charFun.continuousAt (fun t => hU.tendsto_charFun t)
  obtain ⟨K, hK, hKt⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight
      (1 / 4) (by norm_num)
  obtain ⟨M, hM, hKM⟩ := hK.isBounded.subset_closedBall_lt 0 0
  have hUM (n : ℕ) : P {ω | M < |U n ω|} ≤ (1 / 4 : ℝ≥0∞) := by
    calc
      _ ≤ (P.map (U n)) Kᶜ := by
        rw [Measure.map_apply_of_aemeasurable (hU.forall_aemeasurable n)
          hK.isClosed.measurableSet.compl]
        apply measure_mono
        intro ω hω hωK
        have hh := hKM hωK
        have hh' : |U n ω| ≤ M := by
          simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hh
        exact (not_le_of_gt hω) hh'
      _ ≤ 1 / 4 := hKt _ ⟨n, rfl⟩
  have hEtail : ∀ᶠ n in atTop, P {ω | 1 < |E n ω|} ≤ (1 / 4 : ℝ≥0∞) := by
    have he := (tendstoInMeasure_iff_norm.mp hE) 1 zero_lt_one
    filter_upwards [he.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1 / 4))]
      with n hn
    apply le_trans (measure_mono (t := {ω | 1 ≤ ‖E n ω - 0‖}) ?_) hn.le
    intro ω hω
    change 1 < |E n ω| at hω
    change 1 ≤ ‖E n ω - 0‖
    simpa only [sub_zero, Real.norm_eq_abs] using hω.le
  refine ⟨R + M + 1, by linarith, ?_⟩
  filter_upwards [hEtail] with n hn
  have hgood : ∃ ω, |X n ω| ≤ R ∧ |U n ω| ≤ M ∧ |E n ω| ≤ 1 := by
    by_contra hno
    have hcover : Set.univ ⊆
        ({ω | R < |X n ω|} ∪ {ω | M < |U n ω|}) ∪ {ω | 1 < |E n ω|} := by
      intro ω _
      by_cases hx : |X n ω| ≤ R
      · by_cases hu : |U n ω| ≤ M
        · have he : 1 < |E n ω| := lt_of_not_ge (fun he => hno ⟨ω, hx, hu, he⟩)
          exact Or.inr he
        · exact Or.inl (Or.inr (lt_of_not_ge hu))
      · exact Or.inl (Or.inl (lt_of_not_ge hx))
    have hsmall : P Set.univ ≤ (3 / 4 : ℝ≥0∞) := by
      calc
        _ ≤ P (({ω | R < |X n ω|} ∪ {ω | M < |U n ω|}) ∪ {ω | 1 < |E n ω|}) :=
          measure_mono hcover
        _ ≤ (P {ω | R < |X n ω|} + P {ω | M < |U n ω|}) + P {ω | 1 < |E n ω|} :=
          (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
        _ ≤ (1 / 4 + 1 / 4) + 1 / 4 := add_le_add (add_le_add (hXR n) (hUM n)) hn
        _ = 3 / 4 := by
          rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same]
          norm_num
    have hfalse : ¬ (1 : ℝ≥0∞) ≤ 3 / 4 := by
      apply not_le.mpr
      rw [ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      norm_num
    exact hfalse (by simpa only [measure_univ] using hsmall)
  obtain ⟨ω, hx, hu, he⟩ := hgood
  rw [hd n ω]
  calc
    |X n ω - U n ω + E n ω| ≤ |X n ω - U n ω| + |E n ω| := abs_add_le _ _
    _ ≤ (|X n ω| + |U n ω|) + |E n ω| := add_le_add (abs_sub _ _) le_rfl
    _ ≤ R + M + 1 := by linarith

end Critical2DKPZ.Extensions.ScaleLimit
