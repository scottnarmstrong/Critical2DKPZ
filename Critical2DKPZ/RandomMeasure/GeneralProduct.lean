/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.RandomMeasure.GeneralPolish
public import Critical2DKPZ.RandomMeasure.GeneralRandom
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Topology.Metrizable.CompletelyMetrizable

/-! A sequence of Borel probability laws on a countable product of copies of a Hausdorff space is tight if its coordinate marginals are tight. In a Polish space, every tight sequence of probability laws has a weakly convergent subsequence. -/

public section

open MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology

noncomputable section

set_option linter.style.haveILetI false

namespace Critical2DKPZ.RandomMeasure

/-- A sequence of probability laws on a countable product is tight if each coordinate sequence of marginal laws is tight. -/
theorem isTightMeasureSet_range_of_tight_coordinates {ι X : Type*}
    [Countable ι] [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
    [BorelSpace X]
    (P : ℕ → ProbabilityMeasure (ι → X))
    (hcoord : ∀ i : ι, IsTightMeasureSet (Set.range fun n : ℕ =>
      ((P n).map (fun f => f i) : Measure X))) :
    IsTightMeasureSet (Set.range fun n : ℕ => (P n : Measure (ι → X))) := by
  classical
  letI : Countable ι := ‹Countable ι›
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  let δ : ℝ≥0∞ := min ε 1
  have hδpos : 0 < δ := lt_min hε zero_lt_one
  have hδtop : δ < ∞ := lt_of_le_of_lt (min_le_right _ _) (by simp)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδRpos : 0 < δ.toReal := ENNReal.toReal_pos hδpos.ne' hδtop.ne
  obtain ⟨w, hw0, hwfin⟩ :=
    Set.Countable.exists_pos_forall_sum_le
      (Set.countable_univ : (Set.univ : Set ι).Countable) hδRpos
  have hwbudget : (∑' i : ι, ENNReal.ofReal (w i)) ≤ ENNReal.ofReal δ.toReal := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi => (hw0 i).le)]
    exact ENNReal.ofReal_le_ofReal (hwfin s (by intro i hi; simp))
  have hcoordCompact (i : ι) :
      ∃ C : Set X, IsCompact C ∧ ∀ n : ℕ,
        ((P n).map (fun f => f i) : Measure X) (Cᶜ) ≤ ENNReal.ofReal (w i) := by
    have htight := hcoord i
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight
    obtain ⟨C, hC, htail⟩ :=
      htight (ENNReal.ofReal (w i)) (ENNReal.ofReal_pos.mpr (hw0 i))
    exact ⟨C, hC, fun n => htail _ ⟨n, rfl⟩⟩
  choose C hCcompact hCtail using hcoordCompact
  let K : Set (ι → X) := {f | ∀ i, f i ∈ C i}
  have hKcompact : IsCompact K := by
    change IsCompact {f : ∀ i, X | ∀ i, f i ∈ C i}
    exact isCompact_pi_infinite hCcompact
  have hbad (n : ℕ) : (P n : Measure (ι → X)) (Kᶜ) ≤ δ := by
    have hcover : Kᶜ ⊆ ⋃ i : ι, {f : ι → X | f i ∉ C i} := by
      intro f hf
      change ¬ (∀ i : ι, f i ∈ C i) at hf
      push Not at hf
      rcases hf with ⟨i, hi⟩
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    have hbadCoord (i : ι) :
        (P n : Measure (ι → X)) {f : ι → X | f i ∉ C i} ≤ ENNReal.ofReal (w i) := by
      have hclosed : IsClosed (C i) := (hCcompact i).isClosed
      have hpreimage : {f : ι → X | f i ∉ C i} =
          (fun f : ι → X => f i) ⁻¹' (C i)ᶜ := by
        ext f
        rfl
      have hmap :
          (P n : Measure (ι → X)) {f : ι → X | f i ∉ C i} =
            ((P n).map (fun f => f i) : Measure X) ((C i)ᶜ) := by
        rw [hpreimage, ← Measure.map_apply (measurable_pi_apply i)
          (hclosed.measurableSet.compl)]
        rfl
      rw [hmap]
      exact hCtail i n
    calc
      (P n : Measure (ι → X)) (Kᶜ) ≤
          (P n : Measure (ι → X)) (⋃ i : ι, {f : ι → X | f i ∉ C i}) :=
        measure_mono hcover
      _ ≤ ∑' i : ι, (P n : Measure (ι → X)) {f : ι → X | f i ∉ C i} :=
        measure_iUnion_le _
      _ ≤ ∑' i : ι, ENNReal.ofReal (w i) := ENNReal.tsum_le_tsum hbadCoord
      _ ≤ ENNReal.ofReal δ.toReal := hwbudget
      _ = δ := ENNReal.ofReal_toReal hδtop.ne
  refine ⟨K, hKcompact, ?_⟩
  rintro μ ⟨n, rfl⟩
  exact (hbad n).trans hδε

/-- Tight laws on a Polish space have a weakly convergent subsequence. -/
theorem exists_subseq_tendsto_of_tight_probability_laws {X : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [OpensMeasurableSpace X] [PolishSpace X]
    (P : ℕ → ProbabilityMeasure X)
    (hP : IsTightMeasureSet (Set.range fun n : ℕ => (P n : Measure X))) :
    ∃ φ : ℕ → ℕ, ∃ Plim : ProbabilityMeasure X,
      StrictMono φ ∧ Tendsto (fun n => P (φ n)) atTop (𝓝 Plim) := by
  letI : IsCompletelyMetrizableSpace X := inferInstance
  letI : PseudoMetrizableSpace X := inferInstance
  letI : SeparableSpace X := inferInstance
  letI : MetrizableSpace (ProbabilityMeasure X) := inferInstance
  have hset : {((μ : ProbabilityMeasure X) : Measure X) |
      μ ∈ Set.range P} = Set.range fun n : ℕ => (P n : Measure X) := by
    ext μ
    simp
  have hTight : IsTightMeasureSet
      {((μ : ProbabilityMeasure X) : Measure X) | μ ∈ Set.range P} := by
    rw [hset]
    exact hP
  have hcompact := _root_.isCompact_closure_of_isTightMeasureSet hTight
  have hseq : IsSeqCompact (closure (Set.range P)) := hcompact.isSeqCompact
  have hmem : ∀ n, P n ∈ closure (Set.range P) :=
    fun n => subset_closure ⟨n, rfl⟩
  obtain ⟨Plim, _, φ, hφ, hlim⟩ := hseq hmem
  exact ⟨φ, Plim, hφ, hlim⟩

/-- A reindexed tight sequence of laws on a Polish space has a further
weakly convergent subsequence. -/
theorem exists_subseq_tendsto_of_tight_reindexing_probability_laws {X : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [OpensMeasurableSpace X] [PolishSpace X]
    (P : ℕ → ProbabilityMeasure X)
    (hP : IsTightMeasureSet (Set.range fun n : ℕ => (P n : Measure X)))
    (ψ : ℕ → ℕ) :
    ∃ φ : ℕ → ℕ, ∃ Plim : ProbabilityMeasure X,
      StrictMono φ ∧ Tendsto (fun n => P (ψ (φ n))) atTop (𝓝 Plim) := by
  have hP' : IsTightMeasureSet (Set.range fun n : ℕ =>
      (P (ψ n) : Measure X)) := hP.subset (by
        rintro μ ⟨n, rfl⟩
        exact ⟨ψ n, rfl⟩)
  obtain ⟨φ, Plim, hφ, hlim⟩ :=
    exists_subseq_tendsto_of_tight_probability_laws (fun n => P (ψ n)) hP'
  exact ⟨φ, Plim, hφ, hlim⟩

/-- A countable product of copies of the vague space of positive locally finite measures is Polish. -/
theorem vagueCountableProductPolishSpace {ι X : Type*} [Countable ι]
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] :
    PolishSpace (ι → PositiveRadonMeasure X) := by
  let _ : PolishSpace (PositiveRadonMeasure X) := vaguePolishSpace
  infer_instance



end Critical2DKPZ.RandomMeasure

end
