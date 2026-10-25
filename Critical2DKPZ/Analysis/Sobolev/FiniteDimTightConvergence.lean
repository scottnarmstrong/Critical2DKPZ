/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.RandomMeasure.GeneralDetermination
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Data.Set.Countable
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-! On a separable metrizable space, tight laws converge weakly when their finite-dimensional laws under continuous real-valued maps converge and those maps generate the Borel sigma algebra. -/

@[expose] public section

open MeasureTheory Filter TopologicalSpace
open scoped Topology

namespace Critical2DKPZ.Analysis.Sobolev

private def finiteRealCylinderAll {ι : Type*} : Set (Set (ι → ℝ)) :=
  {A | ∃ s : Finset ι, ∃ U : ι → Set ℝ,
    (∀ i ∈ s, MeasurableSet (U i)) ∧ A = Set.pi (s : Set ι) U}

private theorem finiteRealCylinderAll_isPiSystem {ι : Type*} :
    IsPiSystem (finiteRealCylinderAll (ι := ι)) := by
  classical
  rintro A ⟨s, U, hU, rfl⟩ B ⟨t, V, hV, rfl⟩ _
  let W : ι → Set ℝ := fun i =>
    (if i ∈ s then U i else Set.univ) ∩ (if i ∈ t then V i else Set.univ)
  refine ⟨s ∪ t, W, ?_, ?_⟩
  · intro i hi
    rcases Finset.mem_union.mp hi with his | hit
    · by_cases hti : i ∈ t
      · simpa [W, his, hti] using (hU i his).inter (hV i hti)
      · simpa [W, his, hti] using hU i his
    · by_cases hsi : i ∈ s
      · simpa [W, hsi, hit] using (hU i hsi).inter (hV i hit)
      · simpa [W, hsi, hit] using hV i hit
  · ext x
    change (x ∈ Set.pi (s : Set ι) U ∧ x ∈ Set.pi (t : Set ι) V) ↔
      x ∈ Set.pi ((s ∪ t : Finset ι) : Set ι) W
    constructor
    · rintro ⟨hxs, hxt⟩ i hi
      rcases Finset.mem_union.mp hi with his | hit
      · have hleft : x i ∈ (if i ∈ s then U i else Set.univ) := by
          have hxs' : x i ∈ U i := hxs i (by simpa using his)
          simpa [his] using hxs'
        have hright : x i ∈ (if i ∈ t then V i else Set.univ) := by
          by_cases hti : i ∈ t
          · simpa [hti] using hxt i hti
          · simp [hti]
        exact ⟨hleft, hright⟩
      · have hright : x i ∈ (if i ∈ t then V i else Set.univ) := by
          have hxt' : x i ∈ V i := hxt i (by simpa using hit)
          simpa [hit] using hxt'
        have hleft : x i ∈ (if i ∈ s then U i else Set.univ) := by
          by_cases hsi : i ∈ s
          · simpa [hsi] using hxs i hsi
          · simp [hsi]
        exact ⟨hleft, hright⟩
    · intro hx
      constructor
      · intro i hi
        have hi' : i ∈ s := by simpa using hi
        have hmem := hx i (Finset.mem_union.mpr (Or.inl hi'))
        have hleft : x i ∈ (if i ∈ s then U i else Set.univ) := hmem.1
        simpa [hi'] using hleft
      · intro i hi
        have hi' : i ∈ t := by simpa using hi
        have hmem := hx i (Finset.mem_union.mpr (Or.inr hi'))
        have hright : x i ∈ (if i ∈ t then V i else Set.univ) := hmem.2
        simpa [hi'] using hright

private theorem finiteRealCylinderAll_generateFrom {ι : Type*} :
    MeasurableSpace.generateFrom (finiteRealCylinderAll (ι := ι)) =
      (MeasurableSpace.pi : MeasurableSpace (ι → ℝ)) := by
  classical
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro A ⟨s, U, hU, rfl⟩
    exact MeasurableSet.pi (Set.Finite.countable (Finset.finite_toSet s)) hU
  · rw [MeasurableSpace.pi_eq_generateFrom_projections]
    apply MeasurableSpace.generateFrom_mono
    intro A hA
    change ∃ i : ι, ∃ B : Set ℝ, MeasurableSet B ∧ Function.eval i ⁻¹' B = A at hA
    obtain ⟨i, B, hB, rfl⟩ := hA
    refine ⟨{i}, fun j => if j = i then B else Set.univ, ?_, ?_⟩
    · intro j hj
      have hji : j = i := Finset.mem_singleton.mp hj
      subst j
      simpa using hB
    · ext x
      simp

private theorem measure_eq_of_finite_readout_laws
    {E ι : Type*} [MeasurableSpace E]
    (F : E → ι → ℝ)
    (hmeas : Measurable F)
    (hreadout : (inferInstance : MeasurableSpace E) =
      MeasurableSpace.comap F
        (MeasurableSpace.pi : MeasurableSpace (ι → ℝ)))
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ s : Finset ι,
      Measure.map (fun x : E => fun i : s => F x i.1) μ =
        Measure.map (fun x : E => fun i : s => F x i.1) ν) :
    μ = ν := by
  classical
  let C : Set (Set E) :=
    {A | ∃ B ∈ finiteRealCylinderAll (ι := ι),
      F ⁻¹' B = A}
  have hCgen : (inferInstance : MeasurableSpace E) = MeasurableSpace.generateFrom C := by
    calc
      (inferInstance : MeasurableSpace E) =
          (MeasurableSpace.pi : MeasurableSpace (ι → ℝ)).comap F := hreadout
      _ = (MeasurableSpace.generateFrom
          (finiteRealCylinderAll (ι := ι))).comap F := by
            rw [finiteRealCylinderAll_generateFrom]
      _ = MeasurableSpace.generateFrom C := by
        rw [MeasurableSpace.comap_generateFrom]
        rfl
  have hCpi : IsPiSystem C := by
    change IsPiSystem {A | ∃ B ∈
      finiteRealCylinderAll (ι := ι), F ⁻¹' B = A}
    exact finiteRealCylinderAll_isPiSystem.comap F
  have hCeq : ∀ A, A ∈ C → μ A = ν A := by
    intro A hA
    obtain ⟨B, hB, rfl⟩ := hA
    change ∃ s : Finset ι, ∃ U : ι → Set ℝ,
      (∀ i ∈ s, MeasurableSet (U i)) ∧ B = Set.pi (s : Set ι) U at hB
    obtain ⟨s, U, hU, rfl⟩ := hB
    let π : E → s → ℝ := fun x i => F x i.1
    have hπ : Measurable π := by
      apply measurable_pi_iff.mpr
      intro i
      exact (measurable_pi_iff.mp hmeas) i.1
    let B' : Set (s → ℝ) := Set.pi Set.univ fun i => U i.1
    have hB'meas : MeasurableSet B' :=
      MeasurableSet.univ_pi fun i => hU i.1 i.2
    have hfinite := congrArg (fun m : Measure (s → ℝ) => m B') (h s)
    rw [Measure.map_apply hπ hB'meas, Measure.map_apply hπ hB'meas] at hfinite
    have hpre : π ⁻¹' B' = F ⁻¹' Set.pi (s : Set ι) U := by
      ext x
      simp [π, B', Set.mem_pi]
    rw [← hpre]
    exact hfinite
  have htotal : μ Set.univ = ν Set.univ := by
    have hempty := congrArg
      (fun m : Measure ((∅ : Finset ι) → ℝ) => m Set.univ) (h ∅)
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ,
      Measure.map_apply (by fun_prop) MeasurableSet.univ] at hempty
    simpa using hempty
  exact ext_of_generate_finite C hCgen hCpi hCeq htotal

/-- Tight laws on a separable metrizable space converge weakly if their finite-dimensional marginals under continuous real-valued maps converge and those maps generate the Borel sigma algebra. -/
theorem tendsto_probabilityMeasure_of_tight_finiteReadoutLaws
    {E ι : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [T2Space E] [PseudoMetrizableSpace E] [SeparableSpace E]
    [BorelSpace E] [OpensMeasurableSpace E]
    (F : E → ι → ℝ) (hF : Continuous F) (hmeas : Measurable F)
    (hreadout : (inferInstance : MeasurableSpace E) =
      MeasurableSpace.comap F
        (MeasurableSpace.pi : MeasurableSpace (ι → ℝ)))
    (P : ℕ → ProbabilityMeasure E) (Q : ProbabilityMeasure E)
    (hP : IsTightMeasureSet (Set.range fun n : ℕ => (P n : Measure E)))
    (hread : ∀ s : Finset ι,
      Tendsto (fun n => (P n).map (fun x : E => fun i : s => F x i.1)) atTop
        (𝓝 (Q.map (fun x : E => fun i : s => F x i.1)))) :
    Tendsto P atTop (𝓝 Q) := by
  classical
  have hTight : IsTightMeasureSet
      ((fun μ : ProbabilityMeasure E => (μ : Measure E)) '' Set.range P) := by
    have hrange :
        ((fun μ : ProbabilityMeasure E => (μ : Measure E)) '' Set.range P) =
          Set.range fun n : ℕ => (P n : Measure E) := by
      ext μ
      simp
    rw [hrange]
    exact hP
  have hcompact := _root_.isCompact_closure_of_isTightMeasureSet hTight
  have hmem : ∀ᶠ n : ℕ in atTop, P n ∈ closure (Set.range P) := by
    filter_upwards [] with n
    exact subset_closure ⟨n, rfl⟩
  apply hcompact.tendsto_nhds_of_unique_mapClusterPt
    (l := atTop) (f := P) (y := Q) hmem
  intro R hR hcluster
  obtain ⟨φ, hφ, hlim⟩ := hcluster.tendsto_subseq
  have hfinite : ∀ s : Finset ι,
      Measure.map (fun x : E => fun i : s => F x i.1) (R : Measure E) =
        Measure.map (fun x : E => fun i : s => F x i.1) (Q : Measure E) := by
    intro s
    let G : E → s → ℝ := fun x i => F x i.1
    have hproj : Continuous (fun f : ι → ℝ => fun i : s => f i.1) := by
      apply continuous_pi_iff.mpr
      intro i
      exact continuous_apply i.1
    have hG : Continuous G := hproj.comp hF
    have hclusterMap : Tendsto (fun n => (P (φ n)).map G) atTop
        (𝓝 (R.map G)) :=
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        (fun n => P (φ n)) R hlim hG
    have hgivenMap : Tendsto (fun n => (P (φ n)).map G) atTop
        (𝓝 (Q.map G)) := (hread s).comp hφ.tendsto_atTop
    have hprob : R.map G = Q.map G := tendsto_nhds_unique hclusterMap hgivenMap
    exact congrArg Subtype.val hprob
  exact Subtype.ext (measure_eq_of_finite_readout_laws F hmeas hreadout
    (R : Measure E) (Q : Measure E) hfinite)

end Critical2DKPZ.Analysis.Sobolev

end
