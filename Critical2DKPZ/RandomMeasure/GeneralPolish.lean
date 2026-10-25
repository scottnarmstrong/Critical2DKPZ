/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.RandomMeasure.GeneralMetric
public import Critical2DKPZ.RandomMeasure.GeneralCompactness
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.Metrizable.CompletelyMetrizable

/-! On a locally compact second-countable Hausdorff space, positive locally finite Borel measures form a Polish space for vague convergence, and compact-window mass bounds characterize relative compactness. -/

public section

open MeasureTheory Set Metric Filter TopologicalSpace
open scoped CompactlySupported Topology

noncomputable section

set_option linter.style.haveILetI false

namespace Critical2DKPZ.RandomMeasure

/-- The compact-test coordinate map is an isometric embedding for the weighted metric. -/
theorem dist_countableVagueReadout {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X)
    (μ ν : PositiveRadonMeasure X) :
    letI : MetricSpace ((ℕ × ℕ) ⊕ ℕ → ℝ) := PiCountable.metricSpace
    letI : MetricSpace (PositiveRadonMeasure X) := vagueMetricSpace K
    dist (countableVagueReadout K μ) (countableVagueReadout K ν) = dist μ ν := by
  letI : TopologicalSpace (PositiveRadonMeasure X) := vagueMetricTopology K
  letI : MetricSpace (PositiveRadonMeasure X) := vagueMetricSpace K
  letI : MetricSpace (VagueEmbedding K) := vagueEmbeddingMetricSpace K
  letI : MetricSpace ((ℕ × ℕ) ⊕ ℕ → ℝ) := PiCountable.metricSpace
  have hequiv : Isometry (vagueEmbeddingEquiv K) := vagueEmbeddingEquiv_isometry K
  have hembed := Metric.PiNatEmbed.isometry_embed
    (X := PositiveRadonMeasure X)
    (Y := fun _ : (ℕ × ℕ) ⊕ ℕ => ℝ)
    (f := fun i μ => vaguePairing μ (countableVagueTest K i))
  have hread (μ : PositiveRadonMeasure X) :
      countableVagueReadout K μ =
        Metric.PiNatEmbed.embed _ _ _ (vagueEmbeddingEquiv K μ) := by
    funext i
    simp [countableVagueReadout, Metric.PiNatEmbed.embed]
  calc
    dist (countableVagueReadout K μ) (countableVagueReadout K ν) =
        dist (Metric.PiNatEmbed.embed _ _ _ (vagueEmbeddingEquiv K μ))
          (Metric.PiNatEmbed.embed _ _ _ (vagueEmbeddingEquiv K ν)) := by
            rw [hread, hread]
    _ = dist (vagueEmbeddingEquiv K μ) (vagueEmbeddingEquiv K ν) :=
      hembed.dist_eq _ _
    _ = dist μ ν := hequiv.dist_eq _ _

/-- A vague-metric Cauchy sequence has Cauchy compact-test coordinates. -/
theorem cauchySeq_countableVagueReadout {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X)
    (μ : ℕ → PositiveRadonMeasure X)
    (hμ : letI : MetricSpace (PositiveRadonMeasure X) := vagueMetricSpace K
      CauchySeq μ) :
    ∀ i : (ℕ × ℕ) ⊕ ℕ,
      CauchySeq (fun n => countableVagueReadout K (μ n) i) := by
  letI : MetricSpace (PositiveRadonMeasure X) := vagueMetricSpace K
  letI : MetricSpace ((ℕ × ℕ) ⊕ ℕ → ℝ) := PiCountable.metricSpace
  intro i
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let w : ℝ := (2⁻¹ : ℝ) ^ Encodable.encode i
  have hw : 0 < w := by dsimp [w]; positivity
  let δ : ℝ := min ε (w / 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hμ) δ hδ
  refine ⟨N, fun m hm n hn => ?_⟩
  have hprod : dist (countableVagueReadout K (μ m))
      (countableVagueReadout K (μ n)) < w := by
    rw [dist_countableVagueReadout]
    exact lt_trans (hN m hm n hn) (by
      dsimp [δ]
      exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self hw))
  have hcoord := PiCountable.dist_le_dist_pi_of_dist_lt (i := i) hprod
  calc
    dist (countableVagueReadout K (μ m) i) (countableVagueReadout K (μ n) i) ≤
        dist (countableVagueReadout K (μ m)) (countableVagueReadout K (μ n)) := hcoord
    _ < δ := by rw [dist_countableVagueReadout]; exact hN m hm n hn
    _ ≤ ε := min_le_left _ _

/-- A Cauchy sequence has uniform mass bounds on each compact exhaustion
window, by its mass-test coordinate. -/
theorem localMassBound_of_cauchySeq {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X)
    (μ : ℕ → PositiveRadonMeasure X)
    (hμ : letI : MetricSpace (PositiveRadonMeasure X) := vagueMetricSpace K
      CauchySeq μ) :
    ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, (μ n).measure.real (K k) ≤ C := by
  have hcoord := cauchySeq_countableVagueReadout K μ hμ
  intro k
  let f := vagueMassTest K k
  have hscalar : CauchySeq (fun n => vaguePairing (μ n) f) := hcoord (.inr k)
  obtain ⟨R, hRpos, hR⟩ := cauchySeq_bdd hscalar
  refine ⟨|vaguePairing (μ 0) f| + R, fun n => ?_⟩
  calc
    (μ n).measure.real (K k) ≤ vaguePairing (μ n) f := vague_window_mass_le_test K (μ n) k
    _ ≤ |vaguePairing (μ n) f| := le_abs_self _
    _ ≤ |vaguePairing (μ n) f - vaguePairing (μ 0) f| +
          |vaguePairing (μ 0) f| := by
      calc
        |vaguePairing (μ n) f| =
            |(vaguePairing (μ n) f - vaguePairing (μ 0) f) +
              vaguePairing (μ 0) f| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
    _ = dist (vaguePairing (μ n) f) (vaguePairing (μ 0) f) +
          |vaguePairing (μ 0) f| := by rw [Real.dist_eq]
    _ ≤ R + |vaguePairing (μ 0) f| := add_le_add (hR n 0).le le_rfl
    _ = |vaguePairing (μ 0) f| + R := by ring

/-- The weighted countable-test metric is complete for every locally compact,
second-countable Hausdorff carrier. -/
theorem vagueMetric_complete {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X) :
    @CompleteSpace (PositiveRadonMeasure X)
      (vagueMetricSpace K).toUniformSpace := by
  letI : MetricSpace (PositiveRadonMeasure X) := vagueMetricSpace K
  apply Metric.complete_of_cauchySeq_tendsto
  intro μ hμ
  have hmass := localMassBound_of_cauchySeq K μ hμ
  obtain ⟨φ, hφ, ν, hsub⟩ :=
    exists_strictMono_subseq_vague_tendsto_of_localMassBound K μ hmass
  have hsubMetric : Tendsto (fun n => μ (φ n)) atTop
      (@nhds (PositiveRadonMeasure X) (vagueMetricTopology K) ν) := by
    rw [vagueMetricTopology_eq_vagueTopology K]
    exact hsub
  exact ⟨ν, tendsto_nhds_of_cauchySeq_of_subseq hμ hφ.tendsto_atTop hsubMetric⟩

/-- The vague topology is completely metrizable by the explicit countable
test metric. -/
theorem vague_isCompletelyMetrizableSpace {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] :
    IsCompletelyMetrizableSpace (PositiveRadonMeasure X) := by
  refine ⟨⟨vagueMetricSpace (vagueCompactExhaustion X), ?_, ?_⟩⟩
  · exact vagueMetricTopology_eq_vagueTopology (vagueCompactExhaustion X)
  · exact vagueMetric_complete (vagueCompactExhaustion X)

/-- The vague space of positive Radon measures is Polish on every locally
compact, second-countable Hausdorff carrier. -/
theorem vaguePolishSpace {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] : PolishSpace (PositiveRadonMeasure X) := by
  letI : IsCompletelyMetrizableSpace (PositiveRadonMeasure X) :=
    vague_isCompletelyMetrizableSpace
  letI : SeparableSpace (PositiveRadonMeasure X) := vagueSeparableSpace
  infer_instance


/-- The cutoff integral is bounded above by the mass of its next exhaustion
window. -/
theorem vagueMassTest_pairing_le_next_window {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    (K : CompactExhaustion X) (μ : PositiveRadonMeasure X) (k : ℕ) :
    vaguePairing μ (vagueMassTest K k) ≤ μ.measure.real (K (k + 1)) := by
  letI : IsLocallyFiniteMeasure μ.measure := μ.2
  let W := K (k + 1)
  have hW : MeasurableSet W := (K.isCompact (k + 1)).isClosed.measurableSet
  have hfinite : IsFiniteMeasure (μ.measure.restrict W) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact (K.isCompact (k + 1)).measure_lt_top
  letI : IsFiniteMeasure (μ.measure.restrict W) := hfinite
  have hi : Integrable (W.indicator (fun _ => (1 : ℝ))) μ.measure :=
    (integrable_indicator_iff hW).mpr (integrable_const 1)
  have hpoint (x : X) : vagueMassTest K k x ≤ W.indicator (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ W
    · rw [Set.indicator_of_mem hx]
      exact (vagueMassTest_spec K k).2.1 x
    · have hxzero : vagueMassTest K k x = 0 := by
        by_contra hne
        exact hx ((vagueMassTest_spec K k).2.2.2
          (subset_tsupport _ hne))
      simp [Set.indicator_of_notMem hx, hxzero]
  have hint : (∫ x, W.indicator (fun _ => (1 : ℝ)) x ∂μ.measure) =
      μ.measure.real W := by
    simpa only [smul_eq_mul, mul_one] using
      (integral_indicator_const (1 : ℝ) (μ := μ.measure) (s := W) hW)
  calc
    vaguePairing μ (vagueMassTest K k) ≤
        ∫ x, W.indicator (fun _ => (1 : ℝ)) x ∂μ.measure := by
      exact integral_mono (integrable_vagueTest μ (vagueMassTest K k)) hi hpoint
    _ = μ.measure.real W := hint

/-- Uniform compact-window mass bounds characterize relative compactness in
the vague topology. -/
theorem isCompact_vagueClosure_iff_localMassBound {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X)
    {S : Set (PositiveRadonMeasure X)} :
    IsCompact (closure S) ↔
      ∀ k : ℕ, ∃ C : ℝ, ∀ μ ∈ S, μ.measure.real (K k) ≤ C := by
  constructor
  · intro hcompact k
    let f : PositiveRadonMeasure X → ℝ :=
      fun μ => vaguePairing μ (vagueMassTest K k)
    have hf : Continuous f := continuous_vaguePairing (vagueMassTest K k)
    let g : PositiveRadonMeasure X → ℝ := fun μ => |f μ|
    have hg : Continuous g := continuous_abs.comp hf
    have himage : IsCompact (g '' closure S) := hcompact.image hg
    obtain ⟨C, hC⟩ := himage.bddAbove
    refine ⟨C, fun μ hμ => ?_⟩
    calc
      μ.measure.real (K k) ≤ f μ := vague_window_mass_le_test K μ k
      _ ≤ |f μ| := le_abs_self _
      _ = ‖f μ‖ := by rw [Real.norm_eq_abs]
      _ ≤ C := hC ⟨μ, subset_closure hμ, rfl⟩
  · intro hbound
    letI : MetricSpace (PositiveRadonMeasure X) :=
      vagueMetricSpaceOnVagueTopology (vagueCompactExhaustion X)
    haveI : PseudoMetrizableSpace (PositiveRadonMeasure X) := by
      refine ⟨⟨(vagueMetricSpaceOnVagueTopology (vagueCompactExhaustion X)).toUniformSpace,
        vagueMetricSpaceOnVagueTopology_topology (vagueCompactExhaustion X),
        inferInstance⟩⟩
    have hclosureBound : ∀ k : ℕ, ∃ C : ℝ,
        ∀ μ ∈ closure S, μ.measure.real (K k) ≤ C := by
      intro k
      obtain ⟨C, hC⟩ := hbound (k + 1)
      let g := vagueMassTest K k
      let f : PositiveRadonMeasure X → ℝ := fun μ => vaguePairing μ g
      have hf : Continuous f := continuous_vaguePairing g
      have hclosed : IsClosed (f ⁻¹' Set.Iic C) := isClosed_Iic.preimage hf
      have hsubset : S ⊆ f ⁻¹' Set.Iic C := by
        intro μ hμ
        change f μ ≤ C
        exact (vagueMassTest_pairing_le_next_window K μ k).trans
          (hC μ hμ)
      have hcl : closure S ⊆ f ⁻¹' Set.Iic C := closure_minimal hsubset hclosed
      refine ⟨C, fun μ hμ => ?_⟩
      exact (vague_window_mass_le_test K μ k).trans (hcl hμ)
    have hseq : IsSeqCompact (closure S) := by
      intro μ hμ
      have hmass : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
          (μ n).measure.real (K k) ≤ C := by
        intro k
        obtain ⟨C, hC⟩ := hclosureBound k
        exact ⟨C, fun n => hC (μ n) (hμ n)⟩
      obtain ⟨φ, hφ, ν, hν⟩ :=
        exists_strictMono_subseq_vague_tendsto_of_localMassBound K μ hmass
      refine ⟨ν, ?_, φ, hφ, ?_⟩
      · exact isClosed_closure.mem_of_tendsto hν
          (Filter.Eventually.of_forall fun n => hμ (φ n))
      · change Tendsto (fun n => μ (φ n)) atTop (𝓝 ν)
        exact hν
    exact hseq.isCompact

end Critical2DKPZ.RandomMeasure

end
