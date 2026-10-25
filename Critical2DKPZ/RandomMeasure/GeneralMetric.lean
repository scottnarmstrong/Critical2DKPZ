/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.RandomMeasure.GeneralBorel
public import Mathlib.Topology.MetricSpace.PiNat
public import Mathlib.Topology.Bases
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-! On a locally compact second-countable Hausdorff space, a countable determining family of compactly supported continuous tests metrizes vague convergence of positive locally finite measures. -/

public section

open MeasureTheory Set Metric Filter TopologicalSpace
open scoped CompactlySupported Topology PiCountable

noncomputable section

set_option linter.style.haveILetI false

namespace Critical2DKPZ.RandomMeasure

/-- Equality of the selected compact-test integrals implies equality of every compactly supported continuous test integral. -/
theorem vaguePairing_eq_of_countableReadout_eq {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X)
    {μ ν : PositiveRadonMeasure X}
    (hread : countableVagueReadout K μ = countableVagueReadout K ν)
    (f : C_c(X, ℝ)) : vaguePairing μ f = vaguePairing ν f := by
  obtain ⟨n, hf⟩ := exists_vagueExhaustionWindow_support K f
  have hmassPair :
      vaguePairing μ (vagueMassTest K n) = vaguePairing ν (vagueMassTest K n) := by
    have h := congrFun hread (.inr n)
    simpa only [countableVagueReadout, countableVagueTest] using h
  have hmassPair' :
      (∫ x, vagueMassTest K n x ∂μ.measure) =
        ∫ x, vagueMassTest K n x ∂ν.measure := by
    simpa only [vaguePairing] using hmassPair
  let C : ℝ := |vaguePairing μ (vagueMassTest K n)| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hμmass : μ.measure.real (K n) ≤ C := by
    calc
      μ.measure.real (K n) ≤ ∫ x, vagueMassTest K n x ∂μ.measure :=
        vague_window_mass_le_test K μ n
      _ ≤ C := by
        dsimp [C, vaguePairing]
        exact le_trans (le_abs_self _) (by linarith)
  have hνmass : ν.measure.real (K n) ≤ C := by
    calc
      ν.measure.real (K n) ≤ ∫ x, vagueMassTest K n x ∂ν.measure :=
        vague_window_mass_le_test K ν n
      _ ≤ C := by
        rw [← hmassPair']
        dsimp [C, vaguePairing]
        exact le_trans (le_abs_self _) (by linarith)
  by_contra hne
  let η : ℝ := |vaguePairing μ f - vaguePairing ν f| / (4 * C)
  have hη : 0 < η := by
    dsimp [η]
    exact div_pos (abs_pos.mpr (sub_ne_zero.mpr hne)) (by positivity)
  obtain ⟨j, hj⟩ := exists_denseVagueTest_approx K n f hf η hη
  let g := denseVagueTest K n j
  have hg : tsupport (g : X → ℝ) ⊆ K n := denseVagueTest_support K n j
  have hgj : vaguePairing μ g = vaguePairing ν g := by
    have h := congrFun hread (.inl (n, j))
    simpa only [countableVagueReadout, countableVagueTest] using h
  have hμerr : |vaguePairing μ f - vaguePairing μ g| ≤ η * C := by
    exact (vague_test_integral_error K μ n f g hf hg η (fun x hx => by
      simpa only [abs_sub_comm] using (hj x hx).le)).trans
      (mul_le_mul_of_nonneg_left hμmass hη.le)
  have hνerr : |vaguePairing ν f - vaguePairing ν g| ≤ η * C := by
    exact (vague_test_integral_error K ν n f g hf hg η (fun x hx => by
      simpa only [abs_sub_comm] using (hj x hx).le)).trans
      (mul_le_mul_of_nonneg_left hνmass hη.le)
  have htri := abs_sub_le (vaguePairing μ f) (vaguePairing μ g) (vaguePairing ν f)
  have hmid : |vaguePairing μ g - vaguePairing ν f| =
      |vaguePairing ν g - vaguePairing ν f| := by rw [hgj]
  have hlast : |vaguePairing ν g - vaguePairing ν f| ≤ η * C := by
    rw [abs_sub_comm]
    exact hνerr
  have hbound : |vaguePairing μ f - vaguePairing ν f| ≤ 2 * η * C := by
    calc
      |vaguePairing μ f - vaguePairing ν f| ≤
          |vaguePairing μ f - vaguePairing μ g| +
            |vaguePairing μ g - vaguePairing ν f| := htri
      _ ≤ η * C + η * C := add_le_add hμerr (hmid ▸ hlast)
      _ = 2 * η * C := by ring
  have hηeq : 2 * η * C = |vaguePairing μ f - vaguePairing ν f| / 2 := by
    dsimp [η]
    field_simp
    norm_num
  have habspos : 0 < |vaguePairing μ f - vaguePairing ν f| :=
    abs_pos.mpr (sub_ne_zero.mpr hne)
  linarith

/-- The countable family of compact-test integrals separates positive locally finite measures. -/
theorem countableVagueReadout_injective {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X) :
    Function.Injective (countableVagueReadout K) := by
  intro μ ν hread
  apply Subtype.ext
  have hμreg : Measure.Regular μ.measure := by
    let : IsLocallyFiniteMeasure μ.measure := μ.2
    infer_instance
  have hνreg : Measure.Regular ν.measure := by
    let : IsLocallyFiniteMeasure ν.measure := ν.2
    infer_instance
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  exact vaguePairing_eq_of_countableReadout_eq K hread f

/-- The image of the compact-test coordinate map in the countable product of real lines. -/
abbrev VagueEmbedding {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    (K : CompactExhaustion X) :=
  PiNatEmbed (PositiveRadonMeasure X) (fun _ : (ℕ × ℕ) ⊕ ℕ => ℝ)
    (fun i μ => vaguePairing μ (countableVagueTest K i))

/-- Distinct locally finite measures have different integrals against some test in the countable family. -/
theorem countableVagueTests_separate {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X) :
    Pairwise fun μ ν : PositiveRadonMeasure X =>
      ∃ i : (ℕ × ℕ) ⊕ ℕ,
        vaguePairing μ (countableVagueTest K i) ≠
          vaguePairing ν (countableVagueTest K i) := by
  intro μ ν hμν
  by_contra h
  apply hμν
  apply countableVagueReadout_injective K
  funext i
  change vaguePairing μ (countableVagueTest K i) =
    vaguePairing ν (countableVagueTest K i)
  exact not_ne_iff.mp (not_exists.mp h i)

/-- The weighted product metric on the image of the compact-test coordinate map. -/
@[instance_reducible]
noncomputable def vagueEmbeddingMetricSpace {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X) :
    MetricSpace (VagueEmbedding K) :=
  PiNatEmbed.metricSpace (countableVagueTests_separate K)

/-- The compact-test coordinate map is a bijection from locally finite measures onto its image. -/
@[expose]
noncomputable def vagueEmbeddingEquiv {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X) :
    PositiveRadonMeasure X ≃ VagueEmbedding K :=
  PiNatEmbed.toPiNatEquiv _ _ _

/-- Applying the inverse compact-test coordinate map recovers the original measure. -/
@[simp]
theorem vagueEmbeddingEquiv_ofPiNat {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X)
    (μ : PositiveRadonMeasure X) :
    (vagueEmbeddingEquiv K μ).ofPiNat = μ := rfl

/-- The weighted countable-test metric transported to positive Radon
measures. -/
@[instance_reducible]
noncomputable def vagueMetricSpace {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X) :
    MetricSpace (PositiveRadonMeasure X) :=
  MetricSpace.induced (vagueEmbeddingEquiv K)
    (vagueEmbeddingEquiv K).injective (vagueEmbeddingMetricSpace K)

/-- The compact-test coordinate map is an isometry for the weighted test metric. -/
theorem vagueEmbeddingEquiv_isometry {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X) :
    letI : MetricSpace (PositiveRadonMeasure X) := vagueMetricSpace K
    letI : MetricSpace (VagueEmbedding K) := vagueEmbeddingMetricSpace K
    Isometry (vagueEmbeddingEquiv K) := by
  letI : MetricSpace (PositiveRadonMeasure X) := vagueMetricSpace K
  letI : MetricSpace (VagueEmbedding K) := vagueEmbeddingMetricSpace K
  exact MetricSpace.isometry_induced _ (vagueEmbeddingEquiv K).injective

abbrev vagueMetricTopology {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X) :
    TopologicalSpace (PositiveRadonMeasure X) :=
  (vagueMetricSpace K).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- Each coordinate is continuous for the weighted countable-test metric. -/
theorem continuous_countableVaguePairing_metric {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X)
    (i : (ℕ × ℕ) ⊕ ℕ) :
    @Continuous (PositiveRadonMeasure X) ℝ (vagueMetricTopology K)
      inferInstance (fun μ => vaguePairing μ (countableVagueTest K i)) := by
  letI : MetricSpace (PositiveRadonMeasure X) := vagueMetricSpace K
  letI : TopologicalSpace (PositiveRadonMeasure X) := vagueMetricTopology K
  letI : MetricSpace (VagueEmbedding K) := vagueEmbeddingMetricSpace K
  letI : MetricSpace ((ℕ × ℕ) ⊕ ℕ → ℝ) := PiCountable.metricSpace
  have hequiv : Isometry (vagueEmbeddingEquiv K) := by
    intro μ ν
    rfl
  have hembed := Metric.PiNatEmbed.isometry_embed
    (X := PositiveRadonMeasure X)
    (Y := fun _ : (ℕ × ℕ) ⊕ ℕ => ℝ)
    (f := fun i μ => vaguePairing μ (countableVagueTest K i))
  have hcont : Continuous (fun μ : PositiveRadonMeasure X =>
      (Metric.PiNatEmbed.embed _ _ _ (vagueEmbeddingEquiv K μ)) i) :=
    (continuous_apply i).comp (hembed.continuous.comp hequiv.continuous)
  convert hcont using 1
  funext μ
  rfl

/-- The countable-test metric topology agrees with the vague topology. -/
theorem vagueMetricTopology_eq_vagueTopology {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X) :
    vagueMetricTopology K = vagueTopology X := by
  letI : MetricSpace (PositiveRadonMeasure X) := vagueMetricSpace K
  letI : TopologicalSpace (PositiveRadonMeasure X) := vagueMetricTopology K
  letI : TopologicalSpace ((ℕ × ℕ) ⊕ ℕ → ℝ) := Pi.topologicalSpace
  have hcoords : ∀ i : (ℕ × ℕ) ⊕ ℕ,
      Continuous (fun μ : PositiveRadonMeasure X =>
        vaguePairing μ (countableVagueTest K i)) := by
    intro i
    exact continuous_countableVaguePairing_metric K i
  have hread : Continuous (countableVagueReadout K) := continuous_pi hcoords
  have hmetric_le_countable : vagueMetricTopology K ≤ countableVagueTopology K := by
    change vagueMetricTopology K ≤ TopologicalSpace.induced
      (countableVagueReadout K) Pi.topologicalSpace
    exact hread.le_induced
  apply le_antisymm
  · rw [← countableVagueTopology_eq_vague K]
    exact hmetric_le_countable
  · letI : TopologicalSpace (PositiveRadonMeasure X) := countableVagueTopology K
    letI : MetricSpace (PositiveRadonMeasure X) := vagueMetricSpace K
    letI : MetricSpace (VagueEmbedding K) := vagueEmbeddingMetricSpace K
    letI : MetricSpace ((ℕ × ℕ) ⊕ ℕ → ℝ) := PiCountable.metricSpace
    have hcoord' : ∀ i : (ℕ × ℕ) ⊕ ℕ,
        @Continuous (PositiveRadonMeasure X) ℝ (countableVagueTopology K)
          inferInstance (fun μ => vaguePairing μ (countableVagueTest K i)) := by
      intro i
      have hr : @Continuous (PositiveRadonMeasure X)
          ((ℕ × ℕ) ⊕ ℕ → ℝ) (countableVagueTopology K) inferInstance
          (countableVagueReadout K) := by
        change @Continuous (PositiveRadonMeasure X)
          ((ℕ × ℕ) ⊕ ℕ → ℝ)
          (TopologicalSpace.induced (countableVagueReadout K) Pi.topologicalSpace)
          Pi.topologicalSpace (countableVagueReadout K)
        exact continuous_induced_dom
      change Continuous (fun μ => countableVagueReadout K μ i)
      convert (continuous_apply i).comp hr using 1
      rfl
    have hembed : Continuous (fun μ : PositiveRadonMeasure X => vagueEmbeddingEquiv K μ) := by
      change Continuous (Metric.PiNatEmbed.toPiNat
        (X := PositiveRadonMeasure X)
        (Y := fun _ : (ℕ × ℕ) ⊕ ℕ => ℝ)
        (f := fun i μ => vaguePairing μ (countableVagueTest K i)))
      exact Metric.PiNatEmbed.continuous_toPiNat hcoord'
    have hinduced : countableVagueTopology K ≤ vagueMetricTopology K := by
      change countableVagueTopology K ≤ TopologicalSpace.induced
        (vagueEmbeddingEquiv K)
          ((vagueEmbeddingMetricSpace K).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace)
      exact continuous_iff_le_induced.mp hembed
    rw [← countableVagueTopology_eq_vague K]
    exact hinduced

/-- The metric defined by compact-test coordinates, with the vague topology. -/
@[instance_reducible]
noncomputable def vagueMetricSpaceOnVagueTopology {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X) :
    MetricSpace (PositiveRadonMeasure X) :=
  MetricSpace.replaceTopology (vagueMetricSpace K)
    (vagueMetricTopology_eq_vagueTopology K).symm

/-- The uniform structure of the compact-test metric induces the vague topology. -/
theorem vagueMetricSpaceOnVagueTopology_topology {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X) :
    (vagueMetricSpaceOnVagueTopology K).toUniformSpace.toTopologicalSpace =
      vagueTopology X := by
  rfl

/-- Positive Radon measures on a second-countable locally compact Hausdorff
space are separable for the vague topology. -/
theorem vagueSeparableSpace {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] :
    @SeparableSpace (PositiveRadonMeasure X) (vagueTopology X) := by
  letI : SecondCountableTopology (PositiveRadonMeasure X) :=
    vagueTopology_secondCountable
  exact inferInstance


end Critical2DKPZ.RandomMeasure

end
