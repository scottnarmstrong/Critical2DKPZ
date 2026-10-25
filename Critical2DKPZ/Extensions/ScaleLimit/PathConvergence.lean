/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SubsequentialLimits
public import Critical2DKPZ.Extensions.ScaleLimit.WienerLaw
import Critical2DKPZ.Extensions.ScaleLimit.SeqReduction

/-! # Convergence from tightness and the unique subsequential law

The finite-dimensional theorem identifies every subsequential law. Tightness
along every divergent scale sequence therefore gives convergence of the whole
positive-real scale family. This separates the topological argument from the
spectral modulus estimate that supplies tightness.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology BoundedContinuousFunction
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- For an identity limit variable, convergence in distribution is convergence of
its probability laws, with measurability retained explicitly. -/
theorem tendstoInDistribution_id_iff {ι Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → E) (l : Filter ι)
    (μ : ProbabilityMeasure E) :
    TendstoInDistribution X l id (fun _ => P) (μ : Measure E) ↔
      (∀ i, AEMeasurable (X i) P) ∧
        Tendsto (β := ProbabilityMeasure E) (fun i => (⟨P.map (X i), inferInstance⟩ : ProbabilityMeasure E)) l (𝓝 μ) := by
  have hid : (⟨(μ : Measure E).map id, inferInstance⟩ : ProbabilityMeasure E) = μ :=
    Subtype.ext Measure.map_id
  constructor
  · intro h
    exact ⟨h.forall_aemeasurable, by simpa only [hid] using h.tendsto⟩
  · rintro ⟨hX, hlim⟩
    exact ⟨hX, measurable_id.aemeasurable, by simpa only [hid] using hlim⟩

/-- Tightness along every divergent scale sequence and the Brownian finite-dimensional
limit imply full real-parameter convergence to any Wiener law. -/
theorem tendstoInDistribution_scalePath_of_tight
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {t : ℝ} (ht : 0 < t) (x : Plane) (φ : TestFn)
    (hφ : ∀ y, 0 ≤ φ y) (hφ1 : (∫ y, φ y) = 1) (S : ℝ≥0)
    (hTight : ∀ u : ℕ → Set.Ioi (0 : ℝ),
      Tendsto (fun n => (u n : ℝ)) atTop atTop →
      IsTightMeasureSet (Set.range (fun n =>
        P.map (fun ω => scalePath S (H t 0 ω) φ x (u n)))))
    {μ : ProbabilityMeasure (ScalePath S)} (hμ : IsWienerLaw S μ) :
    TendstoInDistribution (fun (L : Set.Ioi (0 : ℝ)) ω => scalePath S (H t 0 ω) φ x L)
      atTop id (fun _ => P) (μ : Measure (ScalePath S)) := by
  apply (tendstoInDistribution_atTop_iff_forall_seq
    (fun L => aemeasurable_scalePath ϑ P Z hZ H hH ht x φ S L) measurable_id.aemeasurable).mpr
  intro u hu
  apply (tendstoInDistribution_id_iff P _ atTop μ).mpr
  refine ⟨fun n => aemeasurable_scalePath ϑ P Z hZ H hH ht x φ S (u n), ?_⟩
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, ν, hms, hν⟩ := exists_subseq_limit P
    (fun n ω => scalePath S (H t 0 ω) φ x (u (ns n)))
    (fun n => aemeasurable_scalePath ϑ P Z hZ H hH ht x φ S (u (ns n)))
    (hTight (fun n => u (ns n)) (hu.comp hns))
  have hνW := isWienerLaw_of_subseq_limit ϑ P Z hZ H hH ht x φ hφ hφ1 S
    (fun n => u (ns (ms n))) (hu.comp (hns.comp hms.tendsto_atTop)) ν hν
  have hνeq : ν = μ := eq_of_isWienerLaw ν μ hνW hμ
  refine ⟨ms, ?_⟩
  have hh := ((tendstoInDistribution_id_iff P _ atTop ν).mp hν).2
  exact hνeq ▸ hh

/-- A single tight divergent KPZ scale sequence constructs the unique Wiener law
on the prescribed continuous-path space. -/
theorem existsUnique_wienerLaw_of_tight
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {t : ℝ} (ht : 0 < t) (x : Plane) (φ : TestFn)
    (hφ : ∀ y, 0 ≤ φ y) (hφ1 : (∫ y, φ y) = 1) (S : ℝ≥0)
    (u : ℕ → Set.Ioi (0 : ℝ)) (hu : Tendsto (fun n => (u n : ℝ)) atTop atTop)
    (hTight : IsTightMeasureSet (Set.range (fun n =>
      P.map (fun ω => scalePath S (H t 0 ω) φ x (u n))))) :
    ∃! μ : ProbabilityMeasure (ScalePath S), IsWienerLaw S μ := by
  obtain ⟨v, μ, hv, hμ⟩ := exists_subseq_limit P
    (fun n ω => scalePath S (H t 0 ω) φ x (u n))
    (fun n => aemeasurable_scalePath ϑ P Z hZ H hH ht x φ S (u n)) hTight
  have hW := isWienerLaw_of_subseq_limit ϑ P Z hZ H hH ht x φ hφ hφ1 S
    (fun n => u (v n)) (hu.comp hv.tendsto_atTop) μ hμ
  exact ⟨μ, hW, fun ν hν => eq_of_isWienerLaw ν μ hν hW⟩

end Critical2DKPZ.Extensions.ScaleLimit
