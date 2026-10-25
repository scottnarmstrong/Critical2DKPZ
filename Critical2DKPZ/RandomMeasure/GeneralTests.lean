/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.RandomMeasure.VagueTopology
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.UrysohnsLemma
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! A locally compact second-countable Hausdorff space has a countable determining family of compactly supported continuous tests, including cutoffs that bound mass on a compact exhaustion. -/

@[expose] public section

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped CompactlySupported ENNReal

noncomputable section

set_option linter.style.haveILetI false

namespace Critical2DKPZ.RandomMeasure

/-- A chosen compact exhaustion of a locally compact second-countable space. -/
noncomputable def vagueCompactExhaustion (X : Type*) [TopologicalSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X] : CompactExhaustion X :=
  CompactExhaustion.choice X

instance compactExhaustionWindowCompact {X : Type*} [TopologicalSpace X]
    (K : CompactExhaustion X) (n : ℕ) : CompactSpace (K n) :=
  isCompact_iff_compactSpace.mp (K.isCompact n)

instance compactExhaustionWindowSecondCountable {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X) (n : ℕ) :
    SecondCountableTopology (K n) :=
  Subtype.secondCountableTopology _

instance compactExhaustionWindowLocallyCompact {X : Type*} [TopologicalSpace X]
    [T2Space X] (K : CompactExhaustion X) (n : ℕ) : LocallyCompactSpace (K n) := by
  infer_instance

instance compactExhaustionWindowContinuousMapSecondCountable {X : Type*}
    [TopologicalSpace X] [SecondCountableTopology X] [T2Space X]
    (K : CompactExhaustion X) (n : ℕ) :
    SecondCountableTopology C(K n, ℝ) := by
  letI : CompactSpace (K n) := compactExhaustionWindowCompact K n
  letI : SecondCountableTopology (K n) := compactExhaustionWindowSecondCountable K n
  letI : LocallyCompactSpace (K n) := compactExhaustionWindowLocallyCompact K n
  exact ContinuousMap.instSecondCountableTopology

/-- Compactly supported tests whose support lies in one fixed exhaustion set. -/
abbrev SupportedVagueTest {X : Type*} [TopologicalSpace X]
    (K : CompactExhaustion X) (n : ℕ) :=
  {f : C_c(X, ℝ) // tsupport (f : X → ℝ) ⊆ K n}

/-- Restriction of a compactly supported test to an exhaustion window. -/
def vagueTestRestriction {X : Type*} [TopologicalSpace X]
    (K : CompactExhaustion X) {n : ℕ} (f : SupportedVagueTest K n) : C(K n, ℝ) :=
  f.val.toContinuousMap.restrict _

instance supportedVagueTestPseudoMetric {X : Type*} [TopologicalSpace X]
    (K : CompactExhaustion X) (n : ℕ) : PseudoMetricSpace (SupportedVagueTest K n) :=
  PseudoMetricSpace.induced (vagueTestRestriction K) inferInstance

instance supportedVagueTestSecondCountable {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [T2Space X] (K : CompactExhaustion X) (n : ℕ) :
    SecondCountableTopology (SupportedVagueTest K n) :=
  secondCountableTopology_induced _ _ (vagueTestRestriction K)

instance supportedVagueTestNonempty {X : Type*} [TopologicalSpace X]
    (K : CompactExhaustion X) (n : ℕ) : Nonempty (SupportedVagueTest K n) :=
  ⟨⟨0, by simp⟩⟩

/-- The `j`th member of the countable dense family of tests supported in the `n`th compact window. -/
def denseVagueTest {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [T2Space X]
    (K : CompactExhaustion X) (n j : ℕ) : C_c(X, ℝ) :=
  (denseSeq (SupportedVagueTest K n) j).val

/-- Each chosen vague test is supported in its specified exhaustion window. -/
theorem denseVagueTest_support {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [T2Space X]
    (K : CompactExhaustion X) (n j : ℕ) :
    tsupport (denseVagueTest K n j : X → ℝ) ⊆ K n :=
  (denseSeq (SupportedVagueTest K n) j).property

/-- The countable vague test family uniformly approximates tests supported in a fixed window. -/
theorem exists_denseVagueTest_approx {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [T2Space X] (K : CompactExhaustion X) (n : ℕ)
    (f : C_c(X, ℝ)) (hf : tsupport (f : X → ℝ) ⊆ K n)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ j : ℕ, ∀ x ∈ K n, |denseVagueTest K n j x - f x| < ε := by
  obtain ⟨j, hj⟩ := (denseRange_denseSeq (SupportedVagueTest K n)).exists_dist_lt
    ⟨f, hf⟩ hε
  refine ⟨j, fun x hx => ?_⟩
  have hb := ContinuousMap.dist_apply_le_dist
    (f := vagueTestRestriction K (denseSeq (SupportedVagueTest K n) j))
    (g := vagueTestRestriction K ⟨f, hf⟩) ⟨x, hx⟩
  exact (show |denseVagueTest K n j x - f x| ≤
      dist (denseSeq (SupportedVagueTest K n) j) ⟨f, hf⟩ by
        simpa only [Real.dist_eq, vagueTestRestriction, ContinuousMap.restrict_apply,
          denseVagueTest] using! hb).trans_lt (by simpa only [dist_comm] using hj)

/-- Every compactly supported test is supported in an exhaustion window. -/
theorem exists_vagueExhaustionWindow_support {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    (K : CompactExhaustion X) (f : C_c(X, ℝ)) :
    ∃ n, tsupport (f : X → ℝ) ⊆ K n := by
  exact K.exists_superset_of_isCompact (by
    simpa only [HasCompactSupport, tsupport] using f.hasCompactSupport)

/-- A positive compactly supported cutoff that is one on an exhaustion window. -/
theorem exists_vagueMassTest {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] (K : CompactExhaustion X) (n : ℕ) :
    ∃ g : C_c(X, ℝ), (∀ x, 0 ≤ g x) ∧
      (∀ x, g x ≤ 1) ∧ (∀ x ∈ K n, g x = 1) ∧
      tsupport (g : X → ℝ) ⊆ K (n + 1) := by
  obtain ⟨g, hg, hgc, hgsupport, h01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen
      (K.isCompact n) isOpen_interior (K.subset_interior_succ n)
  refine ⟨⟨g, hgc⟩, fun x => (h01 x).1, fun x => (h01 x).2, ?_, ?_⟩
  · exact hg
  · exact hgsupport.trans interior_subset

/-- The canonical positive cutoff associated with a compact exhaustion. -/
def vagueMassTest {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] (K : CompactExhaustion X) (n : ℕ) : C_c(X, ℝ) :=
  Classical.choose (exists_vagueMassTest K n)

/-- The chosen vague mass test is nonnegative and at least one on its window. -/
theorem vagueMassTest_spec {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] (K : CompactExhaustion X) (n : ℕ) :
    (∀ x, 0 ≤ vagueMassTest K n x) ∧
      (∀ x, vagueMassTest K n x ≤ 1) ∧
      (∀ x ∈ K n, vagueMassTest K n x = 1) ∧
      tsupport (vagueMassTest K n : X → ℝ) ⊆ K (n + 1) :=
  Classical.choose_spec (exists_vagueMassTest K n)

/-- Each compact-window mass is bounded by its positive cutoff integral. -/
theorem vague_window_mass_le_test {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [BorelSpace X]
    [T2Space X] [LocallyCompactSpace X]
    (K : CompactExhaustion X) (μ : PositiveRadonMeasure X) (n : ℕ) :
    μ.measure.real (K n) ≤ ∫ x, vagueMassTest K n x ∂μ.measure := by
  letI : IsLocallyFiniteMeasure μ.measure := μ.2
  let W := K n
  have hW : MeasurableSet W := (K.isCompact n).isClosed.measurableSet
  have hfinite : IsFiniteMeasure (μ.measure.restrict W) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact (K.isCompact n).measure_lt_top
  have hi : Integrable (W.indicator (fun _ => (1 : ℝ))) μ.measure :=
    (integrable_indicator_iff hW).mpr (integrable_const 1)
  calc
    μ.measure.real W = ∫ x, W.indicator (fun _ => (1 : ℝ)) x ∂μ.measure := by
      simpa only [smul_eq_mul, mul_one] using
        (integral_indicator_const (1 : ℝ) (μ := μ.measure) (s := W) hW).symm
    _ ≤ ∫ x, vagueMassTest K n x ∂μ.measure :=
      integral_mono hi (integrable_vagueTest μ (vagueMassTest K n)) (fun x => by
        by_cases hx : x ∈ W
        · rw [Set.indicator_of_mem hx, (vagueMassTest_spec K n).2.2.1 x hx]
        · simp only [Set.indicator_of_notMem hx]
          exact (vagueMassTest_spec K n).1 x)

/-- Uniform approximation on a common compact support bounds the integral
error by the mass of that compact window. -/
theorem vague_test_integral_error {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [BorelSpace X]
    [T2Space X] [LocallyCompactSpace X]
    (K : CompactExhaustion X) (μ : PositiveRadonMeasure X)
    (n : ℕ) (f g : C_c(X, ℝ))
    (hf : tsupport (f : X → ℝ) ⊆ K n)
    (hg : tsupport (g : X → ℝ) ⊆ K n)
    (ε : ℝ) (happrox : ∀ x ∈ K n, |f x - g x| ≤ ε) :
    |(∫ x, f x ∂μ.measure) - ∫ x, g x ∂μ.measure| ≤
      ε * μ.measure.real (K n) := by
  letI : IsLocallyFiniteMeasure μ.measure := μ.2
  let W := K n
  have hW : MeasurableSet W := (K.isCompact n).isClosed.measurableSet
  have hfinite : IsFiniteMeasure (μ.measure.restrict W) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact (K.isCompact n).measure_lt_top
  rw [← integral_sub (integrable_vagueTest μ f) (integrable_vagueTest μ g)]
  have heq : (∫ x in W, (f x - g x) ∂μ.measure) =
      ∫ x, (f x - g x) ∂μ.measure :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hf0 : f x = 0 := by
        by_contra hn
        exact hx (hf (subset_tsupport _ hn))
      have hg0 : g x = 0 := by
        by_contra hn
        exact hx (hg (subset_tsupport _ hn))
      simp [hf0, hg0])
  rw [← heq, ← Real.norm_eq_abs]
  have hb := norm_integral_le_of_norm_le_const (μ := μ.measure.restrict W)
    (f := fun x => f x - g x) (by
      filter_upwards [ae_restrict_mem hW] with x hx
      simpa only [Real.norm_eq_abs] using happrox x hx)
  simpa only [measureReal_def, Measure.restrict_apply_univ] using hb

/-- The countable family contains every positive local-mass control test. -/
def countableVagueTest {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    (K : CompactExhaustion X) : (ℕ × ℕ) ⊕ ℕ → C_c(X, ℝ)
  | .inl (n, j) => denseVagueTest K n j
  | .inr n => vagueMassTest K n

end Critical2DKPZ.RandomMeasure

end
