/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.RandomMeasure.GeneralBorel
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.Compact

/-! On a locally compact second-countable Hausdorff space, uniform bounds on mass over a compact exhaustion give a vaguely convergent subsequence. -/

@[expose] public section

open MeasureTheory Set Topology Filter
open scoped CompactlySupported

noncomputable section

set_option linter.style.haveILetI false

namespace Critical2DKPZ.RandomMeasure

/-- A compactly supported test pairing is bounded by its sup norm times the
mass of any compact window containing its support. -/
theorem vague_test_pairing_abs_le_window_mass {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X)
    (μ : PositiveRadonMeasure X) (n : ℕ) (f : C_c(X, ℝ))
    (hf : tsupport (f : X → ℝ) ⊆ K n) :
    |vaguePairing μ f| ≤
      ‖vagueTestRestriction K ⟨f, hf⟩‖ * μ.measure.real (K n) := by
  let fK := vagueTestRestriction K ⟨f, hf⟩
  have hpoint : ∀ x ∈ K n, |f x| ≤ ‖fK‖ := by
    intro x hx
    have h := fK.norm_coe_le_norm ⟨x, hx⟩
    have h' : ‖f x‖ ≤ ‖fK‖ := by
      simpa [fK, vagueTestRestriction, ContinuousMap.restrict_apply] using h
    simpa only [Real.norm_eq_abs] using h'
  have herr := vague_test_integral_error K μ n f 0 hf (by simp) ‖fK‖ (by
    intro x hx
    simp only [CompactlySupportedContinuousMap.zero_apply, sub_zero]
    exact hpoint x hx)
  simpa [vaguePairing, fK] using herr

/-- Uniform compact-window mass bounds yield one subsequence along which every integral in the countable compact-test family converges. -/
theorem exists_strictMono_subseq_countableReadout_tendsto {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X)
    (μ : ℕ → PositiveRadonMeasure X)
    (hmass : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
      (μ n).measure.real (K k) ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : (ℕ × ℕ) ⊕ ℕ → ℝ,
      Tendsto (fun n => countableVagueReadout K (μ (φ n))) atTop (𝓝 v) := by
  letI : MetricSpace ((ℕ × ℕ) ⊕ ℕ → ℝ) := PiCountable.metricSpace
  letI : TopologicalSpace ((ℕ × ℕ) ⊕ ℕ → ℝ) := Pi.topologicalSpace
  have hcoord : ∀ i : (ℕ × ℕ) ⊕ ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
      |countableVagueReadout K (μ n) i| ≤ B := by
    intro i
    let f := countableVagueTest K i
    obtain ⟨k, hk⟩ := exists_vagueExhaustionWindow_support K f
    obtain ⟨C, hC⟩ := hmass k
    let fK := vagueTestRestriction K ⟨f, hk⟩
    let B : ℝ := ‖fK‖ * max C 0
    refine ⟨B, mul_nonneg (norm_nonneg _) (le_max_right C 0), ?_⟩
    intro n
    have hmass' : (μ n).measure.real (K k) ≤ max C 0 :=
      (hC n).trans (le_max_left C 0)
    calc
      |countableVagueReadout K (μ n) i| = |vaguePairing (μ n) f| := by rfl
      _ ≤ ‖fK‖ * (μ n).measure.real (K k) :=
        vague_test_pairing_abs_le_window_mass K (μ n) k f hk
      _ ≤ B := by
        dsimp [B]
        exact mul_le_mul_of_nonneg_left hmass' (norm_nonneg _)
  choose B hB_nonneg hB using hcoord
  let T : Set ((ℕ × ℕ) ⊕ ℕ → ℝ) :=
    {v | ∀ i, v i ∈ Set.Icc (-B i) (B i)}
  have hT : IsCompact T := by
    change IsCompact {v : (ℕ × ℕ) ⊕ ℕ → ℝ |
      ∀ i, v i ∈ Set.Icc (-B i) (B i)}
    exact isCompact_pi_infinite fun i => isCompact_Icc
  have hseq : ∀ n : ℕ, countableVagueReadout K (μ n) ∈ T := by
    intro n
    change ∀ i, countableVagueReadout K (μ n) i ∈ Set.Icc (-B i) (B i)
    intro i
    rw [Set.mem_Icc]
    exact abs_le.mp (hB i n)
  obtain ⟨v, hv, φ, hφ, hlim⟩ := hT.tendsto_subseq hseq
  exact ⟨φ, hφ, v, hlim⟩

/-- Convergence of the selected test integrals and uniform compact-window mass bounds make every compact-test integral a Cauchy sequence. -/
theorem vaguePairing_cauchySeq_of_countableReadout_tendsto {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X)
    (μ : ℕ → PositiveRadonMeasure X)
    (hmass : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
      (μ n).measure.real (K k) ≤ C)
    {v : (ℕ × ℕ) ⊕ ℕ → ℝ}
    (hread : Tendsto (fun n => countableVagueReadout K (μ n)) atTop (𝓝 v))
    (f : C_c(X, ℝ)) :
    CauchySeq (fun n => vaguePairing (μ n) f) := by
  have hcoord : ∀ i : (ℕ × ℕ) ⊕ ℕ,
      Tendsto (fun n => countableVagueReadout K (μ n) i) atTop (𝓝 (v i)) := by
    intro i
    exact ((continuous_apply i).tendsto v).comp hread
  have hcoordCauchy (i : (ℕ × ℕ) ⊕ ℕ) :
      CauchySeq (fun n => countableVagueReadout K (μ n) i) := (hcoord i).cauchySeq
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨k, hf⟩ := exists_vagueExhaustionWindow_support K f
  obtain ⟨C, hC⟩ := hmass k
  let C' : ℝ := max C 0
  have hmass' (n : ℕ) : (μ n).measure.real (K k) ≤ C' :=
    (hC n).trans (le_max_left C 0)
  let η : ℝ := ε / (3 * (C' + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηC : η * C' ≤ ε / 3 := by
    dsimp [η]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity)).2
    have hC_le : C' ≤ C' + 1 := by linarith
    calc
      ε * C' ≤ ε * (C' + 1) := mul_le_mul_of_nonneg_left hC_le hε.le
      _ = ε / 3 * (3 * (C' + 1)) := by ring
  obtain ⟨j, hj⟩ := exists_denseVagueTest_approx K k f hf η hη
  let g := denseVagueTest K k j
  have hg : tsupport (g : X → ℝ) ⊆ K k := denseVagueTest_support K k j
  have herr (n : ℕ) : |vaguePairing (μ n) f - vaguePairing (μ n) g| ≤ η * C' := by
    exact (vague_test_integral_error K (μ n) k f g hf hg η (fun x hx => by
      simpa only [abs_sub_comm] using (hj x hx).le)).trans
        (mul_le_mul_of_nonneg_left (hmass' n) hη.le)
  let i : (ℕ × ℕ) ⊕ ℕ := .inl (k, j)
  have htestCauchy : CauchySeq (fun n => vaguePairing (μ n) g) := by
    convert hcoordCauchy i using 1
    funext n
    rfl
  obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp htestCauchy) (ε / 3) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hleft : dist (vaguePairing (μ m) f) (vaguePairing (μ m) g) ≤ η * C' := by
    rw [Real.dist_eq]
    exact herr m
  have hmiddle : dist (vaguePairing (μ m) g) (vaguePairing (μ n) g) < ε / 3 := by
    simpa [countableVagueReadout, countableVagueTest, g, i, Real.dist_eq] using
      hN m hm n hn
  have hright : dist (vaguePairing (μ n) g) (vaguePairing (μ n) f) ≤ η * C' := by
    rw [Real.dist_eq, abs_sub_comm]
    exact herr n
  calc
    dist (vaguePairing (μ m) f) (vaguePairing (μ n) f) ≤
        dist (vaguePairing (μ m) f) (vaguePairing (μ m) g) +
          dist (vaguePairing (μ m) g) (vaguePairing (μ n) g) +
          dist (vaguePairing (μ n) g) (vaguePairing (μ n) f) :=
      dist_triangle4 _ _ _ _
    _ < ε := by linarith

/-- The limit of a compact-test integral along a sequence with uniformly bounded compact-window masses and convergent selected test integrals. -/
noncomputable def vagueLimitValue {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (μ : ℕ → PositiveRadonMeasure X)
    (f : C_c(X, ℝ)) : ℝ :=
  Filter.limUnder atTop (fun n => vaguePairing (μ n) f)

/-- The selected subsequence of test pairings converges to the limiting functional. -/
theorem tendsto_vagueLimitValue {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X)
    (μ : ℕ → PositiveRadonMeasure X)
    (hmass : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
      (μ n).measure.real (K k) ≤ C)
    {v : (ℕ × ℕ) ⊕ ℕ → ℝ}
    (hread : Tendsto (fun n => countableVagueReadout K (μ n)) atTop (𝓝 v))
    (f : C_c(X, ℝ)) :
    Tendsto (fun n => vaguePairing (μ n) f) atTop (𝓝 (vagueLimitValue μ f)) :=
  (vaguePairing_cauchySeq_of_countableReadout_tendsto K μ hmass hread f).tendsto_limUnder

/-- The pointwise limit of vague pairings is a linear functional on `C_c`. -/
noncomputable def vagueLimitLinearMap {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X)
    (μ : ℕ → PositiveRadonMeasure X)
    (hmass : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
      (μ n).measure.real (K k) ≤ C)
    {v : (ℕ × ℕ) ⊕ ℕ → ℝ}
    (hread : Tendsto (fun n => countableVagueReadout K (μ n)) atTop (𝓝 v)) :
    C_c(X, ℝ) →ₗ[ℝ] ℝ where
  toFun := vagueLimitValue μ
  map_add' f g := by
    have hsum : Tendsto (fun n => vaguePairing (μ n) (f + g)) atTop
        (𝓝 (vagueLimitValue μ f + vagueLimitValue μ g)) := by
      have hfun : (fun n => vaguePairing (μ n) (f + g)) =
          fun n => vaguePairing (μ n) f + vaguePairing (μ n) g := by
        funext n
        rw [vaguePairing, vaguePairing, vaguePairing]
        exact integral_add (integrable_vagueTest (μ n) f) (integrable_vagueTest (μ n) g)
      rw [hfun]
      exact (tendsto_vagueLimitValue K μ hmass hread f).add
        (tendsto_vagueLimitValue K μ hmass hread g)
    exact tendsto_nhds_unique (tendsto_vagueLimitValue K μ hmass hread (f + g)) hsum
  map_smul' c f := by
    have hsmul : Tendsto (fun n => vaguePairing (μ n) (c • f)) atTop
        (𝓝 (c • vagueLimitValue μ f)) := by
      have hfun : (fun n => vaguePairing (μ n) (c • f)) =
          fun n => c • vaguePairing (μ n) f := by
        funext n
        change (∫ x, c • f x ∂(μ n).measure) =
          c • ∫ x, f x ∂(μ n).measure
        exact integral_smul c f
      rw [hfun]
      exact (tendsto_vagueLimitValue K μ hmass hread f).const_smul c
    exact tendsto_nhds_unique (tendsto_vagueLimitValue K μ hmass hread (c • f)) hsmul

/-- The limit functional is positive, so Riesz representation applies. -/
noncomputable def vagueLimitPositiveLinearMap {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X)
    (μ : ℕ → PositiveRadonMeasure X)
    (hmass : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
      (μ n).measure.real (K k) ≤ C)
    {v : (ℕ × ℕ) ⊕ ℕ → ℝ}
    (hread : Tendsto (fun n => countableVagueReadout K (μ n)) atTop (𝓝 v)) :
    C_c(X, ℝ) →ₚ[ℝ] ℝ where
  toLinearMap := vagueLimitLinearMap K μ hmass hread
  monotone' := by
    intro f g hfg
    have hpos_mem : vagueLimitValue μ (g - f) ∈ Set.Ici (0 : ℝ) := by
      have hclosed : IsClosed (Set.Ici (0 : ℝ)) := isClosed_Ici
      have hlim := tendsto_vagueLimitValue K μ hmass hread (g - f)
      have hnonneg : ∀ n, vaguePairing (μ n) (g - f) ∈ Set.Ici (0 : ℝ) := by
        intro n
        change 0 ≤ ∫ x, (g - f) x ∂(μ n).measure
        exact integral_nonneg (fun x => sub_nonneg.mpr (hfg x))
      exact hclosed.mem_of_tendsto hlim (Eventually.of_forall hnonneg)
    have hpos : 0 ≤ vagueLimitValue μ (g - f) := hpos_mem
    have hsub := (vagueLimitLinearMap K μ hmass hread).map_sub g f
    exact (sub_nonneg.mp (hsub ▸ hpos))

/-- Riesz representation of a positive functional is finite on compact sets. -/
theorem rieszMeasure_isFiniteOnCompacts {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X)
    (Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ) :
    IsFiniteMeasureOnCompacts (RealRMK.rieszMeasure Λ) := by
  refine ⟨fun L hL => ?_⟩
  obtain ⟨n, hLn⟩ := K.exists_superset_of_isCompact hL
  have hwindow : RealRMK.rieszMeasure Λ (K n) ≤
      ENNReal.ofReal (Λ (vagueMassTest K n)) :=
    RealRMK.rieszMeasure_le_of_eq_one Λ
      (vagueMassTest_spec K n).1 (K.isCompact n)
      (fun x hx => (vagueMassTest_spec K n).2.2.1 x hx)
  calc
    RealRMK.rieszMeasure Λ L ≤ RealRMK.rieszMeasure Λ (K n) := measure_mono hLn
    _ ≤ ENNReal.ofReal (Λ (vagueMassTest K n)) := hwindow
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- The Riesz measure of the limiting positive functional is locally finite and is the vague limit of the extracted sequence. -/
noncomputable def vagueLimitMeasure {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X)
    (μ : ℕ → PositiveRadonMeasure X)
    (hmass : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
      (μ n).measure.real (K k) ≤ C)
    {v : (ℕ × ℕ) ⊕ ℕ → ℝ}
    (hread : Tendsto (fun n => countableVagueReadout K (μ n)) atTop (𝓝 v)) :
    PositiveRadonMeasure X := by
  let Λ := vagueLimitPositiveLinearMap K μ hmass hread
  let ν := RealRMK.rieszMeasure Λ
  have hfinite : IsFiniteMeasureOnCompacts ν := rieszMeasure_isFiniteOnCompacts K Λ
  letI : IsFiniteMeasureOnCompacts ν := hfinite
  have hlocallyFinite : IsLocallyFiniteMeasure ν := by infer_instance
  exact ⟨ν, hlocallyFinite⟩

/-- Integrating a compactly supported test against the limit measure gives the limiting functional. -/
@[simp]
theorem vagueLimitMeasure_pairing {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X)
    (μ : ℕ → PositiveRadonMeasure X)
    (hmass : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
      (μ n).measure.real (K k) ≤ C)
    {v : (ℕ × ℕ) ⊕ ℕ → ℝ}
    (hread : Tendsto (fun n => countableVagueReadout K (μ n)) atTop (𝓝 v))
    (f : C_c(X, ℝ)) :
    vaguePairing (vagueLimitMeasure K μ hmass hread) f = vagueLimitValue μ f := by
  change (∫ x, f x ∂RealRMK.rieszMeasure
    (vagueLimitPositiveLinearMap K μ hmass hread)) = vagueLimitValue μ f
  exact RealRMK.integral_rieszMeasure _ f

/-- Uniform local-mass bounds give relative sequential compactness in the
vague topology. -/
theorem exists_strictMono_subseq_vague_tendsto_of_localMassBound {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X)
    (μ : ℕ → PositiveRadonMeasure X)
    (hmass : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
      (μ n).measure.real (K k) ≤ C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ν : PositiveRadonMeasure X,
      Tendsto (fun n => μ (φ n)) atTop (𝓝 ν) := by
  obtain ⟨φ, hφ, v, hread⟩ :=
    exists_strictMono_subseq_countableReadout_tendsto K μ hmass
  let μ' : ℕ → PositiveRadonMeasure X := fun n => μ (φ n)
  have hmass' : ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
      (μ' n).measure.real (K k) ≤ C := by
    intro k
    obtain ⟨C, hC⟩ := hmass k
    exact ⟨C, fun n => hC (φ n)⟩
  have hread' : Tendsto (fun n => countableVagueReadout K (μ' n)) atTop (𝓝 v) := by
    simpa only [μ'] using hread
  let ν := vagueLimitMeasure K μ' hmass' hread'
  refine ⟨φ, hφ, ν, ?_⟩
  apply (tendsto_vague_iff_forall_test μ' ν).2
  intro f
  rw [vagueLimitMeasure_pairing K μ' hmass' hread']
  exact tendsto_vagueLimitValue K μ' hmass' hread' f

end Critical2DKPZ.RandomMeasure

end
