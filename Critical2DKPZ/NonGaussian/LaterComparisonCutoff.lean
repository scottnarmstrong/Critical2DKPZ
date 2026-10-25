/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.Inputs
public import Critical2DKPZ.RandomMeasure.GeneralTests
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Tactic

/-! # Cutoffs separating mutually singular measures -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported MeasureTheory ENNReal
open CompactlySupportedContinuousMap

namespace Critical2DKPZ.NonGaussian

open Critical2DKPZ.RandomMeasure

/-- The countable dense family of compact tests, clipped pointwise to `[0,1]`. -/
def boundedDenseVagueTest (K : CompactExhaustion Plane) (n j : ℕ) : C_c(Plane, ℝ) :=
  vagueMassTest K n ⊓ (0 ⊔ denseVagueTest K n j)

/-- The clipped dense tests take values in `[0,1]`. -/
theorem boundedDenseVagueTest_bounds (K : CompactExhaustion Plane) (n j : ℕ) (x : Plane) :
    0 ≤ boundedDenseVagueTest K n j x ∧ boundedDenseVagueTest K n j x ≤ 1 := by
  constructor
  · change 0 ≤ min (vagueMassTest K n x) (max 0 (denseVagueTest K n j x))
    exact le_min ((vagueMassTest_spec K n).1 x) (le_max_left 0 _)
  · change min (vagueMassTest K n x) (max 0 (denseVagueTest K n j x)) ≤ 1
    exact (min_le_left _ _).trans ((vagueMassTest_spec K n).2.1 x)


/-- Every `[0,1]`-valued compact test supported in one exhaustion window is uniformly approximated
by a member of the clipped countable family. -/
theorem exists_boundedDenseVagueTest_approx (K : CompactExhaustion Plane) (n : ℕ)
    (f : C_c(Plane, ℝ)) (hf : tsupport (f : Plane → ℝ) ⊆ K n)
    (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ j : ℕ, ∀ x, |boundedDenseVagueTest K n j x - f x| < ε := by
  obtain ⟨j, hj⟩ := exists_denseVagueTest_approx K n f hf ε hε
  refine ⟨j, fun x => ?_⟩
  by_cases hx : x ∈ K n
  · have happrox := hj x hx
    have hmass : vagueMassTest K n x = 1 := (vagueMassTest_spec K n).2.2.1 x hx
    have hclip : |min 1 (max 0 (denseVagueTest K n j x)) - f x| < ε := by
      by_cases hg0 : denseVagueTest K n j x < 0
      · have hfε : f x < ε := by
          have hlow := (abs_lt.mp happrox).1
          linarith
        simp only [max_eq_left (le_of_lt hg0), min_eq_right (by norm_num : (0:ℝ) ≤ 1)]
        simpa [abs_of_nonneg (h0 x)] using hfε
      · have hg0' : 0 ≤ denseVagueTest K n j x := le_of_not_gt hg0
        by_cases hg1 : 1 < denseVagueTest K n j x
        · have hupper : 1 - f x < ε := by
            have hupper' := (abs_lt.mp happrox).2
            linarith
          simp only [max_eq_right hg0', min_eq_left (le_of_lt hg1)]
          simpa [abs_of_nonneg (sub_nonneg.mpr (h1 x))] using hupper
        · have hg1' : denseVagueTest K n j x ≤ 1 := le_of_not_gt hg1
          simp only [max_eq_right hg0', min_eq_right hg1']
          exact happrox
    change |min (vagueMassTest K n x) (max 0 (denseVagueTest K n j x)) - f x| < ε
    rw [hmass]
    exact hclip
  · have hfzero : f x = 0 := by
      by_contra hne
      exact hx (hf (subset_tsupport _ hne))
    have hgzero : denseVagueTest K n j x = 0 := by
      by_contra hne
      exact hx ((denseVagueTest_support K n j) (subset_tsupport _ hne))
    change |min (vagueMassTest K n x) (max 0 (denseVagueTest K n j x)) - f x| < ε
    rw [hgzero, max_self, hfzero]
    rw [min_eq_right ((vagueMassTest_spec K n).1 x)]
    simp only [sub_zero, abs_zero]
    exact hε


/-- Uniform approximation on a compact set bounds the pairing error against a locally finite measure by the approximation error times the measure of that set. -/
theorem compact_test_pairing_error (K : CompactExhaustion Plane) (n : ℕ)
    (μ : Measure Plane) [IsLocallyFiniteMeasure μ] (f g : C_c(Plane, ℝ))
    (hf : tsupport (f : Plane → ℝ) ⊆ K n)
    (hg : tsupport (g : Plane → ℝ) ⊆ K n)
    (ε : ℝ) (happrox : ∀ x ∈ K n, |f x - g x| ≤ ε) :
    |(∫ x, f x ∂μ) - ∫ x, g x ∂μ| ≤ ε * μ.real (K n) := by
  let μR : RandomMeasure.PositiveRadonMeasure Plane := ⟨μ, inferInstance⟩
  have h := RandomMeasure.vague_test_integral_error K μR n f g hf hg ε happrox
  simpa [μR] using h

/-- Multiplying uniformly close bounded tests by a fixed cutoff preserves the compact-window
pairing error estimate. -/
theorem cutoff_product_pairing_error (K : CompactExhaustion Plane) (n : ℕ)
    (μ : Measure Plane) [IsLocallyFiniteMeasure μ]
    (φ f g : C_c(Plane, ℝ)) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hφsupport : tsupport (φ : Plane → ℝ) ⊆ K n)
    (δ : ℝ) (happrox : ∀ x, |g x - f x| ≤ δ) :
    |(∫ x, φ x * g x ∂μ) - ∫ x, φ x * f x ∂μ| ≤ δ * μ.real (K n) := by
  have hleft : tsupport ((φ * g : C_c(Plane, ℝ)) : Plane → ℝ) ⊆ K n :=
    (tsupport_mul_subset_left (f := (φ : Plane → ℝ)) (g := (g : Plane → ℝ))).trans hφsupport
  have hright : tsupport ((φ * f : C_c(Plane, ℝ)) : Plane → ℝ) ⊆ K n :=
    (tsupport_mul_subset_left (f := (φ : Plane → ℝ)) (g := (f : Plane → ℝ))).trans hφsupport
  apply compact_test_pairing_error K n μ (φ * g) (φ * f) hleft hright δ
  intro x hx
  calc
    |φ x * g x - φ x * f x| = φ x * |g x - f x| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (hφ x).1]
    _ ≤ 1 * |g x - f x| :=
      mul_le_mul_of_nonneg_right (hφ x).2 (abs_nonneg _)
    _ ≤ 1 * δ := mul_le_mul_of_nonneg_left (happrox x) (by norm_num)
    _ = δ := one_mul _

/-- If finite `μ` and `ν` are mutually singular, a compact subset of a `ν`-null set
carries all but an arbitrarily small amount of `μ`. -/
theorem exists_compact_singular_mass_approx (μ ν : Measure Plane) [IsFiniteMeasure μ]
    (hSing : Measure.MutuallySingular μ ν) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ K : Set Plane, IsCompact K ∧ K ⊆ hSing.nullSetᶜ ∧
      μ (hSing.nullSetᶜ \ K) < ε := by
  have hF : MeasurableSet hSing.nullSetᶜ := hSing.measurableSet_nullSet.compl
  have hμF : μ (hSing.nullSetᶜ) ≠ ∞ := measure_ne_top μ _
  obtain ⟨K, hKF, hKcompact, hsmall⟩ :=
    hF.exists_isCompact_sdiff_lt hμF (ne_of_gt hε)
  exact ⟨K, hKcompact, hKF, hsmall⟩

/-- A singular pair admits a compact set carrying almost all of `μ` inside the `ν`-null side, with
an open neighborhood of small `ν`-mass. -/
theorem exists_compact_open_singular_window (μ ν : Measure Plane) [IsFiniteMeasure μ]
    [IsLocallyFiniteMeasure ν] (hSing : Measure.MutuallySingular μ ν)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ K V : Set Plane, IsCompact K ∧ K ⊆ hSing.nullSetᶜ ∧
      μ (hSing.nullSetᶜ \ K) < ε ∧ IsOpen V ∧ K ⊆ V ∧ ν V < ε := by
  obtain ⟨K, hKcompact, hKside, hKsmall⟩ :=
    exists_compact_singular_mass_approx μ ν hSing ε hε
  have hνK : ν K = 0 := measure_mono_null hKside hSing.measure_compl_nullSet
  obtain ⟨V, hKV, hVopen, hVsmall⟩ :=
    hKcompact.exists_isOpen_lt_of_lt (μ := ν) ε (by rw [hνK]; exact hε)
  exact ⟨K, V, hKcompact, hKside, hKsmall, hVopen, hKV, hVsmall⟩

/-- Mutually singular measures admit a compactly supported cutoff equal to one on a compact set
carrying almost all of `μ`, with support in an open set of small `ν`-mass. -/
theorem exists_singular_continuous_cutoff (μ ν : Measure Plane) [IsFiniteMeasure μ]
    [IsLocallyFiniteMeasure ν] (hSing : Measure.MutuallySingular μ ν)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ K V : Set Plane, ∃ f : C_c(Plane, ℝ),
      IsCompact K ∧ K ⊆ hSing.nullSetᶜ ∧ μ (hSing.nullSetᶜ \ K) < ε ∧
      IsOpen V ∧ K ⊆ V ∧ ν V < ε ∧
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧ (∀ x ∈ K, f x = 1) ∧
      tsupport (f : Plane → ℝ) ⊆ V := by
  obtain ⟨K, V, hKcompact, hKside, hKsmall, hVopen, hKV, hVsmall⟩ :=
    exists_compact_open_singular_window μ ν hSing ε hε
  obtain ⟨g, hgK, hgcompact, hgsupport, hg01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hKcompact hVopen hKV
  let f : C_c(Plane, ℝ) := ⟨g, hgcompact⟩
  refine ⟨K, V, f, hKcompact, hKside, hKsmall, hVopen, hKV, hVsmall, ?_, ?_, ?_⟩
  · exact fun x => hg01 x
  · exact fun _ hx => hgK hx
  · exact hgsupport

/-- Mutually singular measures admit a compact cutoff with arbitrarily small `ν`-integral
and arbitrarily small `μ`-integral of its complement multiplied by a fixed `[0,1]`-valued compact test;
both integrals are finite. -/
theorem singular_cutoff_integral_bounds (μ ν : Measure Plane) [IsFiniteMeasure μ]
    [IsLocallyFiniteMeasure ν] (hSing : Measure.MutuallySingular μ ν)
    (φ₀ : C_c(Plane, ℝ)) (hφ₀ : ∀ x, 0 ≤ φ₀ x ∧ φ₀ x ≤ 1)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ K V : Set Plane, ∃ f : C_c(Plane, ℝ),
      IsCompact K ∧ K ⊆ hSing.nullSetᶜ ∧ μ (hSing.nullSetᶜ \ K) < ε ∧
      IsOpen V ∧ K ⊆ V ∧ ν V < ε ∧
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧ (∀ x ∈ K, f x = 1) ∧
      tsupport (f : Plane → ℝ) ⊆ V ∧
      Integrable (fun x => f x) ν ∧
      (∫ x, f x ∂ν) ≤ ν.real V ∧
      Integrable (fun x => φ₀ x * (1 - f x)) μ ∧
      (∫ x, φ₀ x * (1 - f x) ∂μ) ≤ μ.real (hSing.nullSetᶜ \ K) := by
  obtain ⟨K, V, f, hKcompact, hKside, hKsmall, hVopen, hKV, hVsmall,
      hf01, hfK, hfsupp⟩ := exists_singular_continuous_cutoff μ ν hSing ε hε
  have hfν : Integrable (fun x => f x) ν :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hνVtop : ν V < ∞ := lt_of_lt_of_le hVsmall le_top
  have hνrestr : IsFiniteMeasure (ν.restrict V) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact hνVtop
  have hνVconst : Integrable (fun _ : Plane => (1 : ℝ)) (ν.restrict V) :=
    integrable_const_iff.2 (Or.inr hνrestr)
  have hVindicator : Integrable (V.indicator fun _ : Plane => (1 : ℝ)) ν :=
    (integrable_indicator_iff hVopen.measurableSet).2 hνVconst
  have hfle : ∀ x, f x ≤ V.indicator (fun _ : Plane => (1 : ℝ)) x := by
    intro x
    by_cases hxV : x ∈ V
    · rw [Set.indicator_of_mem hxV]
      exact (hf01 x).2
    · have hfx : f x = 0 := by
        by_contra hne
        exact hxV (hfsupp (subset_tsupport _ hne))
      rw [Set.indicator_of_notMem hxV, hfx]
  have hfupper : (∫ x, f x ∂ν) ≤ ν.real V := by
    calc
      (∫ x, f x ∂ν) ≤ ∫ x, V.indicator (fun _ : Plane => (1 : ℝ)) x ∂ν :=
        integral_mono hfν hVindicator hfle
      _ = ν.real V := by
        simpa only [smul_eq_mul, mul_one] using
          (integral_indicator_const (1 : ℝ) (μ := ν) (s := V) hVopen.measurableSet)
  let q : C_c(Plane, ℝ) := φ₀ - φ₀ * f
  have hqeq : (fun x => q x) = (fun x => φ₀ x * (1 - f x)) := by
    funext x
    simp only [q, CompactlySupportedContinuousMap.sub_apply,
      CompactlySupportedContinuousMap.mul_apply]
    ring
  have hqμ : Integrable (fun x => q x) μ :=
    q.continuous.integrable_of_hasCompactSupport q.hasCompactSupport
  have hKc : MeasurableSet Kᶜ := hKcompact.isClosed.measurableSet.compl
  have hKcindicator : Integrable (Kᶜ.indicator fun _ : Plane => (1 : ℝ)) μ :=
    (integrable_indicator_iff hKc).2 (integrable_const 1)
  have hqle : ∀ x, q x ≤ Kᶜ.indicator (fun _ : Plane => (1 : ℝ)) x := by
    intro x
    by_cases hxK : x ∈ K
    · rw [Set.indicator_of_notMem (by simpa using hxK)]
      rw [congrFun hqeq x, hfK x hxK]
      simp
    · rw [Set.indicator_of_mem (by simpa using hxK), congrFun hqeq x]
      calc
        φ₀ x * (1 - f x) ≤ φ₀ x * 1 :=
          mul_le_mul_of_nonneg_left (by linarith [(hf01 x).1]) (hφ₀ x).1
        _ = φ₀ x := mul_one _
        _ ≤ 1 := (hφ₀ x).2
  have hKcsum : μ Kᶜ ≤ μ (hSing.nullSetᶜ \ K) := by
    have hsubset : Kᶜ ⊆ hSing.nullSet ∪ (hSing.nullSetᶜ \ K) := by
      intro x hxK
      by_cases hxE : x ∈ hSing.nullSet
      · exact Or.inl hxE
      · exact Or.inr ⟨hxE, hxK⟩
    calc
      μ Kᶜ ≤ μ (hSing.nullSet ∪ (hSing.nullSetᶜ \ K)) := measure_mono hsubset
      _ ≤ μ hSing.nullSet + μ (hSing.nullSetᶜ \ K) := measure_union_le _ _
      _ = μ (hSing.nullSetᶜ \ K) := by rw [hSing.measure_nullSet, zero_add]
  have hqbound : (∫ x, q x ∂μ) ≤ μ.real (hSing.nullSetᶜ \ K) := by
    calc
      (∫ x, q x ∂μ) ≤ ∫ x, Kᶜ.indicator (fun _ : Plane => (1 : ℝ)) x ∂μ :=
        integral_mono hqμ hKcindicator hqle
      _ = μ.real Kᶜ := by
        simpa only [smul_eq_mul, mul_one] using
          (integral_indicator_const (1 : ℝ) (μ := μ) (s := Kᶜ) hKc)
      _ ≤ μ.real (hSing.nullSetᶜ \ K) := by
        exact ENNReal.toReal_mono (measure_ne_top μ (hSing.nullSetᶜ \ K)) hKcsum
  have hqeqAE : (fun x => q x) =ᵐ[μ] fun x => φ₀ x * (1 - f x) :=
    Filter.Eventually.of_forall fun x => congrFun hqeq x
  have hresint : Integrable (fun x => φ₀ x * (1 - f x)) μ := hqμ.congr hqeqAE
  have hresbound : (∫ x, φ₀ x * (1 - f x) ∂μ) ≤ μ.real (hSing.nullSetᶜ \ K) := by
    calc
      (∫ x, φ₀ x * (1 - f x) ∂μ) = ∫ x, q x ∂μ := integral_congr_ae hqeqAE.symm
      _ ≤ μ.real (hSing.nullSetᶜ \ K) := hqbound
  exact ⟨K, V, f, hKcompact, hKside, hKsmall, hVopen, hKV, hVsmall,
    hf01, hfK, hfsupp, hfν, hfupper, hresint, hresbound⟩

end Critical2DKPZ.NonGaussian

end
