/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.LaterComparisonCutoff
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic

/-! # Countable test separation for singular measures -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped CompactlySupported MeasureTheory ENNReal
open CompactlySupportedContinuousMap

namespace Critical2DKPZ.NonGaussian

/-- An enumeration by `ℕ` of the clipped compact test family indexed by `ℕ × ℕ`. -/
def countableBoundedVagueTest (k : ℕ) : C_c(Plane, ℝ) :=
  boundedDenseVagueTest (RandomMeasure.vagueCompactExhaustion Plane)
    (Nat.unpair k).1 (Nat.unpair k).2

/-- For mutually singular measures, a test from the fixed countable family simultaneously makes the localized pairing against one measure and the complementary pairing against the other arbitrarily small. -/
theorem exists_boundedDenseVagueTest_singular_separation (μ ν : Measure Plane)
    [IsFiniteMeasure μ] [IsLocallyFiniteMeasure ν]
    (hSing : Measure.MutuallySingular μ ν) (φ : C_c(Plane, ℝ))
    (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ n j : ℕ,
      (∫ x, φ x * boundedDenseVagueTest
        (RandomMeasure.vagueCompactExhaustion Plane) n j x ∂ν) < ε ∧
      (∫ x, φ x * (1 - boundedDenseVagueTest
        (RandomMeasure.vagueCompactExhaustion Plane) n j x) ∂μ) < ε := by
  let e : ℝ := ε / 4
  have he : 0 < e := by dsimp [e]; positivity
  let eENN : ℝ≥0∞ := ENNReal.ofReal e
  have heENN : 0 < eENN := ENNReal.ofReal_pos.mpr he
  obtain ⟨K, V, f, _, _, hKsmall, _, _, hVsmall, hf01, _, _, hfint, hfbase,
      _, hresbase⟩ :=
    singular_cutoff_integral_bounds μ ν hSing φ hφ eENN heENN
  have hVne : ν V ≠ ∞ := (lt_of_lt_of_le hVsmall le_top).ne
  have hVreal : ν.real V < e := by
    have hlt : (ν V).toReal < eENN.toReal :=
      (ENNReal.toReal_lt_toReal hVne ENNReal.ofReal_ne_top).2 hVsmall
    simpa [Measure.real, eENN, ENNReal.toReal_ofReal he.le] using hlt
  have hKreal : μ.real (hSing.nullSetᶜ \ K) < e := by
    have hlt : (μ (hSing.nullSetᶜ \ K)).toReal < eENN.toReal :=
      (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).2 hKsmall
    simpa [Measure.real, eENN, ENNReal.toReal_ofReal he.le] using hlt
  let Q : CompactExhaustion Plane := RandomMeasure.vagueCompactExhaustion Plane
  obtain ⟨nf, hfsupp⟩ := RandomMeasure.exists_vagueExhaustionWindow_support Q f
  obtain ⟨nφ, hφsupp⟩ := RandomMeasure.exists_vagueExhaustionWindow_support Q φ
  let n : ℕ := max nf nφ
  have hfsupp' : tsupport (f : Plane → ℝ) ⊆ Q n :=
    hfsupp.trans (Q.subset (Nat.le_max_left nf nφ))
  have hφsupp' : tsupport (φ : Plane → ℝ) ⊆ Q n :=
    hφsupp.trans (Q.subset (Nat.le_max_right nf nφ))
  have hμmass : 0 ≤ μ.real (Q n) := measureReal_nonneg
  have hνmass : 0 ≤ ν.real (Q n) := measureReal_nonneg
  let den : ℝ := μ.real (Q n) + ν.real (Q n) + 1
  have hden : 0 < den := by dsimp [den]; linarith
  let δ : ℝ := ε / (8 * den)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδμ : δ * μ.real (Q n) ≤ ε / 8 := by
    have hm : μ.real (Q n) ≤ den := by dsimp [den]; linarith
    calc
      δ * μ.real (Q n) ≤ δ * den := mul_le_mul_of_nonneg_left hm hδ.le
      _ = ε / 8 := by dsimp [δ]; field_simp [ne_of_gt hden]
  have hδν : δ * ν.real (Q n) ≤ ε / 8 := by
    have hm : ν.real (Q n) ≤ den := by dsimp [den]; linarith
    calc
      δ * ν.real (Q n) ≤ δ * den := mul_le_mul_of_nonneg_left hm hδ.le
      _ = ε / 8 := by dsimp [δ]; field_simp [ne_of_gt hden]
  obtain ⟨j, happrox⟩ :=
    exists_boundedDenseVagueTest_approx Q n f hfsupp' (fun x => (hf01 x).1)
      (fun x => (hf01 x).2) δ hδ
  let χ : C_c(Plane, ℝ) := boundedDenseVagueTest Q n j
  have hνerr := cutoff_product_pairing_error Q n ν φ f χ hφ hφsupp' δ
    (fun x => (happrox x).le)
  have hμerr := cutoff_product_pairing_error Q n μ φ f χ hφ hφsupp' δ
    (fun x => (happrox x).le)
  have hφfIntν : Integrable (fun x => φ x * f x) ν :=
    (φ * f).continuous.integrable_of_hasCompactSupport (φ * f).hasCompactSupport
  have hφfLe : (∫ x, φ x * f x ∂ν) ≤ ∫ x, f x ∂ν := by
    apply integral_mono hφfIntν hfint
    intro x
    calc
      φ x * f x ≤ 1 * f x := mul_le_mul_of_nonneg_right (hφ x).2 (hf01 x).1
      _ = f x := one_mul _
  have hfirst : (∫ x, φ x * χ x ∂ν) < ε := by
    have herr := (abs_le.mp hνerr).2
    dsimp [χ] at herr ⊢
    have hbase : (∫ x, f x ∂ν) < ε / 4 := by
      exact lt_of_le_of_lt hfbase hVreal
    linarith
  have hφIntμ : Integrable (fun x => φ x) μ :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hφχIntμ : Integrable (fun x => φ x * χ x) μ := by
    change Integrable (fun x => (φ * χ) x) μ
    exact (φ * χ).continuous.integrable_of_hasCompactSupport (φ * χ).hasCompactSupport
  have hqχ : (fun x => (φ - φ * χ) x) =ᵐ[μ]
      fun x => φ x * (1 - χ x) := by
    filter_upwards [] with x
    simp only [CompactlySupportedContinuousMap.sub_apply,
      CompactlySupportedContinuousMap.mul_apply]
    ring
  have hresχ :
      (∫ x, φ x * (1 - χ x) ∂μ) = (∫ x, φ x ∂μ) - ∫ x, φ x * χ x ∂μ := by
    calc
      _ = ∫ x, (φ - φ * χ) x ∂μ := integral_congr_ae hqχ.symm
      _ = _ := by exact integral_sub hφIntμ hφχIntμ
  have hφfIntμ : Integrable (fun x => φ x * f x) μ :=
    (φ * f).continuous.integrable_of_hasCompactSupport (φ * f).hasCompactSupport
  have hqf : (fun x => (φ - φ * f) x) =ᵐ[μ]
      fun x => φ x * (1 - f x) := by
    filter_upwards [] with x
    simp only [CompactlySupportedContinuousMap.sub_apply,
      CompactlySupportedContinuousMap.mul_apply]
    ring
  have hresf :
      (∫ x, φ x * (1 - f x) ∂μ) = (∫ x, φ x ∂μ) - ∫ x, φ x * f x ∂μ := by
    calc
      _ = ∫ x, (φ - φ * f) x ∂μ := integral_congr_ae hqf.symm
      _ = _ := by exact integral_sub hφIntμ hφfIntμ
  have hsecond : (∫ x, φ x * (1 - χ x) ∂μ) < ε := by
    have herr := (abs_le.mp hμerr).1
    have hbase : (∫ x, φ x * (1 - f x) ∂μ) < ε / 4 :=
      lt_of_le_of_lt hresbase hKreal
    rw [hresf] at hbase
    rw [hresχ]
    linarith
  exact ⟨n, j, hfirst, hsecond⟩

/-- The singular separation witness can be chosen from one fixed sequence of compactly supported
tests. -/
theorem exists_countableBoundedVagueTest_singular_separation (μ ν : Measure Plane)
    [IsFiniteMeasure μ] [IsLocallyFiniteMeasure ν]
    (hSing : Measure.MutuallySingular μ ν) (φ : C_c(Plane, ℝ))
    (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ,
      (∫ x, φ x * countableBoundedVagueTest k x ∂ν) < ε ∧
      (∫ x, φ x * (1 - countableBoundedVagueTest k x) ∂μ) < ε := by
  obtain ⟨n, j, hν, hμ⟩ :=
    exists_boundedDenseVagueTest_singular_separation μ ν hSing φ hφ ε hε
  refine ⟨Nat.pair n j, ?_, ?_⟩
  · simpa [countableBoundedVagueTest, Nat.unpair_pair] using hν
  · simpa [countableBoundedVagueTest, Nat.unpair_pair] using hμ


end Critical2DKPZ.NonGaussian

end
