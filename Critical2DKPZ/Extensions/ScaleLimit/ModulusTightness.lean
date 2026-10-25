/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.ModulusCompactness
public import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # Tightness from an initial-value bound and a uniform modulus

A summable allocation of error probabilities makes the deterministic modulus
compact sets carry uniformly nearly all the mass.
-/

@[expose] public section
noncomputable section
open MeasureTheory TopologicalSpace
open scoped NNReal ENNReal
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Tightness of real continuous-path laws from tight initial values and a uniform
modulus in probability. The bad-modulus event need not first be proved measurable. -/
theorem isTightMeasureSet_of_modulus {S : ℝ≥0} {ι : Type*}
    (μ : ι → ProbabilityMeasure (ScalePath S))
    (h0 : ∀ ε > (0 : ℝ), ∃ M : ℝ, ∀ i,
      (μ i : Measure (ScalePath S)) {f | M < |f ⟨0, by simp⟩|} ≤ ENNReal.ofReal ε)
    (hmod : ∀ η > (0 : ℝ), ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ i,
      (μ i : Measure (ScalePath S)) {f | ∃ s r : ScaleInterval S,
        dist (s : ℝ) (r : ℝ) ≤ δ ∧ η < |f s - f r|} ≤ ENNReal.ofReal ε) :
    IsTightMeasureSet (Set.range (fun i => (μ i : Measure (ScalePath S)))) := by
  classical
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨b, hb, hsum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
  obtain ⟨M, hM⟩ := h0 (b 0) (hb 0)
  have hm : ∀ n : ℕ, ∃ δ > (0 : ℝ), ∀ i,
      (μ i : Measure (ScalePath S)) {f | ∃ s r : ScaleInterval S,
        dist (s : ℝ) (r : ℝ) ≤ δ ∧ 1 / ((n : ℝ) + 1) < |f s - f r|} ≤ (b (n+1) : ℝ≥0∞) := by
    intro n
    simpa only [ENNReal.ofReal_coe_nnreal] using
      hmod (1 / ((n : ℝ) + 1)) (by positivity) (b (n+1)) (hb (n+1))
  choose δ hδ hbad using hm
  refine ⟨modulusCompactSet S M δ, isCompact_modulusCompactSet S M δ hδ, ?_⟩
  rintro _ ⟨i, rfl⟩
  let B : ℕ → Set (ScalePath S) := fun n =>
    match n with
    | 0 => {f | M < |f ⟨0, by simp⟩|}
    | k+1 => {f | ∃ s r : ScaleInterval S,
        dist (s : ℝ) (r : ℝ) ≤ δ k ∧ 1 / ((k : ℝ) + 1) < |f s - f r|}
  have hsub : (modulusCompactSet S M δ)ᶜ ⊆ ⋃ n, B n := by
    intro f hf
    by_cases hinit : |f ⟨0, by simp⟩| ≤ M
    · have hfail : ∃ (n : ℕ) (s r : ScaleInterval S),
          dist (s : ℝ) (r : ℝ) ≤ δ n ∧ 1 / ((n : ℝ) + 1) < |f s - f r| := by
        have hn : ¬ ∀ n (s r : ScaleInterval S), dist (s : ℝ) (r : ℝ) ≤ δ n →
            |f s - f r| ≤ 1 / ((n : ℝ) + 1) := fun hm => hf ⟨hinit, hm⟩
        push Not at hn
        exact hn
      obtain ⟨n, s, r, hsr, hv⟩ := hfail
      exact Set.mem_iUnion.mpr ⟨n+1, s, r, hsr, hv⟩
    · exact Set.mem_iUnion.mpr ⟨0, lt_of_not_ge hinit⟩
  calc
    (μ i : Measure (ScalePath S)) (modulusCompactSet S M δ)ᶜ ≤
        (μ i : Measure (ScalePath S)) (⋃ n, B n) := measure_mono hsub
    _ ≤ ∑' n, (μ i : Measure (ScalePath S)) (B n) := measure_iUnion_le _
    _ ≤ ∑' n, (b n : ℝ≥0∞) := by
      apply ENNReal.tsum_le_tsum
      intro n
      cases n with
      | zero => simpa only [B, ENNReal.ofReal_coe_nnreal] using hM i
      | succ n => exact hbad n i
    _ ≤ ε := hsum.le

end Critical2DKPZ.Extensions.ScaleLimit
