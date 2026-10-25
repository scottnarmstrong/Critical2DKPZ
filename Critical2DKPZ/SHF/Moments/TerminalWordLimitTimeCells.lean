/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitClocks
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! # Exact integration of the two time clocks

The entrance clock is floor plus one, while the run clock is floor.
In particular the rectangles with run index zero are included.
-/

@[expose] public noncomputable section
open Filter MeasureTheory
open scoped BigOperators CompactlySupported Topology ENNReal
namespace Critical2DKPZ.SHF.Moments

private def wordTimeCell (N a b : ℕ) : Set (ℝ × ℝ) :=
  Set.Ico ((a : ℝ) / N) (((a : ℝ) + 1) / N) ×ˢ
    Set.Ico ((b : ℝ) / N) (((b : ℝ) + 1) / N)

private theorem wordTimeCell_measurable (N a b : ℕ) : MeasurableSet (wordTimeCell N a b) :=
  measurableSet_Ico.prod measurableSet_Ico

private theorem wordTimeInterval_mem {N : ℕ} (hN : 0 < N) (a : ℕ) (t : ℝ) :
    t ∈ Set.Ico ((a : ℝ) / N) (((a : ℝ) + 1) / N) ↔
      0 ≤ t ∧ ⌊(N : ℝ) * t⌋₊ = a := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · intro ht
    have ht0 : 0 ≤ t := (div_nonneg (Nat.cast_nonneg _) hNr.le).trans ht.1
    refine ⟨ht0, (Nat.floor_eq_iff (mul_nonneg hNr.le ht0)).mpr ?_⟩
    exact ⟨by nlinarith [(div_le_iff₀ hNr).mp ht.1],
      by nlinarith [(lt_div_iff₀ hNr).mp ht.2]⟩
  · rintro ⟨ht0, hf⟩
    have hh := (Nat.floor_eq_iff (mul_nonneg hNr.le ht0)).mp hf
    exact ⟨(div_le_iff₀ hNr).mpr (by nlinarith [hh.1]),
      (lt_div_iff₀ hNr).mpr (by nlinarith [hh.2])⟩

private theorem wordTimeCell_mem {N : ℕ} (hN : 0 < N) (a b : ℕ) (q : ℝ × ℝ) :
    q ∈ wordTimeCell N a b ↔
      0 ≤ q.1 ∧ 0 ≤ q.2 ∧ ⌊(N : ℝ) * q.1⌋₊ = a ∧ ⌊(N : ℝ) * q.2⌋₊ = b := by
  simp only [wordTimeCell, Set.mem_prod, wordTimeInterval_mem hN]
  tauto

private theorem wordTimeCell_volume {N : ℕ} (hN : 0 < N) (a b : ℕ) :
    volume (wordTimeCell N a b) = ENNReal.ofReal ((N : ℝ)⁻¹ ^ 2) := by
  have hd (k : ℕ) : ((k : ℝ) + 1) / N - (k : ℝ) / N = (N : ℝ)⁻¹ := by ring
  rw [Measure.volume_eq_prod, wordTimeCell, Measure.prod_prod]
  simp only [Real.volume_Ico, hd, pow_two,
    ENNReal.ofReal_mul (by positivity : 0 ≤ (N : ℝ)⁻¹)]

private theorem wordTimeCell_integral {N : ℕ} (hN : 0 < N) (a b : ℕ) (c : ℝ) :
    Integrable ((wordTimeCell N a b).indicator (fun _ => c)) ∧
      (∫ q : ℝ × ℝ, (wordTimeCell N a b).indicator (fun _ => c) q) = c / (N : ℝ)^2 := by
  have hm := wordTimeCell_measurable N a b
  have hv := wordTimeCell_volume hN a b
  refine ⟨(integrable_indicator_iff hm).mpr (integrableOn_const (by rw [hv]; finiteness)), ?_⟩
  rw [integral_indicator_const _ hm, measureReal_def, hv, ENNReal.toReal_ofReal (by positivity)]
  simp only [smul_eq_mul]
  ring

private theorem wordTimeStep_eq_sum {N : ℕ} (hN : 0 < N) (n : ℕ)
    (F : ℕ → ℕ → ℝ) (q : ℝ × ℝ) :
    (if 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ wordEntranceClock N q.1 + ⌊(N : ℝ) * q.2⌋₊ ≤ n
      then F (wordEntranceClock N q.1) ⌊(N : ℝ) * q.2⌋₊ else 0) =
      ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
        (wordTimeCell N (s - 1) r).indicator (fun _ => F s r) q := by
  classical
  by_cases hq : 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ wordEntranceClock N q.1 + ⌊(N : ℝ) * q.2⌋₊ ≤ n
  · rw [ite_eq_left hq]
    have hs : wordEntranceClock N q.1 ∈ Finset.Icc 1 n := by
      simp only [Finset.mem_Icc, wordEntranceClock] at *
      omega
    have hr : ⌊(N : ℝ) * q.2⌋₊ ∈ Finset.range (n - wordEntranceClock N q.1 + 1) := by
      simp only [Finset.mem_range]
      omega
    rw [Finset.sum_eq_single_of_mem _ hs]
    · rw [Finset.sum_eq_single_of_mem _ hr]
      · rw [Set.indicator_of_mem]
        exact (wordTimeCell_mem hN _ _ q).mpr ⟨hq.1, hq.2.1, by simp [wordEntranceClock], rfl⟩
      · intro r _ hne
        apply Set.indicator_of_notMem
        intro hm
        exact hne ((wordTimeCell_mem hN _ _ q).mp hm).2.2.2.symm
    · intro s hs hne
      apply Finset.sum_eq_zero
      intro r _
      apply Set.indicator_of_notMem
      intro hm
      have hh := ((wordTimeCell_mem hN _ _ q).mp hm).2.2.1
      have hsp := (Finset.mem_Icc.mp hs).1
      apply hne
      simp only [wordEntranceClock]
      omega
  · rw [ite_eq_right hq]
    symm
    apply Finset.sum_eq_zero
    intro s hs
    apply Finset.sum_eq_zero
    intro r hr
    apply Set.indicator_of_notMem
    intro hm
    obtain ⟨hq1, hq2, hfs, hfr⟩ := (wordTimeCell_mem hN _ _ q).mp hm
    apply hq
    refine ⟨hq1, hq2, ?_⟩
    have hs' := Finset.mem_Icc.mp hs
    have hr' := Finset.mem_range.mp hr
    simp only [wordEntranceClock, hfs, hfr]
    omega

/-- Integrability and exact cell volume for the two-time staircase. -/
theorem integrable_integral_wordTimeStep {N : ℕ} (hN : 0 < N) (n : ℕ)
    (F : ℕ → ℕ → ℝ) :
    Integrable (fun q : ℝ × ℝ =>
      if 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ wordEntranceClock N q.1 + ⌊(N : ℝ) * q.2⌋₊ ≤ n
      then F (wordEntranceClock N q.1) ⌊(N : ℝ) * q.2⌋₊ else 0) ∧
    (∫ q : ℝ × ℝ,
      if 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ wordEntranceClock N q.1 + ⌊(N : ℝ) * q.2⌋₊ ≤ n
      then F (wordEntranceClock N q.1) ⌊(N : ℝ) * q.2⌋₊ else 0) =
      (∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1), F s r) / (N : ℝ)^2 := by
  classical
  simp_rw [wordTimeStep_eq_sum hN]
  have hi (s r : ℕ) := (wordTimeCell_integral hN (s - 1) r (F s r)).1
  refine ⟨integrable_finsetSum _ (fun s _ => integrable_finsetSum _ (fun r _ => hi s r)), ?_⟩
  rw [integral_finsetSum _ (fun s _ => integrable_finsetSum _ (fun r _ => hi s r))]
  simp_rw [integral_finsetSum _ (fun r _ => hi _ r)]
  simp_rw [(wordTimeCell_integral hN _ _ _).2, Finset.sum_div]

end Critical2DKPZ.SHF.Moments
