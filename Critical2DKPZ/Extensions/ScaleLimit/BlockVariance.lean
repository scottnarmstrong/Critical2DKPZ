/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.TruncatedLogs
public import Critical2DKPZ.Extensions.ScaleLimit.BlockMoments
import Critical2DKPZ.Extensions.ScaleLimit.HarmonicBounds
import Mathlib.Tactic

/-! # Harmonic variance bound for the independent logarithmic block sum -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A positive-index truncated logarithm has every finite moment. -/
theorem memLp_logTrunc_of_pos (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) {j : ℕ} (hj : 0 < j) (p : ℝ≥0∞) : MemLp (logTrunc Z ρ j) p P := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  exact memLp_logTrunc ϑ P Z hZ hρ k p

/-- Every finite logarithmic partial sum has every finite moment. -/
theorem memLp_partialSum (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ) (p : ℝ≥0∞) : MemLp (partialSum Z ρ n) p P := by
  change MemLp (fun ω => ∑ j ∈ Finset.Icc 1 n, logTrunc Z ρ j ω) p P
  apply memLp_finsetSum
  intro j hj
  exact memLp_logTrunc_of_pos ϑ P Z hZ hρ (by have := (Finset.mem_Icc.mp hj).1; omega) p

/-- Independence gives the exact finite-sum variance identity without using the
unconstrained block at index zero. -/
theorem variance_partialSum_eq_sum (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ) :
    variance (partialSum Z ρ n) P = ∑ j ∈ Finset.Icc 1 n, variance (logTrunc Z ρ j) P := by
  have hmem (j : ℕ) (hj : j ∈ Finset.Icc 1 n) : MemLp (logTrunc Z ρ j) 2 P :=
    memLp_logTrunc_of_pos ϑ P Z hZ hρ (by have := (Finset.mem_Icc.mp hj).1; omega) 2
  have hpair (i : ℕ) (hi : i ∈ Finset.Icc 1 n) (j : ℕ) (hj : j ∈ Finset.Icc 1 n)
      (hij : i ≠ j) : IndepFun (logTrunc Z ρ i) (logTrunc Z ρ j) P := by
    have hi1 := (Finset.mem_Icc.mp hi).1
    have hj1 := (Finset.mem_Icc.mp hj).1
    have h := (iIndepFun_logTrunc ϑ P Z hZ hρ).indepFun (i := i - 1) (j := j - 1) (by omega)
    simpa only [Nat.sub_add_cancel hi1, Nat.sub_add_cancel hj1] using h
  have hv := IndepFun.variance_sum hmem hpair
  have heq : (∑ j ∈ Finset.Icc 1 n, logTrunc Z ρ j) = partialSum Z ρ n := by
    funext ω
    exact Finset.sum_apply ω _ _
  rw [heq] at hv
  exact hv

/-- The variance of the partial sum is bounded by a constant times the harmonic
clock, including all initial indices. -/
theorem variance_partialSum_le (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, variance (partialSum Z ρ n) P ≤ C * (1 + Real.log n) := by
  obtain ⟨C, hC0, hC⟩ := block_moments ϑ P Z hZ hρ
  refine ⟨4 * C, by positivity, ?_⟩
  intro n
  have hsingle (j : ℕ) (hj : j ∈ Finset.Icc 1 n) :
      variance (logTrunc Z ρ j) P ≤ (4 * C) * (j : ℝ)⁻¹ := by
    have hjpos : 0 < j := by have := (Finset.mem_Icc.mp hj).1; omega
    have hmem := memLp_logTrunc_of_pos ϑ P Z hZ hρ hjpos 2
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hjpos.ne'
    obtain ⟨hi2, _hi4, hb2, _hb4⟩ := hC k
    have hsq : Integrable (fun ω => logTrunc Z ρ (k + 1) ω ^ 2) P :=
      (memLp_two_iff_integrable_sq hmem.aestronglyMeasurable).mp hmem
    have hle : (∫ ω, logTrunc Z ρ (k + 1) ω ^ 2 ∂P) ≤
        4 * ∫ ω, (blockMass Z ρ (k + 1) ω - 1) ^ 2 ∂P := by
      rw [← integral_const_mul]
      apply integral_mono_ae hsq (hi2.const_mul 4)
      exact Filter.Eventually.of_forall fun ω => truncatedLog_sq_le _
    calc
      _ ≤ ∫ ω, logTrunc Z ρ (k + 1) ω ^ 2 ∂P :=
        variance_le_expectation_sq hmem.aestronglyMeasurable
      _ ≤ 4 * (C / (k + 1 : ℕ)) := hle.trans (mul_le_mul_of_nonneg_left hb2 (by norm_num))
      _ = _ := by push_cast; ring
  rw [variance_partialSum_eq_sum ϑ P Z hZ hρ]
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 n, (4 * C) * (j : ℝ)⁻¹ := Finset.sum_le_sum hsingle
    _ = (4 * C) * ∑ j ∈ Finset.Icc 1 n, (j : ℝ)⁻¹ := (Finset.mul_sum _ _ _).symm
    _ ≤ (4 * C) * (1 + Real.log n) :=
      mul_le_mul_of_nonneg_left (sum_Icc_inv_le_one_add_log n) (by positivity)

end Critical2DKPZ.Extensions.ScaleLimit
