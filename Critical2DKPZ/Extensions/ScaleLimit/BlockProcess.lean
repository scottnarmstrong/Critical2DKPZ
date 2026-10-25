/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.PartialSumCovariance
public import Critical2DKPZ.Extensions.ScaleLimit.CenteredArrayCLT
import Critical2DKPZ.Extensions.ScaleLimit.CentringLemma
import Mathlib.Tactic

/-! # Centered block summands and the normalized partial-sum process -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Centered positive-index block logarithms, reindexed from zero. -/
def centeredLogBlock {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (ρ : ℝ) (j : ℕ) (ω : Ω) : ℝ :=
  logTrunc Z ρ (j + 1) ω - ∫ ω', logTrunc Z ρ (j + 1) ω' ∂P

/-- The centered logarithmic partial-sum process at the geometric scale clock. -/
def normalizedPartialSum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (ρ L s : ℝ) (ω : Ω) : ℝ :=
  (partialSum Z ρ (nL ρ L s) ω - ∫ ω', partialSum Z ρ (nL ρ L s) ω' ∂P) / Real.sqrt L

/-- Centering preserves independence of the positive-index blocks. -/
theorem iIndepFun_centeredLogBlock (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) : iIndepFun (centeredLogBlock P Z ρ) P :=
  (iIndepFun_logTrunc ϑ P Z hZ hρ).comp
    (fun j z => z - ∫ ω, logTrunc Z ρ (j + 1) ω ∂P) (fun _ => by fun_prop)

/-- Centered block summands have every finite moment. -/
theorem memLp_centeredLogBlock (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) (j : ℕ) (p : ℝ≥0∞) : MemLp (centeredLogBlock P Z ρ j) p P :=
  (memLp_logTrunc ϑ P Z hZ hρ j p).sub (memLp_const _)

/-- The summands are centered at every index. -/
theorem integral_centeredLogBlock (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) (j : ℕ) : (∫ ω, centeredLogBlock P Z ρ j ω ∂P) = 0 := by
  simp only [centeredLogBlock, integral_sub ((memLp_logTrunc ϑ P Z hZ hρ j 1).integrable le_rfl)
    (integrable_const _), integral_const, probReal_univ, one_smul, sub_self]

/-- The centered summands are bounded pointwise by twice the logarithmic cutoff. -/
theorem abs_centeredLogBlock_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (ρ : ℝ)
    (j : ℕ) (ω : Ω) : |centeredLogBlock P Z ρ j ω| ≤ 2 * Real.log 2 := by
  have hmean := norm_integral_le_of_norm_le_const (μ := P) (f := logTrunc Z ρ (j + 1))
    (C := Real.log 2) (Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using abs_logTrunc_le Z ρ (j + 1) ω)
  have hmean' : |∫ ω', logTrunc Z ρ (j + 1) ω' ∂P| ≤ Real.log 2 := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hmean
  exact (abs_sub _ _).trans (by linarith [abs_logTrunc_le Z ρ (j + 1) ω])

/-- Summing the centered blocks gives the centered partial sum. -/
theorem partialSumRange_centeredLogBlock (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ) (ω : Ω) :
    partialSumRange (centeredLogBlock P Z ρ) n ω =
      partialSum Z ρ n ω - ∫ ω', partialSum Z ρ n ω' ∂P := by
  have hsum (ω : Ω) : (∑ j ∈ Finset.range n, logTrunc Z ρ (j + 1) ω) = partialSum Z ρ n ω :=
    sum_range_add_one_eq_sum_Icc (fun j => logTrunc Z ρ j ω) n
  have hmean : (∑ j ∈ Finset.range n, ∫ ω', logTrunc Z ρ (j + 1) ω' ∂P) =
      ∫ ω', partialSum Z ρ n ω' ∂P := by
    rw [← integral_finsetSum _ (fun j _ => (memLp_logTrunc ϑ P Z hZ hρ j 1).integrable le_rfl)]
    simp only [hsum]
  simp only [partialSumRange, centeredLogBlock, Finset.sum_sub_distrib, hsum, hmean]

/-- The normalized partial sum is square integrable at all real scales. -/
theorem memLp_normalizedPartialSum (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) (L s : ℝ) : MemLp (normalizedPartialSum P Z ρ L s) 2 P := by
  have h : MemLp (fun ω => (Real.sqrt L)⁻¹ *
      (partialSum Z ρ (nL ρ L s) ω - ∫ ω', partialSum Z ρ (nL ρ L s) ω' ∂P)) 2 P :=
    ((memLp_partialSum ϑ P Z hZ hρ (nL ρ L s) 2).sub (memLp_const _)).const_mul _
  change MemLp (fun ω => (partialSum Z ρ (nL ρ L s) ω -
    ∫ ω', partialSum Z ρ (nL ρ L s) ω' ∂P) / Real.sqrt L) 2 P
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- Centering removes no covariance, and the square-root factors multiply to `L`. -/
theorem covariance_normalizedPartialSum (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) (L : Set.Ioi (0 : ℝ)) (s s' : ℝ) :
    covariance (normalizedPartialSum P Z ρ L s) (normalizedPartialSum P Z ρ L s') P =
      (L : ℝ)⁻¹ * covariance (partialSum Z ρ (nL ρ L s)) (partialSum Z ρ (nL ρ L s')) P := by
  change covariance (fun ω => (_ - _) / Real.sqrt (L : ℝ)) (fun ω => (_ - _) / Real.sqrt (L : ℝ)) P = _
  rw [covariance_fun_div_left, covariance_fun_div_right,
    covariance_sub_const_left ((memLp_partialSum ϑ P Z hZ hρ (nL ρ L s) 2).integrable one_le_two),
    covariance_sub_const_right ((memLp_partialSum ϑ P Z hZ hρ (nL ρ L s') 2).integrable one_le_two),
    div_div, ← pow_two, Real.sq_sqrt L.property.le]
  ring

end Critical2DKPZ.Extensions.ScaleLimit
