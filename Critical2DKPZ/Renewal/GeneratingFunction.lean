/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.ExponentialTilt
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Generating functions of nonnegative renewal kernels

Absolute convergence of the Cauchy products and Tonelli's theorem give the exact geometric
resolvent for the full renewal mass. The strictly positive increment convention is retained:
the value of the step kernel at zero is ignored, while the renewal mass has a unit atom there.
-/

@[expose] public noncomputable section

namespace Critical2DKPZ.Renewal

/-- Generating-function coefficients of the positive step kernel, including a zero at time zero. -/
def weightedStep (w : ℕ → ℝ) (ρ : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else w n * ρ ^ n

/-- The `k`-fold convolution coefficients after multiplication by the generating variable. -/
def weightedConvolution (w : ℕ → ℝ) (ρ : ℝ) (k n : ℕ) : ℝ :=
  convolutionPower w k n * ρ ^ n

/-- The zeroth weighted convolution power is the point mass at zero. -/
@[simp] theorem weightedConvolution_zero (w : ℕ → ℝ) (ρ : ℝ) (n : ℕ) :
    weightedConvolution w ρ 0 n = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0 <;> simp only [weightedConvolution, convolutionPower_zero, hn,
    ↓reduceIte, pow_zero, mul_one, zero_mul]

/-- The weighted renewal step is nonnegative. -/
theorem weightedStep_nonneg {w : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r) {ρ : ℝ} (hρ : 0 ≤ ρ) (n : ℕ) :
    0 ≤ weightedStep w ρ n := by
  unfold weightedStep
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (hw n) (pow_nonneg hρ n)

/-- The weighted convolution power is nonnegative. -/
theorem weightedConvolution_nonneg {w : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (k n : ℕ) : 0 ≤ weightedConvolution w ρ k n :=
  mul_nonneg (convolutionPower_nonneg hw k n) (pow_nonneg hρ n)

/-- The convolution recurrence becomes an ordinary Cauchy product after weighting. -/
theorem weightedConvolution_succ (w : ℕ → ℝ) (ρ : ℝ) (k n : ℕ) :
    weightedConvolution w ρ (k + 1) n =
      ∑ r ∈ Finset.range (n + 1), weightedStep w ρ r * weightedConvolution w ρ k (n - r) := by
  rw [Finset.sum_range_eq_add_Ico _ (by omega : 0 < n + 1)]
  simp only [weightedStep, ↓reduceIte, zero_mul, zero_add, Finset.Ico_add_one_right_eq_Icc]
  rw [weightedConvolution, convolutionPower_succ, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  have hr0 : r ≠ 0 := by have := (Finset.mem_Icc.mp hr).1; omega
  rw [ite_eq_right hr0, weightedConvolution]
  have hexp : ρ ^ r * ρ ^ (n - r) = ρ ^ n := by
    rw [← pow_add, Nat.add_sub_of_le (Finset.mem_Icc.mp hr).2]
  calc
    _ = (w r * convolutionPower w k (n - r)) * (ρ ^ r * ρ ^ (n - r)) := by rw [hexp]
    _ = _ := by ring

/-- The zeroth weighted convolution power has generating-function sum one. -/
theorem hasSum_weightedConvolution_zero (w : ℕ → ℝ) (ρ : ℝ) :
    HasSum (weightedConvolution w ρ 0) 1 := by
  have h : HasSum (weightedConvolution w ρ 0)
      (∑ n ∈ ({0} : Finset ℕ), weightedConvolution w ρ 0 n) :=
    hasSum_sum_of_ne_finset_zero (s := ({0} : Finset ℕ))
    (f := weightedConvolution w ρ 0) (fun n hn => by
      simp only [Finset.mem_singleton] at hn
      rw [weightedConvolution_zero, ite_eq_right hn])
  simpa only [Finset.sum_singleton, weightedConvolution_zero, ↓reduceIte] using h

/-- Each convolution power has generating function equal to the corresponding scalar power. -/
theorem hasSum_weightedConvolution {w : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hs : Summable (weightedStep w ρ)) (k : ℕ) :
    HasSum (weightedConvolution w ρ k) ((∑' n, weightedStep w ρ n) ^ k) := by
  have hnstep : Summable (fun n => ‖weightedStep w ρ n‖) :=
    hs.congr fun n => (Real.norm_of_nonneg (weightedStep_nonneg hw hρ n)).symm
  induction k with
  | zero => simpa only [pow_zero] using hasSum_weightedConvolution_zero w ρ
  | succ k ih =>
    have hnconv : Summable (fun n => ‖weightedConvolution w ρ k n‖) :=
      ih.summable.congr fun n => (Real.norm_of_nonneg (weightedConvolution_nonneg hw hρ k n)).symm
    have h := hasSum_sum_range_mul_of_summable_norm hnstep hnconv
    rw [ih.tsum_eq, ← pow_succ'] at h
    exact h.congr_fun (fun n => weightedConvolution_succ w ρ k n)

/-- The full renewal generating function is the exact geometric resolvent. -/
theorem hasSum_weighted_renewalMass {w : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hs : Summable (weightedStep w ρ))
    (hsub : (∑' n, weightedStep w ρ n) < 1) :
    HasSum (fun n => renewalMass w n * ρ ^ n) (1 / (1 - ∑' n, weightedStep w ρ n)) := by
  let S := ∑' n, weightedStep w ρ n
  have hS : 0 ≤ S := tsum_nonneg (weightedStep_nonneg hw hρ)
  have hgeo : HasSum (fun k : ℕ => S ^ k) (1 / (1 - S)) := by
    simpa only [one_div] using hasSum_geometric_of_lt_one hS hsub
  have hrows (k : ℕ) : HasSum (weightedConvolution w ρ k) (S ^ k) :=
    hasSum_weightedConvolution hw hρ hs k
  have hdouble : Summable (fun p : ℕ × ℕ => weightedConvolution w ρ p.1 p.2) := by
    apply (summable_prod_of_nonneg (fun p => weightedConvolution_nonneg hw hρ p.1 p.2)).mpr
    refine ⟨fun k => (hrows k).summable, ?_⟩
    exact hgeo.summable.congr fun k => (hrows k).tsum_eq.symm
  have hcolumn (n : ℕ) : HasSum (fun k => weightedConvolution w ρ k n) (renewalMass w n * ρ ^ n) :=
    (hasSum_convolutionPower w n).mul_right (ρ ^ n)
  have htotal : (∑' n, renewalMass w n * ρ ^ n) = 1 / (1 - S) := by
    calc
      _ = ∑' n, ∑' k, weightedConvolution w ρ k n := tsum_congr fun n => (hcolumn n).tsum_eq.symm
      _ = ∑' k, ∑' n, weightedConvolution w ρ k n :=
        Summable.tsum_comm (f := fun k n => weightedConvolution w ρ k n) hdouble
      _ = ∑' k, S ^ k := tsum_congr fun k => (hrows k).tsum_eq
      _ = _ := hgeo.tsum_eq
  have hsum : Summable (fun n => renewalMass w n * ρ ^ n) :=
    hdouble.prod_symm.prod.congr fun n => (hcolumn n).tsum_eq
  rw [← htotal]
  exact hsum.hasSum

end Critical2DKPZ.Renewal

end
