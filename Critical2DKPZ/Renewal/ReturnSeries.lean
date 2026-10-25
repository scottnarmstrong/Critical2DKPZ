/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.CriticalWindow
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.NumberTheory.Harmonic.Defs
import Critical2DKPZ.RandomWalk.ReplicaOverlap
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Damped return series and the summable local-CLT error

The difference `q_{2r}(0) - 1/(πr)` is absolutely summable. Its Abel-damped sum and its
ordinary partial sums therefore have the same limit. The remaining harmonic contribution
is exactly a logarithm. This is the normalization calculation behind the Euler-constant
shift in the critical-window renewal limit.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.Renewal

/-- The summable error after removing the period-2 leading return probability. -/
def returnError (n : ℕ) : ℝ :=
  returnWeight (n + 1) - (1 / Real.pi) * ((n + 1 : ℕ) : ℝ)⁻¹

/-- The norms of the return-kernel error terms are summable. -/
theorem summable_norm_returnError : Summable (fun n => ‖returnError n‖) := by
  obtain ⟨K, _, hK⟩ := srwKernel_two_mul_zero_localCLT
  have hs : Summable (fun n : ℕ => K / (n : ℝ) ^ 2) := by
    simpa only [div_eq_mul_inv, one_mul] using
      (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).mul_left K
  have hs' : Summable (fun n : ℕ => K / ((n + 1 : ℕ) : ℝ) ^ 2) :=
    hs.comp_injective Nat.succ_injective
  apply hs'.of_nonneg_of_le (fun n => norm_nonneg (returnError n))
  intro n
  exact hK (n + 1) (by omega)

/-- The return-kernel error series is summable. -/
theorem summable_returnError : Summable returnError := summable_norm_returnError.of_norm

/-- Exponential damping on the rescaled positive time axis. -/
def dampingFactor (a : ℝ) (N n : ℕ) : ℝ :=
  Real.exp (-a * (n + 1) / (N + 1))

/-- The damping factor is strictly positive. -/
theorem dampingFactor_pos (a : ℝ) (N n : ℕ) : 0 < dampingFactor a N n := Real.exp_pos _

/-- The damping factor is at most one. -/
theorem dampingFactor_le_one {a : ℝ} (ha : 0 ≤ a) (N n : ℕ) : dampingFactor a N n ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (by positivity)) (by positivity)

/-- The damping factor tends to one as the lattice scale grows. -/
theorem tendsto_dampingFactor (a : ℝ) (n : ℕ) :
    Tendsto (fun N => dampingFactor a N n) atTop (nhds 1) := by
  have htop : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using!
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp htop
  have hx : Tendsto (fun N : ℕ => -a * ((n : ℝ) + 1) / ((N : ℝ) + 1)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds (x := -a * ((n : ℝ) + 1))).mul hinv
  exact (Real.tendsto_exp_nhds_zero_nhds_one.comp hx)

/-- The damped return-kernel error series is summable. -/
theorem summable_damped_returnError {a : ℝ} (ha : 0 ≤ a) (N : ℕ) :
    Summable (fun n => returnError n * dampingFactor a N n) := by
  apply Summable.of_norm_bounded summable_norm_returnError
  intro n
  simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (dampingFactor_pos a N n)]
  exact mul_le_of_le_one_right (abs_nonneg _) (dampingFactor_le_one ha N n)

/-- Abel damping preserves the total summable return error. -/
theorem tendsto_tsum_damped_returnError {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun N => ∑' n, returnError n * dampingFactor a N n) atTop (nhds (∑' n, returnError n)) := by
  apply tendsto_tsum_of_dominated_convergence summable_norm_returnError
  · intro n
    simpa only [mul_one] using (tendsto_const_nhds (x := returnError n)).mul (tendsto_dampingFactor a n)
  · apply Filter.Eventually.of_forall
    intro N n
    simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (dampingFactor_pos a N n)]
    exact mul_le_of_le_one_right (abs_nonneg _) (dampingFactor_le_one ha N n)

/-- Summing from one to a finite horizon equals the shifted range sum. -/
theorem sum_Icc_one_eq_sum_range (f : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, f n = ∑ n ∈ Finset.range N, f (n + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  exact Finset.sum_congr rfl fun n _ => congrArg f (Nat.add_comm 1 n)

/-- Exact decomposition of the overlap into its harmonic main term and return error. -/
theorem replicaOverlap_eq_harmonic_add_error (N : ℕ) :
    replicaOverlap N = (1 / Real.pi) * (harmonic N : ℝ) +
      ∑ n ∈ Finset.range N, returnError n := by
  rw [replicaOverlap, sum_Icc_one_eq_sum_range, harmonic]
  simp only [returnError, returnWeight, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
    Finset.mul_sum, Finset.sum_sub_distrib]
  ring

/-- The damped harmonic series is the exact logarithm from the geometric power series. -/
theorem hasSum_damped_harmonic (a : ℝ) (ha : 0 < a) (N : ℕ) :
    HasSum (fun n => dampingFactor a N n / ((n + 1 : ℕ) : ℝ))
      (-Real.log (1 - Real.exp (-a / (N + 1)))) := by
  have hx : |Real.exp (-a / (N + 1))| < 1 := by
    rw [abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos ha) (by positivity)
  have he (n : ℕ) : dampingFactor a N n = Real.exp (-a / (N + 1)) ^ (n + 1) := by
    rw [dampingFactor, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  simpa only [he, Nat.cast_add, Nat.cast_one] using Real.hasSum_pow_div_log_of_abs_lt_one hx

/-- The exponentially damped return series, with a strictly positive damping parameter. -/
def dampedReturnSum (a : {a : ℝ // 0 < a}) (N : ℕ) : ℝ :=
  ∑' n, returnWeight (n + 1) * dampingFactor a N n

/-- The damped return series is the logarithmic harmonic part plus the damped summable error. -/
theorem hasSum_damped_return (a : {a : ℝ // 0 < a}) (N : ℕ) :
    HasSum (fun n => returnWeight (n + 1) * dampingFactor a N n)
      ((1 / Real.pi) * (-Real.log (1 - Real.exp (-a / (N + 1)))) +
        ∑' n, returnError n * dampingFactor a N n) := by
  have h := ((hasSum_damped_harmonic a a.2 N).mul_left (1 / Real.pi)).add
    (summable_damped_returnError a.2.le N).hasSum
  convert h using 1
  funext n
  simp only [returnError, div_eq_mul_inv]
  push_cast
  ring

/-- The damped return sum splits into its logarithmic main term and error series. -/
theorem dampedReturnSum_eq (a : {a : ℝ // 0 < a}) (N : ℕ) :
    dampedReturnSum a N = (1 / Real.pi) * (-Real.log (1 - Real.exp (-a / (N + 1)))) +
      ∑' n, returnError n * dampingFactor a N n := (hasSum_damped_return a N).tsum_eq

end Critical2DKPZ.Renewal

end
