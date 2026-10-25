/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Critical2DKPZ.Definitions.CriticalBeta
public import Critical2DKPZ.Definitions.CriticalSigmaSq
public import Critical2DKPZ.Definitions.EvenLattice
public import Critical2DKPZ.Definitions.NearestEven
public import Critical2DKPZ.Definitions.Plane
public import Critical2DKPZ.Definitions.ReplicaOverlap
public import Critical2DKPZ.Definitions.Site
public import Critical2DKPZ.Definitions.SrwKernel
public import Critical2DKPZ.Definitions.WalkPosition

/-! The even-lattice representative is nearest, the replica overlap is positive, and the critical disorder strength solves its tuning equation for all sufficiently large scales. -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ

/-- The nearest even-lattice representative belongs to the even lattice. -/
theorem nearestEven_mem_evenLattice (x : Plane) : nearestEven x ∈ evenLattice :=
  ⟨round ((x 0 + x 1) / 2), by simp [nearestEven]⟩

/-- `nearestEven x` is a nearest point of the even lattice to `x`. -/
theorem nearestEven_nearest (x : Plane) (z : Site) (hz : z ∈ evenLattice) :
    (x 0 - nearestEven x 0) ^ 2 + (x 1 - nearestEven x 1) ^ 2 ≤
      (x 0 - z 0) ^ 2 + (x 1 - z 1) ^ 2 := by
  obtain ⟨c, hc⟩ := hz
  have h0 : z 0 = c + (z 0 - c) := by ring
  have h1 : z 1 = c - (z 0 - c) := by omega
  set d : ℤ := z 0 - c
  set u : ℝ := (x 0 + x 1) / 2
  set v : ℝ := (x 0 - x 1) / 2
  have key : ∀ a b : ℝ, (x 0 - (a + b)) ^ 2 + (x 1 - (a - b)) ^ 2
      = 2 * ((u - a) ^ 2 + (v - b) ^ 2) := by intro a b; simp only [u, v]; ring
  have hu : (u - round u) ^ 2 ≤ (u - c) ^ 2 := by
    rw [← sq_abs, ← sq_abs (u - c)]; exact pow_le_pow_left₀ (abs_nonneg _) (round_le u c) 2
  have hv : (v - round v) ^ 2 ≤ (v - d) ^ 2 := by
    rw [← sq_abs, ← sq_abs (v - d)]; exact pow_le_pow_left₀ (abs_nonneg _) (round_le v d) 2
  have lhs : (x 0 - nearestEven x 0) ^ 2 + (x 1 - nearestEven x 1) ^ 2
      = 2 * ((u - round u) ^ 2 + (v - round v) ^ 2) := by
    simp only [nearestEven, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    push_cast; exact key _ _
  have rhs : (x 0 - z 0) ^ 2 + (x 1 - z 1) ^ 2 = 2 * ((u - c) ^ 2 + (v - d) ^ 2) := by
    rw [h0, h1]; push_cast; exact key _ _
  rw [lhs, rhs]; linarith

/-- Every simple random walk transition probability is nonnegative. -/
theorem srwKernel_nonneg (n : ℕ) (z : Site) : 0 ≤ srwKernel n z :=
  Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity

/-- The simple random walk has strictly positive probability of returning to the origin in two steps. -/
theorem srwKernel_two_zero_pos : 0 < srwKernel 2 0 := by
  have hpath : walkPosition 0 ![0, 1] 2 = 0 := by decide
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun s : Fin 2 → Fin 4 =>
    (4 : ℝ)⁻¹ ^ 2 * if walkPosition 0 s 2 = 0 then 1 else 0)
    (fun _ _ => by split_ifs <;> positivity) (Finset.mem_univ ![0, 1]))
  simp [hpath]

/-- The replica overlap is strictly positive for every positive cutoff. -/
theorem replicaOverlap_pos {N : ℕ} (hN : 1 ≤ N) : 0 < replicaOverlap N :=
  lt_of_lt_of_le srwKernel_two_zero_pos
    (Finset.single_le_sum (f := fun n => srwKernel (2 * n) 0)
      (fun _ _ => srwKernel_nonneg _ _) (Finset.mem_Icc.2 ⟨le_rfl, hN⟩))

/-- For all sufficiently large scales, the critical disorder strength satisfies `e^{β_N²} − 1 = σ_N²`. -/
theorem criticalBeta_spec (ϑ : ℝ) : ∀ᶠ N : ℕ in atTop,
    Real.exp (criticalBeta ϑ N ^ 2) - 1 = criticalSigmaSq ϑ N := by
  filter_upwards [eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop |ϑ|]
    with N hN hlog
  simp only [Function.comp] at hlog
  have hL : 0 < Real.log N := lt_of_le_of_lt (abs_nonneg ϑ) hlog
  have hσ : 0 < 1 + ϑ / Real.log N := by
    have : -1 < ϑ / Real.log N := by
      rw [lt_div_iff₀ hL]; linarith [neg_abs_le ϑ]
    linarith
  have hR := replicaOverlap_pos hN
  have hpos : 0 < criticalSigmaSq ϑ N := div_pos hσ hR
  have hlogpos : 0 ≤ Real.log (1 + criticalSigmaSq ϑ N) := (Real.log_pos (by linarith)).le
  unfold criticalBeta
  rw [Real.sq_sqrt hlogpos, Real.exp_log (by linarith)]
  ring

end Critical2DKPZ

end

end
