/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.CriticalLaplace
import Critical2DKPZ.Renewal.ExponentialTilt

/-! # Uniform tails for the critical renewal clock

The positive-step convention in `convolutionPower` ignores the kernel at zero. Exponential
tilting bounds the clock's cumulative convolution powers by powers of a damped step mass.
The Euler-shifted Laplace normalization makes its logarithmic deficit arbitrarily large.
-/

@[expose] public noncomputable section

open Filter Critical2DKPZ.Renewal
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

/-- The tilted mass of the truncated critical gap law is bounded by the full damped series. -/
theorem criticalClock_tilt_cutoff_le (a : {a : ℝ // 0 < a}) {N : ℕ} (hN : 1 ≤ N) (n : ℕ) :
    cutoffMass (exponentialTilt
      (fun r => if r ≤ N then returnWeight r / replicaOverlap N else 0)
      (a / (N + 1))) n ≤ criticalSigmaSq 0 N * dampedReturnSum a N := by
  have hσ : 0 ≤ criticalSigmaSq 0 N := by
    simp only [criticalSigmaSq, zero_div, add_zero]
    exact div_nonneg zero_le_one (replicaOverlap_pos hN).le
  have hnonneg : ∀ r, 0 ≤ weightedStep
      (fun r => criticalSigmaSq 0 N * returnWeight r) (dampingBase a N) r :=
    weightedStep_nonneg (fun r => mul_nonneg hσ (srwKernel_nonneg _ _)) (Real.exp_pos _).le
  have hs := hasSum_weightedStep_critical 0 a N
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 n, weightedStep
        (fun r => criticalSigmaSq 0 N * returnWeight r) (dampingBase a N) r := by
      apply Finset.sum_le_sum
      intro r hr
      have hr0 : r ≠ 0 := by have := (Finset.mem_Icc.mp hr).1; omega
      simp only [exponentialTilt, weightedStep, hr0, ↓reduceIte, dampingBase_pow]
      split_ifs with hrN
      · simp only [criticalSigmaSq, zero_div, add_zero]
        have he : -((a : ℝ) / (N + 1)) * r = -(a : ℝ) * r / (N + 1) := by ring
        rw [he]
        exact le_of_eq (by ring)
      · simp only [mul_zero]
        exact mul_nonneg (mul_nonneg hσ (srwKernel_nonneg _ _)) (Real.exp_pos _).le
    _ ≤ _ := hs.summable.sum_le_tsum _ (fun r _ => hnonneg r) |>.trans_eq hs.tsum_eq

/-- For each fixed positive diffusive horizon and positive rate `M`, the cumulative mass after `k` critical renewal steps is at most `C * exp (-M * k / log N)`. The bound is uniform in `k` for all sufficiently large `N`. -/
theorem criticalClock_tail_le (B M : ℝ) (hB : 0 < B) (hM : 0 < M) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ k : ℕ,
      ∑ n ∈ Finset.range (⌊B * N⌋₊ + 1),
          convolutionPower (fun r => if r ≤ N then returnWeight r / replicaOverlap N else 0) k n ≤
        C * Real.exp (-M * k / Real.log N) := by
  let a : {a : ℝ // 0 < a} :=
    ⟨Real.exp (2 * M + 1 - Real.eulerMascheroniConstant), Real.exp_pos _⟩
  have hlimit : Real.log (a : ℝ) + Real.eulerMascheroniConstant - 0 = 2 * M + 1 := by
    simp only [a, Real.log_exp]
    ring
  have hgap := (tendsto_log_mul_critical_gap 0 a).eventually
    (eventually_gt_nhds (show M < Real.log (a : ℝ) + Real.eulerMascheroniConstant - 0 by
      rw [hlimit]; linarith only [hM]))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hgap
  refine ⟨Real.exp ((a : ℝ) * B), max N₀ 2, fun N hN k => ?_⟩
  have hN2 : 2 ≤ N := (le_max_right N₀ 2).trans hN
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hR : 0 < replicaOverlap N := replicaOverlap_pos (by omega)
  let w : ℕ → ℝ := fun r => if r ≤ N then returnWeight r / replicaOverlap N else 0
  have hw : ∀ r, 0 ≤ w r := by
    intro r
    dsimp [w]
    split_ifs
    · exact div_nonneg (srwKernel_nonneg _ _) hR.le
    · exact le_rfl
  have hmass : cutoffMass (exponentialTilt w (a / (N + 1))) ⌊B * N⌋₊ ≤
      Real.exp (-M / Real.log N) := by
    have hg := hN₀ N ((le_max_left N₀ 2).trans hN)
    have hdeficit : criticalSigmaSq 0 N * dampedReturnSum a N ≤ 1 - M / Real.log N := by
      have hd : M / Real.log N ≤ 1 - criticalSigmaSq 0 N * dampedReturnSum a N :=
        (div_le_iff₀ hlog).2 (by nlinarith only [hg])
      linarith only [hd]
    calc
      _ ≤ criticalSigmaSq 0 N * dampedReturnSum a N :=
        criticalClock_tilt_cutoff_le a (by omega) _
      _ ≤ 1 - M / Real.log N := hdeficit
      _ ≤ _ := by simpa only [sub_eq_add_neg, neg_div, add_comm] using
        Real.add_one_le_exp (-M / Real.log N)
  have hpow : cutoffMass (exponentialTilt w (a / (N + 1))) ⌊B * N⌋₊ ^ k ≤
      Real.exp (-M * k / Real.log N) := by
    have hn : 0 ≤ cutoffMass (exponentialTilt w (a / (N + 1))) ⌊B * N⌋₊ :=
      Finset.sum_nonneg (fun r _ => exponentialTilt_nonneg hw _ r)
    have h := pow_le_pow_left₀ hn hmass k
    rw [← Real.exp_nat_mul] at h
    have he : (k : ℝ) * (-M / Real.log N) = -M * k / Real.log N := by ring
    simpa only [he] using h
  have hfloor : (⌊B * N⌋₊ : ℝ) ≤ B * ((N : ℝ) + 1) :=
    (Nat.floor_le (mul_nonneg hB.le (Nat.cast_nonneg N))).trans (by nlinarith only [hB])
  have htime : (a : ℝ) / (N + 1) * ⌊B * N⌋₊ ≤ (a : ℝ) * B := by
    calc
      _ = (a : ℝ) * ((⌊B * N⌋₊ : ℝ) / (N + 1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left ((div_le_iff₀ (by positivity)).2 hfloor) a.2.le
  change cumulativePower w k ⌊B * N⌋₊ ≤ _
  calc
    _ ≤ Real.exp ((a : ℝ) / (N + 1) * ⌊B * N⌋₊) *
        cutoffMass (exponentialTilt w (a / (N + 1))) ⌊B * N⌋₊ ^ k :=
      cumulativePower_le_exp_mul_pow hw (div_nonneg a.2.le (by positivity)) _ _
    _ ≤ Real.exp ((a : ℝ) * B) * Real.exp (-M * k / Real.log N) :=
      mul_le_mul (Real.exp_le_exp.2 htime) hpow (pow_nonneg
        (Finset.sum_nonneg (fun r _ => exponentialTilt_nonneg hw _ r)) k) (Real.exp_pos _).le

end Critical2DKPZ.SHF.Moments
