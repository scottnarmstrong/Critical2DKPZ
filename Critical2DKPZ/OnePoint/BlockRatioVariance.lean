/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.BlockRatioExpansion
import Critical2DKPZ.MomentBounds.BlockVarianceReduction
import Critical2DKPZ.MomentBounds.BlockClockBounds
import Mathlib.Tactic

/-! # Uniform block-mass variance bound -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

namespace Critical2DKPZ.OnePoint

open Critical2DKPZ.Blocks

/-- The variance of an interior block mass is bounded by the inverse distance to the terminal block, uniformly over geometric ratios above `ρ₀`. -/
theorem variance_blockMass_le_uniform (A ρ₀ : ℝ) (hρ₀ : 1 < ρ₀) :
    ∃ C : ℝ, ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
      ∀ i : ℕ, 1 ≤ i → i + 1 ≤ Critical2DKPZ.blockCount N ρ →
        Var[fun ω => blockMass (Critical2DKPZ.criticalBeta ϑ N)
          (Critical2DKPZ.blockTime N ρ) i ω; disorderLaw] ≤
          C / ((Critical2DKPZ.blockCount N ρ : ℝ) - i) := by
  obtain ⟨Cvar, hCvar, hNvar⟩ :=
    Critical2DKPZ.MomentBounds.smoothedP2Plane_variance_le_uniform A 1
  obtain ⟨Cperiod, hperiod⟩ := replicaOverlap_sub_log_bounded
  have hρ₀pos : 0 < ρ₀ := by linarith
  have hlogρ₀ : 0 < Real.log ρ₀ := Real.log_pos hρ₀
  let q := Real.log 3 + |Cperiod|
  let B := 1 + q / Real.log ρ₀
  let C := 3 * Cvar * B / Real.pi
  have hq : 0 ≤ q := by
    dsimp [q]
    exact add_nonneg (Real.log_nonneg (by norm_num)) (abs_nonneg Cperiod)
  have hB : 0 < B := by
    dsimp [B]
    positivity
  refine ⟨C, ?_⟩
  intro ρ hρ₀ρ
  have hρ : 1 < ρ := lt_of_lt_of_le hρ₀ hρ₀ρ
  have hρpos : 0 < ρ := by linarith
  have hlogρ₀ρ : Real.log ρ₀ ≤ Real.log ρ :=
    Real.log_le_log hρ₀pos hρ₀ρ
  filter_upwards [hNvar,
    Filter.eventually_ge_atTop (⌈2 * ρ₀ / (ρ₀ - 1)⌉₊)] with N hNvar hN
  intro ϑ hϑ i hi hiK
  have hclock : Monotone (Critical2DKPZ.blockTime N ρ) :=
    Critical2DKPZ.MomentBounds.blockTime_monotone_of_large_horizon hρ₀ hρ₀ρ hN
  have hK : 2 ≤ Critical2DKPZ.blockCount N ρ := by omega
  have hiK' : i < Critical2DKPZ.blockCount N ρ := by omega
  have hfinal : Critical2DKPZ.blockTime N ρ
      (Critical2DKPZ.blockCount N ρ) = N := by
    simp [Critical2DKPZ.blockTime, Nat.ne_of_gt (by omega : 0 < Critical2DKPZ.blockCount N ρ)]
  have htimeN : Critical2DKPZ.blockTime N ρ i ≤ N := by
    calc
      Critical2DKPZ.blockTime N ρ i ≤
          Critical2DKPZ.blockTime N ρ (Critical2DKPZ.blockCount N ρ) :=
        hclock (Nat.le_of_lt hiK')
      _ = N := hfinal
  have hscale := Critical2DKPZ.MomentBounds.blockTime_lower_geometric_scale hρ hi hiK'
  have hiReal : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hpow : 1 ≤ ρ ^ ((i : ℝ) - 1) :=
    Real.one_le_rpow hρ.le (by linarith)
  have hn : 1 ≤ Critical2DKPZ.blockTime N ρ i := by
    have hreal : (1 : ℝ) ≤ (Critical2DKPZ.blockTime N ρ i : ℝ) := hpow.trans hscale
    exact_mod_cast hreal
  let s := Critical2DKPZ.blockTime N ρ (i - 1)
  let n := Critical2DKPZ.blockTime N ρ i
  have hsn : s ≤ n := by
    dsimp [s, n]
    exact hclock (Nat.sub_le i 1)
  have hratio :
      (((max n 1 : ℕ) : ℝ) / ((max s 1 : ℕ) : ℝ)) ≤ ρ + 2 := by
    by_cases hi1 : i = 1
    · subst i
      have hρN := Critical2DKPZ.MomentBounds.ratio_le_horizon_of_blockCount_ge_two hρ hK
      simpa [s, n] using
        Critical2DKPZ.MomentBounds.blockTime_first_endpoint_ratio_le hρ hρN
    · have hi2 : 2 ≤ i := by omega
      simpa [s, n] using
        Critical2DKPZ.MomentBounds.blockTime_endpoint_ratio_le hρ hi2 hiK'
  have hoverlap :=
    Critical2DKPZ.MomentBounds.replicaOverlap_sub_le_of_ratio_bound
      Cperiod hperiod hsn hratio
  let d := Critical2DKPZ.blockCount N ρ - i
  have hdpos : 0 < d := by dsimp [d]; omega
  have hdRealPos : 0 < (d : ℝ) := by exact_mod_cast hdpos
  have hlogρ : 0 < Real.log ρ := Real.log_pos hρ
  have hdenlower :=
    Critical2DKPZ.MomentBounds.blockTime_log_horizon_lower hρ le_rfl hi hiK'
  have hdenpos : 0 < Real.log (1 + (N : ℝ) / n) := by
    have hlowpos : 0 < (d : ℝ) * Real.log ρ / 3 := by positivity
    exact lt_of_lt_of_le hlowpos (by simpa [d, n] using hdenlower)
  have hratioLog : (Real.log (ρ + 2) + Cperiod) / Real.log ρ ≤ B := by
    have hthree : ρ + 2 ≤ 3 * ρ := by nlinarith
    have hlogScale : Real.log (ρ + 2) ≤ Real.log 3 + Real.log ρ := by
      calc
        Real.log (ρ + 2) ≤ Real.log (3 * ρ) :=
          Real.log_le_log (by linarith) hthree
        _ = Real.log 3 + Real.log ρ := by
          rw [Real.log_mul (by norm_num) hρpos.ne']
    have hnum : Real.log (ρ + 2) + Cperiod ≤ Real.log ρ + q := by
      dsimp [q]
      linarith [hlogScale, le_abs_self Cperiod]
    have hqdiv : q / Real.log ρ ≤ q / Real.log ρ₀ :=
      div_le_div_of_nonneg_left hq hlogρ₀ hlogρ₀ρ
    calc
      (Real.log (ρ + 2) + Cperiod) / Real.log ρ ≤
          (Real.log ρ + q) / Real.log ρ :=
        div_le_div_of_nonneg_right hnum hlogρ.le
      _ = 1 + q / Real.log ρ := by
        field_simp [ne_of_gt hlogρ]
      _ ≤ B := by
        dsimp [B]
        linarith
  have hnumBound : Real.log (ρ + 2) + Cperiod ≤ Real.log ρ * B := by
    simpa [mul_comm] using (div_le_iff₀ hlogρ).mp hratioLog
  have hbase := hNvar ϑ hϑ s n hsn hn (by
    have htimeNReal : (n : ℝ) ≤ (N : ℝ) := by
      dsimp [n]
      exact_mod_cast htimeN
    simpa [n] using htimeNReal)
  have hbaseOverlap : Cvar * (replicaOverlap n - replicaOverlap s) /
      Real.log (1 + (N : ℝ) / n) ≤
      Cvar * ((Real.log (ρ + 2) + Cperiod) / Real.pi) /
        Real.log (1 + (N : ℝ) / n) := by
    apply div_le_div_of_nonneg_right _ hdenpos.le
    exact mul_le_mul_of_nonneg_left hoverlap hCvar
  have hbaseNum : Cvar * ((Real.log (ρ + 2) + Cperiod) / Real.pi) ≤
      Cvar * ((Real.log ρ * B) / Real.pi) := by
    apply mul_le_mul_of_nonneg_left _ hCvar
    exact div_le_div_of_nonneg_right hnumBound Real.pi_pos.le
  have hmain :=
    div_le_div_of_nonneg_left
      (show 0 ≤ Cvar * ((Real.log ρ * B) / Real.pi) by positivity)
      (by positivity : 0 < (d : ℝ) * Real.log ρ / 3)
      (by simpa [d, n] using hdenlower)
  have hdcast : (d : ℝ) = (Critical2DKPZ.blockCount N ρ : ℝ) - i := by
    dsimp [d]
    rw [Nat.cast_sub (Nat.le_of_lt hiK')]
  have halgebra :
      (Cvar * ((Real.log ρ * B) / Real.pi)) / ((d : ℝ) * Real.log ρ / 3) = C / d := by
    dsimp [C]
    field_simp [ne_of_gt hdRealPos, ne_of_gt hlogρ, Real.pi_ne_zero]
  calc
    Var[fun ω => blockMass (Critical2DKPZ.criticalBeta ϑ N)
        (Critical2DKPZ.blockTime N ρ) i ω; disorderLaw] ≤
        Cvar * (replicaOverlap n - replicaOverlap s) /
          Real.log (1 + (N : ℝ) / n) := by
      simpa [blockMass, s, n] using hbase
    _ ≤ Cvar * ((Real.log (ρ + 2) + Cperiod) / Real.pi) /
          Real.log (1 + (N : ℝ) / n) := hbaseOverlap
    _ ≤ (Cvar * ((Real.log ρ * B) / Real.pi)) /
          Real.log (1 + (N : ℝ) / n) :=
      div_le_div_of_nonneg_right hbaseNum hdenpos.le
    _ ≤ (Cvar * ((Real.log ρ * B) / Real.pi)) /
          ((d : ℝ) * Real.log ρ / 3) := hmain
    _ = C / d := halgebra
    _ = C / ((Critical2DKPZ.blockCount N ρ : ℝ) - i) := by rw [hdcast]

end Critical2DKPZ.OnePoint

end
