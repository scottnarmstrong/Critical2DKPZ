/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.SecondMoment
public import Critical2DKPZ.Definitions.BlockCount
public import Critical2DKPZ.Definitions.BlockTime
import Critical2DKPZ.MomentBounds.BlockClockBounds
import Critical2DKPZ.PolymerCalculus.Clocks
import Mathlib.Tactic

/-! # Variance form of the uniform one-point block estimate -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter

namespace Critical2DKPZ.MomentBounds

/-- The uniform smoothed second-moment estimate implies a uniform variance
bound with the same overlap increment and logarithmic denominator. -/
theorem smoothedP2Plane_variance_le_uniform (A T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
      ∀ s n : ℕ, s ≤ n → 1 ≤ n → (n : ℝ) ≤ T * N →
        ProbabilityTheory.variance
          (fun ω : Disorder => Critical2DKPZ.smoothedP2Plane
            (Critical2DKPZ.criticalBeta ϑ N) s n 0 ω) disorderLaw ≤
          C * (Critical2DKPZ.replicaOverlap n - Critical2DKPZ.replicaOverlap s) /
            Real.log (1 + (N : ℝ) / n) := by
  obtain ⟨C₀, hN⟩ := Critical2DKPZ.OnePoint.smoothedP2Plane_secondMoment_le_uniform A T
  refine ⟨|C₀|, abs_nonneg C₀, ?_⟩
  filter_upwards [hN, Filter.eventually_ge_atTop 2] with N hN hN2
  intro ϑ hϑ s n hsn hn hnT
  let β := Critical2DKPZ.criticalBeta ϑ N
  let Z := fun ω : Disorder => Critical2DKPZ.smoothedP2Plane β s n 0 ω
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hden : 0 < Real.log (1 + (N : ℝ) / n) := by
    apply Real.log_pos
    have hratio : 0 < (N : ℝ) / n := div_pos hNpos hnpos
    linarith
  have hgap : 0 ≤ Critical2DKPZ.replicaOverlap n -
      Critical2DKPZ.replicaOverlap s := by
    unfold Critical2DKPZ.replicaOverlap
    change 0 ≤
      (∑ r ∈ Finset.Icc 1 n, Critical2DKPZ.srwKernel (2 * r) 0) -
        ∑ r ∈ Finset.Icc 1 s, Critical2DKPZ.srwKernel (2 * r) 0
    apply sub_nonneg.mpr
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc_right hsn)
      (fun r _ _ => Critical2DKPZ.srwKernel_nonneg (2 * r) 0)
  have hsecond := hN ϑ hϑ s n hsn hn hnT
  have hmem : MemLp Z 2 disorderLaw :=
    Critical2DKPZ.Polymer.memLp_smoothedP2Plane β s n 0 2 (by norm_num)
  have hmean : (∫ ω, Z ω ∂disorderLaw) = 1 := by
    dsimp [Z]
    exact Critical2DKPZ.Polymer.integral_smoothedP2Plane β s n 0
  have hvariance : ProbabilityTheory.variance Z disorderLaw =
      (∫ ω, Z ω ^ 2 ∂disorderLaw) - 1 := by
    rw [ProbabilityTheory.variance_eq_sub hmem, hmean]
    norm_num
  have hbase : ProbabilityTheory.variance Z disorderLaw ≤
      C₀ * (Critical2DKPZ.replicaOverlap n - Critical2DKPZ.replicaOverlap s) /
        Real.log (1 + (N : ℝ) / n) := by
    rw [hvariance]
    linarith
  calc
    ProbabilityTheory.variance Z disorderLaw ≤
        C₀ * (Critical2DKPZ.replicaOverlap n - Critical2DKPZ.replicaOverlap s) /
          Real.log (1 + (N : ℝ) / n) := hbase
    _ ≤ |C₀| * (Critical2DKPZ.replicaOverlap n - Critical2DKPZ.replicaOverlap s) /
          Real.log (1 + (N : ℝ) / n) := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact mul_le_mul_of_nonneg_right (le_abs_self C₀) hgap
    _ = _ := by ring

/-- A bounded endpoint-scale ratio bounds the overlap increment up to the period-two error in `OnePoint.replicaOverlap_sub_log_bounded`. -/
theorem replicaOverlap_sub_le_of_ratio_bound (C₀ : ℝ)
    (hC₀ : ∀ s n : ℕ, s ≤ n →
      |Real.pi * (Critical2DKPZ.replicaOverlap n - Critical2DKPZ.replicaOverlap s) -
        Real.log (((max n 1 : ℕ) : ℝ) / ((max s 1 : ℕ) : ℝ))| ≤ C₀)
    {s n : ℕ} (hsn : s ≤ n) {R : ℝ}
    (hRatio : (((max n 1 : ℕ) : ℝ) / ((max s 1 : ℕ) : ℝ)) ≤ R) :
    Critical2DKPZ.replicaOverlap n - Critical2DKPZ.replicaOverlap s ≤
      (Real.log R + C₀) / Real.pi := by
  have hspos : 0 < ((max s 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < max s 1 by omega)
  have hnpos : 0 < ((max n 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < max n 1 by omega)
  have hratioPos : 0 < (((max n 1 : ℕ) : ℝ) / ((max s 1 : ℕ) : ℝ)) :=
    div_pos hnpos hspos
  have hlogRatio := Real.log_le_log hratioPos hRatio
  have herror := (abs_le.mp (hC₀ s n hsn)).2
  have hboundPi : Real.pi *
      (Critical2DKPZ.replicaOverlap n - Critical2DKPZ.replicaOverlap s) ≤
      Real.log R + C₀ := by linarith
  apply (le_div_iff₀ Real.pi_pos).2
  nlinarith [hboundPi]

/-- The uniform one-point estimate turns a bounded endpoint ratio into a
variance bound with an explicit logarithmic distance-to-horizon denominator.
All constants are chosen before the horizon and block endpoints. -/
theorem smoothedP2Plane_variance_le_of_ratio_bound (A T R : ℝ) :
    ∃ C₀ Cvar : ℝ, 0 ≤ Cvar ∧
      ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ s n : ℕ, s ≤ n →
        1 ≤ n → (n : ℝ) ≤ T * N →
        (((max n 1 : ℕ) : ℝ) / ((max s 1 : ℕ) : ℝ)) ≤ R →
        ProbabilityTheory.variance
          (fun ω : Disorder => Critical2DKPZ.smoothedP2Plane
            (Critical2DKPZ.criticalBeta ϑ N) s n 0 ω) disorderLaw ≤
          Cvar * ((Real.log R + C₀) / Real.pi) /
            Real.log (1 + (N : ℝ) / n) := by
  obtain ⟨Cvar, hCvarNonneg, hNvar⟩ :=
    smoothedP2Plane_variance_le_uniform A T
  obtain ⟨C₀, hC₀⟩ := Critical2DKPZ.OnePoint.replicaOverlap_sub_log_bounded
  refine ⟨C₀, Cvar, hCvarNonneg, ?_⟩
  filter_upwards [hNvar, Filter.eventually_ge_atTop 2] with N hNvar hN2
  intro ϑ hϑ s n hsn hn hnT hratio
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hden : 0 < Real.log (1 + (N : ℝ) / n) := by
    apply Real.log_pos
    have hfrac : 0 < (N : ℝ) / n := div_pos hNpos hnpos
    linarith
  have hoverlap := replicaOverlap_sub_le_of_ratio_bound C₀ hC₀ hsn hratio
  have hvariance := hNvar ϑ hϑ s n hsn hn hnT
  calc
    ProbabilityTheory.variance
        (fun ω : Disorder => Critical2DKPZ.smoothedP2Plane
          (Critical2DKPZ.criticalBeta ϑ N) s n 0 ω) disorderLaw ≤
        Cvar * (Critical2DKPZ.replicaOverlap n -
          Critical2DKPZ.replicaOverlap s) /
          Real.log (1 + (N : ℝ) / n) := hvariance
    _ ≤ Cvar * ((Real.log R + C₀) / Real.pi) /
          Real.log (1 + (N : ℝ) / n) := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact mul_le_mul_of_nonneg_left hoverlap hCvarNonneg

/-- Every interior geometric block after the first has endpoint-scale ratio at
most `ρ + 2`. The two units account for even-clock rounding; the lower scale
bound on the preceding endpoint absorbs them. -/
theorem blockTime_endpoint_ratio_le {N i : ℕ} {ρ : ℝ}
    (hρ : 1 < ρ) (hi : 2 ≤ i)
    (hiK : i < Critical2DKPZ.blockCount N ρ) :
    (((max (Critical2DKPZ.blockTime N ρ i) 1 : ℕ) : ℝ) /
      ((max (Critical2DKPZ.blockTime N ρ (i - 1)) 1 : ℕ) : ℝ)) ≤ ρ + 2 := by
  let s := Critical2DKPZ.blockTime N ρ (i - 1)
  let n := Critical2DKPZ.blockTime N ρ i
  have hiPrev : 1 ≤ i - 1 := by omega
  have hiPrevK : i - 1 < Critical2DKPZ.blockCount N ρ := by omega
  have hsLower := blockTime_lower_geometric_scale hρ hiPrev hiPrevK
  have hnLower := blockTime_lower_geometric_scale hρ (by omega) hiK
  have hsOne : (1 : ℝ) ≤ (s : ℝ) := by
    have hExp : 0 ≤ ((i - 1 : ℕ) : ℝ) - 1 := by
      have hcast : (1 : ℝ) ≤ ((i - 1 : ℕ) : ℝ) := by exact_mod_cast hiPrev
      linarith
    calc
      1 ≤ ρ ^ (((i - 1 : ℕ) : ℝ) - 1) :=
        Real.one_le_rpow hρ.le hExp
      _ ≤ (s : ℝ) := by simpa [s] using hsLower
  have hnOne : (1 : ℝ) ≤ (n : ℝ) := by
    calc
      1 ≤ ρ ^ ((i : ℝ) - 1) := by
        apply Real.one_le_rpow hρ.le
        have hcast : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast (show 1 ≤ i from by omega)
        linarith
      _ ≤ (n : ℝ) := by simpa [n] using hnLower
  have hsNat : 1 ≤ s := by exact_mod_cast hsOne
  have hnNat : 1 ≤ n := by exact_mod_cast hnOne
  have hsFormula : s = Critical2DKPZ.evenCeil
      ((N : ℝ) * ρ ^ (((i - 1 : ℕ) : ℝ) - Critical2DKPZ.blockCount N ρ)) := by
    simp [s, Critical2DKPZ.blockTime, Nat.ne_of_gt (Nat.zero_lt_of_lt hiPrev), hiPrevK]
  have hnFormula : n = Critical2DKPZ.evenCeil
      ((N : ℝ) * ρ ^ ((i : ℝ) - Critical2DKPZ.blockCount N ρ)) := by
    simp [n, Critical2DKPZ.blockTime, Nat.ne_of_gt (by omega : 0 < i), hiK]
  let x := (N : ℝ) * ρ ^ (((i - 1 : ℕ) : ℝ) - Critical2DKPZ.blockCount N ρ)
  have hxNonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hxle : x ≤ (s : ℝ) := by
    dsimp [x]
    rw [hsFormula]
    exact Critical2DKPZ.le_evenCeil _
  have hpow : ρ ^ ((i : ℝ) - Critical2DKPZ.blockCount N ρ) =
      ρ ^ (((i - 1 : ℕ) : ℝ) - Critical2DKPZ.blockCount N ρ) * ρ := by
    have hiCast : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by
      exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ i))
    rw [show (i : ℝ) - Critical2DKPZ.blockCount N ρ =
        (((i - 1 : ℕ) : ℝ) - Critical2DKPZ.blockCount N ρ) + 1 by linarith,
      Real.rpow_add (by linarith : 0 < ρ), Real.rpow_one]
  have hnUpper : (n : ℝ) < ρ * x + 2 := by
    rw [hnFormula]
    rw [show (N : ℝ) * ρ ^ ((i : ℝ) - Critical2DKPZ.blockCount N ρ) = ρ * x by
      dsimp [x]
      rw [hpow]
      ring]
    exact Critical2DKPZ.evenCeil_lt_add_two (by positivity)
  have hnBound : (n : ℝ) ≤ (ρ + 2) * (s : ℝ) := by
    have hρnonneg : 0 ≤ ρ := le_of_lt (lt_trans (by norm_num) hρ)
    calc
      (n : ℝ) ≤ ρ * x + 2 := hnUpper.le
      _ ≤ ρ * (s : ℝ) + 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hxle hρnonneg]
      _ ≤ (ρ + 2) * (s : ℝ) := by
        nlinarith [hsOne]
  have hmaxn : max n 1 = n := max_eq_left hnNat
  have hmaxs : max s 1 = s := max_eq_left hsNat
  rw [hmaxn, hmaxs]
  apply (div_le_iff₀ (by exact_mod_cast (show 0 < s by omega))).2
  exact hnBound

/-- The first block has endpoint ratio at most `ρ + 2`; its zero-time start is
handled by the unit floor in the overlap ratio. -/
theorem blockTime_first_endpoint_ratio_le {N : ℕ} {ρ : ℝ}
    (hρ : 1 < ρ) (hρN : ρ ≤ (N : ℝ)) :
    (((max (Critical2DKPZ.blockTime N ρ 1) 1 : ℕ) : ℝ) /
      ((max (Critical2DKPZ.blockTime N ρ 0) 1 : ℕ) : ℝ)) ≤ ρ + 2 := by
  have hK := blockCount_ge_two_of_ratio_le_horizon hρ hρN
  have h1K : 1 < Critical2DKPZ.blockCount N ρ := by omega
  have hnLower := blockTime_lower_geometric_scale hρ (by omega) h1K
  have hnNat : 1 ≤ Critical2DKPZ.blockTime N ρ 1 := by
    have hreal : (1 : ℝ) ≤ (Critical2DKPZ.blockTime N ρ 1 : ℝ) := by
      simpa using hnLower
    exact_mod_cast hreal
  have hmaxn : max (Critical2DKPZ.blockTime N ρ 1) 1 =
      Critical2DKPZ.blockTime N ρ 1 := max_eq_left hnNat
  have hmaxs : max (Critical2DKPZ.blockTime N ρ 0) 1 = 1 := by
    simp [Critical2DKPZ.blockTime]
  rw [hmaxn, hmaxs]
  have hupper := blockTime_first_endpoint_lt hρ hρN
  simpa using hupper.le

/-- A cubic comparison gives a convenient logarithmic loss of one third. -/
theorem log_one_add_third_le (x : ℝ) (hx : 0 ≤ x) :
    (1 / 3 : ℝ) * Real.log (1 + x) ≤ Real.log (1 + x / 3) := by
  have hpoly : 1 + x ≤ (1 + x / 3) ^ 3 := by
    nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) hx]
  have hlog := Real.log_le_log (by positivity : 0 < 1 + x) hpoly
  rw [Real.log_pow] at hlog
  nlinarith

/-- The geometric clock's logarithmic denominator grows at least linearly in
the number of remaining blocks. The one-third factor absorbs the two-unit
even-ceiling error in the endpoint. -/
theorem blockTime_log_horizon_lower {N i : ℕ} {ρ₀ ρ : ℝ}
    (hρ₀ : 1 < ρ₀) (hρ₀ρ : ρ₀ ≤ ρ) (hi : 1 ≤ i)
    (hiK : i < Critical2DKPZ.blockCount N ρ) :
    ((Critical2DKPZ.blockCount N ρ - i : ℕ) : ℝ) * Real.log ρ₀ / 3 ≤
      Real.log (1 + (N : ℝ) / Critical2DKPZ.blockTime N ρ i) := by
  have hρ : 1 < ρ := lt_of_lt_of_le hρ₀ hρ₀ρ
  let K := Critical2DKPZ.blockCount N ρ
  let d := K - i
  let n := Critical2DKPZ.blockTime N ρ i
  let x := (N : ℝ) * ρ ^ ((i : ℝ) - (K : ℝ))
  have hiKle : i ≤ K := Nat.le_of_lt hiK
  have hdcast : (d : ℝ) = (K : ℝ) - (i : ℝ) := by
    dsimp [d]
    rw [Nat.cast_sub hiKle]
  have hnLower := blockTime_lower_geometric_scale hρ (by omega) hiK
  have hrawLower : 1 ≤ x := by
    have hexp : 0 ≤ (i : ℝ) - 1 := by
      have hiCast : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
      linarith
    have hpow : 1 ≤ ρ ^ ((i : ℝ) - 1) := Real.one_le_rpow hρ.le hexp
    exact hpow.trans (by simpa [x, K] using
      blockTime_unrounded_geometric_scale hρ hi hiK)
  have hnFormula : n = Critical2DKPZ.evenCeil x := by
    dsimp [n, x, K]
    simp [Critical2DKPZ.blockTime, Nat.ne_of_gt (by omega : 0 < i), hiK]
  have hxNonneg : 0 ≤ x := by dsimp [x]; positivity
  have hnUpper : (n : ℝ) < x + 2 := by
    rw [hnFormula]
    exact Critical2DKPZ.evenCeil_lt_add_two hxNonneg
  have hnLeThreeX : (n : ℝ) ≤ 3 * x := by
    linarith
  have hprod : ρ ^ ((i : ℝ) - (K : ℝ)) * (ρ ^ d : ℝ) = 1 := by
    rw [← Real.rpow_natCast ρ d, ← Real.rpow_add (by linarith : 0 < ρ)]
    have hsum : (i : ℝ) - (K : ℝ) + (d : ℝ) = 0 := by
      rw [hdcast]
      ring
    rw [hsum, Real.rpow_zero]
  have hNscale : (N : ℝ) = x * (ρ ^ d : ℝ) := by
    calc
      (N : ℝ) = (N : ℝ) * 1 := by ring
      _ = (N : ℝ) *
          (ρ ^ ((i : ℝ) - (K : ℝ)) * (ρ ^ d : ℝ)) := by simp [hprod]
      _ = x * (ρ ^ d : ℝ) := by dsimp [x]; ring
  have hnPos : 0 < (n : ℝ) := by
    have hpowPos : 0 < ρ ^ ((i : ℝ) - 1) := Real.rpow_pos_of_pos (by linarith) _
    exact lt_of_lt_of_le hpowPos hnLower
  have hpowNonneg : 0 ≤ (ρ ^ d : ℝ) := by positivity
  have hratioLower : (ρ ^ d : ℝ) / 3 ≤ (N : ℝ) / n := by
    apply (le_div_iff₀ hnPos).2
    calc
      ((ρ ^ d : ℝ) / 3) * (n : ℝ) ≤ ((ρ ^ d : ℝ) / 3) * (3 * x) :=
        mul_le_mul_of_nonneg_left hnLeThreeX (div_nonneg hpowNonneg (by norm_num))
      _ = x * (ρ ^ d : ℝ) := by ring
      _ = (N : ℝ) := hNscale.symm
  have hratioPos : 0 < (ρ ^ d : ℝ) := pow_pos (by linarith : 0 < ρ) d
  have hlogMono : Real.log (1 + (ρ ^ d : ℝ) / 3) ≤
      Real.log (1 + (N : ℝ) / n) := by
    apply Real.log_le_log (by positivity)
    linarith
  have hthird := log_one_add_third_le (ρ ^ d : ℝ) (pow_nonneg (le_of_lt (by linarith : 0 < ρ)) d)
  have hlogpow : (d : ℝ) * Real.log ρ ≤ Real.log (1 + (ρ ^ d : ℝ)) := by
    calc
      (d : ℝ) * Real.log ρ = Real.log (ρ ^ d : ℝ) := by rw [Real.log_pow]
      _ ≤ Real.log (1 + (ρ ^ d : ℝ)) := by
        apply Real.log_le_log hratioPos
        linarith
  have hlogρ : Real.log ρ₀ ≤ Real.log ρ :=
    Real.log_le_log (by linarith : 0 < ρ₀) hρ₀ρ
  have hdlog : ((d : ℝ) * Real.log ρ₀) / 3 ≤
      ((d : ℝ) * Real.log ρ) / 3 := by
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 3)
    exact mul_le_mul_of_nonneg_left hlogρ (Nat.cast_nonneg d)
  calc
    ((d : ℝ) * Real.log ρ₀) / 3 ≤ ((d : ℝ) * Real.log ρ) / 3 := hdlog
    _ ≤ Real.log (1 + (ρ ^ d : ℝ)) / 3 := by linarith
    _ ≤ Real.log (1 + (ρ ^ d : ℝ) / 3) := by
      calc
        Real.log (1 + (ρ ^ d : ℝ)) / 3 =
            (1 / 3 : ℝ) * Real.log (1 + (ρ ^ d : ℝ)) := by ring
        _ ≤ Real.log (1 + (ρ ^ d : ℝ) / 3) := hthird
    _ ≤ Real.log (1 + (N : ℝ) / n) := hlogMono

/-- Uniform variance control for every noninitial geometric block, once the
clock is monotone and stays below the horizon. The remaining denominator is
the logarithmic distance from the terminal scale. -/
theorem block_interior_variance_le_uniform (A ρmax : ℝ) :
    ∃ C₀ Cvar : ℝ, 0 ≤ Cvar ∧
      ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ ρ : ℝ, 1 < ρ →
        ρ ≤ ρmax → ∀ i : ℕ,
          1 ≤ i → i < Critical2DKPZ.blockCount N ρ →
          Monotone (Critical2DKPZ.blockTime N ρ) →
          Critical2DKPZ.blockTime N ρ i ≤ N →
          ProbabilityTheory.variance
            (fun ω : Disorder => Critical2DKPZ.smoothedP2Plane
              (Critical2DKPZ.criticalBeta ϑ N)
              (Critical2DKPZ.blockTime N ρ (i - 1))
              (Critical2DKPZ.blockTime N ρ i) 0 ω) disorderLaw ≤
            Cvar * ((Real.log (ρmax + 2) + C₀) / Real.pi) /
              Real.log (1 + (N : ℝ) / Critical2DKPZ.blockTime N ρ i) := by
  obtain ⟨C₀, Cvar, hCvar, hN⟩ :=
    smoothedP2Plane_variance_le_of_ratio_bound A 1 (ρmax + 2)
  refine ⟨C₀, Cvar, hCvar, ?_⟩
  filter_upwards [hN] with N hN
  intro ϑ hϑ ρ hρ hρmax i hi hiK hclock htimeN
  let s := Critical2DKPZ.blockTime N ρ (i - 1)
  let n := Critical2DKPZ.blockTime N ρ i
  have hsn : s ≤ n := by
    dsimp [s, n]
    exact hclock (Nat.sub_le i 1)
  have hnLower := blockTime_lower_geometric_scale hρ (by omega) hiK
  have hnPowOne : (1 : ℝ) ≤ ρ ^ ((i : ℝ) - 1) := by
    apply Real.one_le_rpow hρ.le
    have hiCast : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast (show 1 ≤ i from by omega)
    linarith
  have hnOne : 1 ≤ n := by
    have hnOneReal : (1 : ℝ) ≤ (n : ℝ) := by
      dsimp [n]
      exact hnPowOne.trans hnLower
    exact_mod_cast hnOneReal
  have hratioρ :
      (((max n 1 : ℕ) : ℝ) / ((max s 1 : ℕ) : ℝ)) ≤ ρ + 2 := by
    by_cases hi1 : i = 1
    · subst i
      simpa [s, n] using blockTime_first_endpoint_ratio_le hρ
        (ratio_le_horizon_of_blockCount_ge_two hρ (by omega))
    · have hi2 : 2 ≤ i := by omega
      simpa [s, n] using blockTime_endpoint_ratio_le hρ hi2 hiK
  have hratio : (((max n 1 : ℕ) : ℝ) / ((max s 1 : ℕ) : ℝ)) ≤ ρmax + 2 := by
    dsimp [s, n] at hratioρ ⊢
    linarith
  have hnN : (n : ℝ) ≤ 1 * (N : ℝ) := by
    have htimeNreal : (Critical2DKPZ.blockTime N ρ i : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast htimeN
    simpa [n] using htimeNreal
  have hbound := hN ϑ hϑ s n hsn hnOne hnN hratio
  simpa [s, n] using hbound

/-- On a compact geometric-ratio range, every noninitial nonterminal block has
variance at most a constant divided by the number of remaining blocks. -/
theorem block_interior_variance_le_inverse_remaining (A ρ₀ ρmax : ℝ)
    (hρ₀ : 1 < ρ₀) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ ρ : ℝ,
        ρ₀ ≤ ρ → ρ ≤ ρmax → ∀ i : ℕ,
          1 ≤ i → i < Critical2DKPZ.blockCount N ρ →
          Monotone (Critical2DKPZ.blockTime N ρ) →
          Critical2DKPZ.blockTime N ρ i ≤ N →
          ProbabilityTheory.variance
            (fun ω : Disorder => Critical2DKPZ.smoothedP2Plane
              (Critical2DKPZ.criticalBeta ϑ N)
              (Critical2DKPZ.blockTime N ρ (i - 1))
              (Critical2DKPZ.blockTime N ρ i) 0 ω) disorderLaw ≤
            C / ((Critical2DKPZ.blockCount N ρ - i : ℕ) : ℝ) := by
  obtain ⟨C₀, Cvar, hCvar, hNvar⟩ :=
    block_interior_variance_le_uniform A ρmax
  let A₀ := Cvar * ((Real.log (ρmax + 2) + C₀) / Real.pi)
  let C := 3 * |A₀| / Real.log ρ₀
  have hlogρ₀ : 0 < Real.log ρ₀ := Real.log_pos hρ₀
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (mul_nonneg (by norm_num) (abs_nonneg A₀)) hlogρ₀.le
  refine ⟨C, hCnonneg, ?_⟩
  filter_upwards [hNvar] with N hNvar
  intro ϑ hϑ ρ hρ₀ρ hρmax i hi hiK hclock htimeN
  let d : ℕ := Critical2DKPZ.blockCount N ρ - i
  have hdpos : 0 < d := by dsimp [d]; omega
  have hdenlower := blockTime_log_horizon_lower hρ₀ hρ₀ρ hi hiK
  have hdenpos : 0 < Real.log
      (1 + (N : ℝ) / Critical2DKPZ.blockTime N ρ i) := by
    have hlowpos : 0 < ((d : ℝ) * Real.log ρ₀ / 3) := by
      have hdposReal : 0 < (d : ℝ) := by exact_mod_cast hdpos
      positivity
    exact lt_of_lt_of_le hlowpos hdenlower
  have hbase := hNvar ϑ hϑ ρ (lt_of_lt_of_le hρ₀ hρ₀ρ) hρmax i hi hiK hclock htimeN
  have hbaseAbs : A₀ / Real.log
        (1 + (N : ℝ) / Critical2DKPZ.blockTime N ρ i) ≤
      |A₀| / Real.log
        (1 + (N : ℝ) / Critical2DKPZ.blockTime N ρ i) :=
    div_le_div_of_nonneg_right (le_abs_self A₀) hdenpos.le
  have hbaseDen : |A₀| / Real.log
        (1 + (N : ℝ) / Critical2DKPZ.blockTime N ρ i) ≤
      |A₀| / ((d : ℝ) * Real.log ρ₀ / 3) :=
    div_le_div_of_nonneg_left (abs_nonneg A₀)
      (by positivity : 0 < (d : ℝ) * Real.log ρ₀ / 3) hdenlower
  have hdposReal : 0 < (d : ℝ) := by exact_mod_cast hdpos
  have halgebra : |A₀| / ((d : ℝ) * Real.log ρ₀ / 3) = C / (d : ℝ) := by
    dsimp [C]
    field_simp [ne_of_gt hdposReal, ne_of_gt hlogρ₀]
  calc
    ProbabilityTheory.variance
        (fun ω : Disorder => Critical2DKPZ.smoothedP2Plane
          (Critical2DKPZ.criticalBeta ϑ N)
          (Critical2DKPZ.blockTime N ρ (i - 1))
          (Critical2DKPZ.blockTime N ρ i) 0 ω) disorderLaw ≤
        A₀ / Real.log (1 + (N : ℝ) / Critical2DKPZ.blockTime N ρ i) := by
          simpa [A₀] using hbase
    _ ≤ |A₀| / Real.log
          (1 + (N : ℝ) / Critical2DKPZ.blockTime N ρ i) := hbaseAbs
    _ ≤ |A₀| / ((d : ℝ) * Real.log ρ₀ / 3) := hbaseDen
    _ = C / ((Critical2DKPZ.blockCount N ρ - i : ℕ) : ℝ) := by
      simpa [d] using halgebra

/-- Uniform compact-ratio form of the interior variance estimate. The large
horizon threshold supplies clock monotonicity and places every nonterminal
endpoint below the horizon, so the hypotheses are internal to the conclusion. -/
theorem block_interior_variance_le_inverse_remaining_compact
    (A ρ₀ ρmax : ℝ) (hρ₀ : 1 < ρ₀) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ ρ : ℝ,
        ρ₀ ≤ ρ → ρ ≤ ρmax → ∀ i : ℕ,
          1 ≤ i → i < Critical2DKPZ.blockCount N ρ →
          ProbabilityTheory.variance
            (fun ω : Disorder => Critical2DKPZ.smoothedP2Plane
              (Critical2DKPZ.criticalBeta ϑ N)
              (Critical2DKPZ.blockTime N ρ (i - 1))
              (Critical2DKPZ.blockTime N ρ i) 0 ω) disorderLaw ≤
            C / ((Critical2DKPZ.blockCount N ρ - i : ℕ) : ℝ) := by
  obtain ⟨C, hC, hNvar⟩ :=
    block_interior_variance_le_inverse_remaining A ρ₀ ρmax hρ₀
  let Nclock := ⌈2 * ρ₀ / (ρ₀ - 1)⌉₊
  let Nrho := ⌈ρmax⌉₊
  refine ⟨C, hC, ?_⟩
  filter_upwards [hNvar,
    Filter.eventually_ge_atTop (max Nclock Nrho)] with N hNvar hNthreshold
  intro ϑ hϑ ρ hρ₀ρ hρmax i hi hiK
  have hNceil : Nrho ≤ N := le_trans (Nat.le_max_right Nclock Nrho) hNthreshold
  have hNclock : Nclock ≤ N := le_trans (Nat.le_max_left Nclock Nrho) hNthreshold
  have hρ₀ρ' : ρ₀ ≤ ρ := hρ₀ρ
  have hρ : 1 < ρ := lt_of_lt_of_le hρ₀ hρ₀ρ'
  have hρN : ρ ≤ (N : ℝ) := by
    have hceil : ρmax ≤ (Nrho : ℝ) := by simpa [Nrho] using Nat.le_ceil ρmax
    have hNcast : (Nrho : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNceil
    exact hρmax.trans (hceil.trans hNcast)
  have hclock := blockTime_monotone_of_large_horizon hρ₀ hρ₀ρ' (by
    simpa [Nclock] using hNclock)
  have hK : 2 ≤ Critical2DKPZ.blockCount N ρ :=
    blockCount_ge_two_of_ratio_le_horizon hρ hρN
  have hfinal : Critical2DKPZ.blockTime N ρ
      (Critical2DKPZ.blockCount N ρ) = N := by
    simp [Critical2DKPZ.blockTime,
      Nat.ne_of_gt (by omega : 0 < Critical2DKPZ.blockCount N ρ)]
  have htimeN : Critical2DKPZ.blockTime N ρ i ≤ N := by
    calc
      Critical2DKPZ.blockTime N ρ i ≤
          Critical2DKPZ.blockTime N ρ (Critical2DKPZ.blockCount N ρ) :=
        hclock (Nat.le_of_lt hiK)
      _ = N := hfinal
  exact hNvar ϑ hϑ ρ hρ₀ρ hρmax i hi hiK hclock htimeN

/-- The terminal block has a uniform variance bound on compact ratio ranges;
its denominator is exactly `log 2` and the endpoint ratio is at most `ρ²`. -/
theorem block_final_variance_le_uniform (A ρ₀ ρmax : ℝ) (hρ₀ : 1 < ρ₀) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ ρ : ℝ,
        ρ₀ ≤ ρ → ρ ≤ ρmax →
        ProbabilityTheory.variance
          (fun ω : Disorder => Critical2DKPZ.smoothedP2Plane
            (Critical2DKPZ.criticalBeta ϑ N)
            (Critical2DKPZ.blockTime N ρ
              (Critical2DKPZ.blockCount N ρ - 1)) N 0 ω) disorderLaw ≤ C := by
  obtain ⟨C₀, Cvar, hCvar, hN⟩ :=
    smoothedP2Plane_variance_le_of_ratio_bound A 1 (ρmax ^ 2)
  let A₀ := Cvar * ((Real.log (ρmax ^ 2) + C₀) / Real.pi)
  let C := |A₀ / Real.log 2|
  have hCnonneg : 0 ≤ C := by dsimp [C]; exact abs_nonneg _
  refine ⟨C, hCnonneg, ?_⟩
  let Nclock := ⌈2 * ρ₀ / (ρ₀ - 1)⌉₊
  let Nrho := ⌈ρmax⌉₊
  filter_upwards [hN,
    Filter.eventually_ge_atTop (max Nclock Nrho)] with N hN hNthreshold
  intro ϑ hϑ ρ hρ₀ρ hρmax
  have hNceil : Nrho ≤ N := le_trans (Nat.le_max_right Nclock Nrho) hNthreshold
  have hNclock : Nclock ≤ N := le_trans (Nat.le_max_left Nclock Nrho) hNthreshold
  have hρ : 1 < ρ := lt_of_lt_of_le hρ₀ hρ₀ρ
  have hρN : ρ ≤ (N : ℝ) := by
    have hceil : ρmax ≤ (Nrho : ℝ) := by simpa [Nrho] using Nat.le_ceil ρmax
    have hNcast : (Nrho : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNceil
    exact hρmax.trans (hceil.trans hNcast)
  have hclock := blockTime_monotone_of_large_horizon hρ₀ hρ₀ρ (by
    simpa [Nclock] using hNclock)
  have hK : 2 ≤ Critical2DKPZ.blockCount N ρ :=
    blockCount_ge_two_of_ratio_le_horizon hρ hρN
  let K := Critical2DKPZ.blockCount N ρ
  let s := Critical2DKPZ.blockTime N ρ (K - 1)
  have hsn : s ≤ N := by
    have hfinal : Critical2DKPZ.blockTime N ρ K = N := by
      simp [Critical2DKPZ.blockTime, K, Nat.ne_of_gt (by omega :
        0 < Critical2DKPZ.blockCount N ρ)]
    calc
      s ≤ Critical2DKPZ.blockTime N ρ K := by
        dsimp [s, K]
        exact hclock (Nat.sub_le (Critical2DKPZ.blockCount N ρ) 1)
      _ = N := hfinal
  have hNpos : 0 < (N : ℝ) := by linarith
  have hnOne : 1 ≤ N := by exact_mod_cast (show (1 : ℝ) ≤ (N : ℝ) by linarith)
  have hratioρ := blockTime_final_endpoint_ratio_le hρ hK
  have hρnonneg : 0 ≤ ρ := by linarith
  have hρmaxnonneg : 0 ≤ ρmax := by linarith
  have hpowMono : Real.rpow ρ 2 ≤ ρmax ^ 2 := by
    have hsq : ρ ^ 2 ≤ ρmax ^ 2 := by
      simpa only [pow_two] using mul_le_mul hρmax hρmax hρnonneg hρmaxnonneg
    calc
      Real.rpow ρ 2 = ρ ^ 2 := Real.rpow_natCast ρ 2
      _ ≤ ρmax ^ 2 := hsq
  have hratio :
      (((max N 1 : ℕ) : ℝ) / ((max s 1 : ℕ) : ℝ)) ≤ ρmax ^ 2 := by
    dsimp [s, K] at hratioρ ⊢
    exact hratioρ.trans hpowMono
  have hbound := hN ϑ hϑ s N hsn hnOne (by norm_num) hratio
  have hlogden : Real.log (1 + (N : ℝ) / N) = Real.log 2 := by
    rw [div_self (ne_of_gt hNpos)]
    norm_num
  have hbound' :
      ProbabilityTheory.variance
        (fun ω : Disorder => Critical2DKPZ.smoothedP2Plane
          (Critical2DKPZ.criticalBeta ϑ N) s N 0 ω) disorderLaw ≤ A₀ / Real.log 2 := by
    simpa only [A₀, hlogden] using hbound
  have habs : A₀ / Real.log 2 ≤ C := le_abs_self _
  simpa [s, K, C] using hbound'.trans habs

end Critical2DKPZ.MomentBounds

end
