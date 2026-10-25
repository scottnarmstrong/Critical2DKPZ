/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.BlockClockBounds
public import Critical2DKPZ.MomentBounds.ShortDurationMoments
import Critical2DKPZ.Blocks.Core
import Mathlib.Tactic

/-! # Uniform moment bounds for bounded geometric blocks -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.MomentBounds


/-- At sufficiently small disorder strength, the centered fourth moment of a bounded interior geometric block is at most a uniform constant times its squared variance. -/
theorem block_shortDuration_fourth_moment (Ldur : ℕ)
    {ρ₀ : ℝ} (hρ₀ : 1 < ρ₀) :
    ∃ β₀ C : ℝ, 0 < β₀ ∧ ∀ {N i : ℕ} {ρ : ℝ}, ρ₀ ≤ ρ →
      Monotone (Critical2DKPZ.blockTime N ρ) →
      1 ≤ i → i < Critical2DKPZ.blockCount N ρ →
      Critical2DKPZ.blockTime N ρ i -
        Critical2DKPZ.blockTime N ρ (i - 1) ≤ Ldur →
      ∀ β : ℝ, 0 ≤ β → β ≤ β₀ →
      (∫ ω : Disorder,
        |Critical2DKPZ.smoothedP2Plane β
          (Critical2DKPZ.blockTime N ρ (i - 1))
          (Critical2DKPZ.blockTime N ρ i) 0 ω - 1| ^ 4 ∂disorderLaw ≤
        C * ProbabilityTheory.variance
          (fun ω : Disorder => Critical2DKPZ.smoothedP2Plane β
            (Critical2DKPZ.blockTime N ρ (i - 1))
            (Critical2DKPZ.blockTime N ρ i) 0 ω) disorderLaw ^ 2) ∧
      (∫ ω : Disorder,
        |Critical2DKPZ.smoothedP2Plane β
          (Critical2DKPZ.blockTime N ρ (i - 1))
          (Critical2DKPZ.blockTime N ρ i) 0 ω - 1| ^ 4 ∂disorderLaw ≤ C * β ^ 4) := by
  let M : ℝ := ((Ldur : ℝ) + 2) / (1 - ρ₀⁻¹) + 2
  let H : ℕ := max 1 ⌈M⌉₊
  have hMden : 0 < 1 - ρ₀⁻¹ := by
    have hρ₀pos : 0 < ρ₀ := by linarith
    have hInvLt : ρ₀⁻¹ < 1 := (inv_lt_one₀ hρ₀pos).2 hρ₀
    linarith
  have hceil : M ≤ (⌈M⌉₊ : ℝ) := Nat.le_ceil M
  have hHpositive : 1 ≤ H := by
    exact Nat.le_trans (Nat.le_max_left 1 ⌈M⌉₊) le_rfl
  obtain ⟨β₀, C, hβ₀, hShortHorizonFourthMomentInput⟩ :=
    smoothedP2Plane_fourth_moment_shortHorizon H
  have hCnonneg : 0 ≤ C := by
    let βtest : ℝ := β₀ / 2
    have hβtest : 0 < βtest := by dsimp [βtest]; positivity
    have hβtest0 : 0 ≤ βtest := hβtest.le
    have hβtestle : βtest ≤ β₀ := by dsimp [βtest]; linarith
    have hzero : 0 ≤ ∫ ω : Disorder,
        |Critical2DKPZ.smoothedP2Plane βtest 0 1 0 ω - 1| ^ 4 ∂disorderLaw :=
      integral_nonneg fun ω => by positivity
    have htest := (hShortHorizonFourthMomentInput βtest hβtest0 hβtestle 0 1 (by omega) hHpositive 0).2
    have hpow : 0 < βtest ^ 4 := pow_pos hβtest 4
    nlinarith
  refine ⟨β₀, C, hβ₀, ?_⟩
  intro N i ρ hρ hclock hi hiK hdur β hβ0 hβle
  have hendpoint := blockTime_endpoint_lt_of_duration_le Ldur hρ₀ hρ hi hiK hdur
  have htimeReal : (Critical2DKPZ.blockTime N ρ i : ℝ) < (⌈M⌉₊ : ℝ) := by
    dsimp [M] at hendpoint ⊢
    exact hendpoint.trans_le hceil
  have htimeBound : Critical2DKPZ.blockTime N ρ i ≤ H := by
    have htimeBoundReal : (Critical2DKPZ.blockTime N ρ i : ℝ) ≤ (H : ℝ) := by
      exact htimeReal.le.trans (by exact_mod_cast (Nat.le_max_right 1 ⌈M⌉₊))
    exact_mod_cast htimeBoundReal
  have hmono : Critical2DKPZ.blockTime N ρ (i - 1) ≤
      Critical2DKPZ.blockTime N ρ i := hclock (Nat.sub_le i 1)
  by_cases hstrict : Critical2DKPZ.blockTime N ρ (i - 1) <
      Critical2DKPZ.blockTime N ρ i
  · exact hShortHorizonFourthMomentInput β hβ0 hβle
      (Critical2DKPZ.blockTime N ρ (i - 1))
      (Critical2DKPZ.blockTime N ρ i) hstrict htimeBound 0
  · have heq : Critical2DKPZ.blockTime N ρ (i - 1) =
        Critical2DKPZ.blockTime N ρ i := by omega
    have hconstant : (fun ω : Disorder => Critical2DKPZ.smoothedP2Plane β
        (Critical2DKPZ.blockTime N ρ (i - 1))
        (Critical2DKPZ.blockTime N ρ i) 0 ω) = fun _ => (1 : ℝ) := by
      funext ω
      rw [heq]
      exact Critical2DKPZ.Blocks.smoothedP2Plane_eq_one_of_eq β _ ω
    have hmoment : ∫ ω : Disorder,
        |Critical2DKPZ.smoothedP2Plane β
          (Critical2DKPZ.blockTime N ρ (i - 1))
          (Critical2DKPZ.blockTime N ρ i) 0 ω - 1| ^ 4 ∂disorderLaw = 0 := by
      rw [show (fun ω : Disorder =>
        |Critical2DKPZ.smoothedP2Plane β
          (Critical2DKPZ.blockTime N ρ (i - 1))
          (Critical2DKPZ.blockTime N ρ i) 0 ω - 1| ^ 4) =
          fun _ => (0 : ℝ) from funext fun ω => by
            rw [heq, Critical2DKPZ.Blocks.smoothedP2Plane_eq_one_of_eq]
            norm_num]
      simp
    have hvariance : ProbabilityTheory.variance
        (fun ω : Disorder => Critical2DKPZ.smoothedP2Plane β
          (Critical2DKPZ.blockTime N ρ (i - 1))
          (Critical2DKPZ.blockTime N ρ i) 0 ω) disorderLaw = 0 := by
      rw [hconstant]
      rw [ProbabilityTheory.variance_eq_integral (by fun_prop)]
      simp
    constructor
    · rw [hmoment, hvariance]
      positivity
    · rw [hmoment]
      exact mul_nonneg hCnonneg (by positivity)

/-- A bounded terminal geometric block has a bounded endpoint and a centered fourth moment controlled by its squared variance when the ratio stays away from one. -/
theorem block_final_shortDuration_fourth_moment (Ldur : ℕ)
    {ρ₀ : ℝ} (hρ₀ : 1 < ρ₀) :
    ∃ β₀ C : ℝ, 0 < β₀ ∧ ∀ {N : ℕ} {ρ : ℝ}, ρ₀ ≤ ρ →
      Monotone (Critical2DKPZ.blockTime N ρ) →
      Critical2DKPZ.blockTime N ρ (Critical2DKPZ.blockCount N ρ) -
        Critical2DKPZ.blockTime N ρ (Critical2DKPZ.blockCount N ρ - 1) ≤ Ldur →
      ∀ β : ℝ, 0 ≤ β → β ≤ β₀ →
      (∫ ω : Disorder,
        |Critical2DKPZ.smoothedP2Plane β
          (Critical2DKPZ.blockTime N ρ (Critical2DKPZ.blockCount N ρ - 1))
          (Critical2DKPZ.blockTime N ρ (Critical2DKPZ.blockCount N ρ)) 0 ω - 1| ^ 4
          ∂disorderLaw ≤
        C * ProbabilityTheory.variance
          (fun ω : Disorder => Critical2DKPZ.smoothedP2Plane β
            (Critical2DKPZ.blockTime N ρ (Critical2DKPZ.blockCount N ρ - 1))
            (Critical2DKPZ.blockTime N ρ (Critical2DKPZ.blockCount N ρ)) 0 ω)
          disorderLaw ^ 2) ∧
      (∫ ω : Disorder,
        |Critical2DKPZ.smoothedP2Plane β
          (Critical2DKPZ.blockTime N ρ (Critical2DKPZ.blockCount N ρ - 1))
          (Critical2DKPZ.blockTime N ρ (Critical2DKPZ.blockCount N ρ)) 0 ω - 1| ^ 4
          ∂disorderLaw ≤ C * β ^ 4) := by
  let δ₀ : ℝ := 1 - ρ₀⁻¹
  let M : ℝ := ((Ldur : ℝ) + 2) / δ₀
  let H : ℕ := ⌈M⌉₊
  have hρ₀pos : 0 < ρ₀ := by linarith
  have hδ₀pos : 0 < δ₀ := by
    dsimp [δ₀]
    have hInvLt : ρ₀⁻¹ < 1 := (inv_lt_one₀ hρ₀pos).2 hρ₀
    linarith
  have hδ₀le : δ₀ ≤ 1 := by
    dsimp [δ₀]
    have hInvPos : 0 < ρ₀⁻¹ := inv_pos.mpr hρ₀pos
    linarith
  have hHpositive : 1 ≤ H := by
    have hMtwo : (2 : ℝ) ≤ M := by
      dsimp [M]
      apply (le_div_iff₀ hδ₀pos).2
      have hL : 0 ≤ (Ldur : ℝ) := Nat.cast_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hδ₀le (by norm_num : (0 : ℝ) ≤ 2)]
    have hcast : (1 : ℝ) ≤ (H : ℝ) := by
      have hceil : M ≤ (H : ℝ) := by
        simpa [H] using (Nat.le_ceil M)
      linarith
    exact_mod_cast hcast
  obtain ⟨β₀, C, hβ₀, hShortHorizonFourthMomentInput⟩ :=
    smoothedP2Plane_fourth_moment_shortHorizon H
  have hCnonneg : 0 ≤ C := by
    let βtest : ℝ := β₀ / 2
    have hβtest : 0 < βtest := by dsimp [βtest]; positivity
    have hβtest0 : 0 ≤ βtest := hβtest.le
    have hβtestle : βtest ≤ β₀ := by dsimp [βtest]; linarith
    have hzero : 0 ≤ ∫ ω : Disorder,
        |Critical2DKPZ.smoothedP2Plane βtest 0 1 0 ω - 1| ^ 4 ∂disorderLaw :=
      integral_nonneg fun ω => by positivity
    have htest := (hShortHorizonFourthMomentInput βtest hβtest0 hβtestle 0 1 (by omega) hHpositive 0).2
    have hpow : 0 < βtest ^ 4 := pow_pos hβtest 4
    nlinarith
  refine ⟨β₀, C, hβ₀, ?_⟩
  intro N ρ hρ hclock hdur β hβ0 hβle
  let K := Critical2DKPZ.blockCount N ρ
  have hρpos : 0 < ρ := by linarith
  have hρinv : ρ⁻¹ ≤ ρ₀⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hρ₀pos hρ
  have hKpos : 1 ≤ K := by
    dsimp [K, Critical2DKPZ.blockCount]
    omega
  have hfinal : Critical2DKPZ.blockTime N ρ K = N := by
    simp [K, Critical2DKPZ.blockTime, Nat.ne_of_gt hKpos]
  have hNbound : (N : ℝ) ≤ M := by
    by_cases hK : K = 1
    · have hprev : Critical2DKPZ.blockTime N ρ (K - 1) = 0 := by
        rw [hK]
        simp [Critical2DKPZ.blockTime]
      have hdurR : (N : ℝ) ≤ (Ldur : ℝ) := by
        have hcast : ((Critical2DKPZ.blockTime N ρ K -
            Critical2DKPZ.blockTime N ρ (K - 1) : ℕ) : ℝ) ≤ (Ldur : ℝ) := by
          exact_mod_cast hdur
        rw [hfinal, hprev] at hcast
        exact hcast
      dsimp [M]
      apply (le_div_iff₀ hδ₀pos).2
      have hL : 0 ≤ (Ldur : ℝ) := Nat.cast_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hδ₀le hL]
    · have hKtwo : 2 ≤ K := by omega
      have hρone : 1 < ρ := lt_of_lt_of_le hρ₀ hρ
      have hfactor : δ₀ ≤ 1 - ρ⁻¹ := by
        dsimp [δ₀]
        linarith
      have hNfactor : (N : ℝ) * δ₀ ≤ (Ldur : ℝ) + 2 := by
        by_cases hgap : 2 ≤ (N : ℝ) * (1 - ρ⁻¹)
        · have hlow := blockTime_final_duration_lower_geometric_scale
            hρone hKtwo hgap
          have hdurR : ((Critical2DKPZ.blockTime N ρ K -
              Critical2DKPZ.blockTime N ρ (K - 1) : ℕ) : ℝ) ≤ (Ldur : ℝ) := by
            exact_mod_cast hdur
          have hcast : ((Critical2DKPZ.blockTime N ρ K -
              Critical2DKPZ.blockTime N ρ (K - 1) : ℕ) : ℝ) =
              (Critical2DKPZ.blockTime N ρ K : ℝ) -
                (Critical2DKPZ.blockTime N ρ (K - 1) : ℝ) := by
            rw [Nat.cast_sub (hclock (Nat.sub_le K 1))]
          rw [hcast] at hlow
          calc
            (N : ℝ) * δ₀ ≤ (N : ℝ) * (1 - ρ⁻¹) := by
              exact mul_le_mul_of_nonneg_left hfactor (Nat.cast_nonneg N)
            _ ≤ (Ldur : ℝ) + 2 := by linarith
        · have hgapLt : (N : ℝ) * (1 - ρ⁻¹) < 2 := lt_of_not_ge hgap
          have hmul : (N : ℝ) * δ₀ ≤ (N : ℝ) * (1 - ρ⁻¹) :=
            mul_le_mul_of_nonneg_left hfactor (Nat.cast_nonneg N)
          have hL : 0 ≤ (Ldur : ℝ) := Nat.cast_nonneg _
          linarith
      dsimp [M]
      exact (le_div_iff₀ hδ₀pos).2 hNfactor
  have hNboundH : N ≤ H := by
    have hceil : M ≤ (H : ℝ) := by
      simpa [H] using (Nat.le_ceil M)
    exact_mod_cast hNbound.trans hceil
  have hmono : Critical2DKPZ.blockTime N ρ (K - 1) ≤
      Critical2DKPZ.blockTime N ρ K := hclock (Nat.sub_le K 1)
  have hKboundH : Critical2DKPZ.blockTime N ρ K ≤ H := by
    rw [hfinal]
    exact hNboundH
  by_cases hstrict : Critical2DKPZ.blockTime N ρ (K - 1) <
      Critical2DKPZ.blockTime N ρ K
  · exact hShortHorizonFourthMomentInput β hβ0 hβle
      (Critical2DKPZ.blockTime N ρ (K - 1))
      (Critical2DKPZ.blockTime N ρ K) hstrict hKboundH 0
  · have heq : Critical2DKPZ.blockTime N ρ (K - 1) =
        Critical2DKPZ.blockTime N ρ K := by omega
    have hconstant : (fun ω : Disorder => Critical2DKPZ.smoothedP2Plane β
        (Critical2DKPZ.blockTime N ρ (K - 1))
        (Critical2DKPZ.blockTime N ρ K) 0 ω) = fun _ => (1 : ℝ) := by
      funext ω
      rw [heq]
      exact Critical2DKPZ.Blocks.smoothedP2Plane_eq_one_of_eq β _ ω
    have hmoment : ∫ ω : Disorder,
        |Critical2DKPZ.smoothedP2Plane β
          (Critical2DKPZ.blockTime N ρ (K - 1))
          (Critical2DKPZ.blockTime N ρ K) 0 ω - 1| ^ 4 ∂disorderLaw = 0 := by
      rw [show (fun ω : Disorder =>
        |Critical2DKPZ.smoothedP2Plane β
          (Critical2DKPZ.blockTime N ρ (K - 1))
          (Critical2DKPZ.blockTime N ρ K) 0 ω - 1| ^ 4) =
          fun _ => (0 : ℝ) from funext fun ω => by
            rw [heq, Critical2DKPZ.Blocks.smoothedP2Plane_eq_one_of_eq]
            norm_num]
      simp
    have hvariance : ProbabilityTheory.variance
        (fun ω : Disorder => Critical2DKPZ.smoothedP2Plane β
          (Critical2DKPZ.blockTime N ρ (K - 1))
          (Critical2DKPZ.blockTime N ρ K) 0 ω) disorderLaw = 0 := by
      rw [hconstant]
      rw [ProbabilityTheory.variance_eq_integral (by fun_prop)]
      simp
    constructor
    · rw [hmoment, hvariance]
      positivity
    · rw [hmoment]
      exact mul_nonneg hCnonneg (by positivity)

end Critical2DKPZ.MomentBounds

end
