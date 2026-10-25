/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.BlockTime
import Critical2DKPZ.PolymerCalculus.Clocks
import Mathlib.Tactic

/-! # Geometric block duration estimates for moment bounds -/

@[expose] public section

open Filter

namespace Critical2DKPZ.MomentBounds

/-- At an interior geometric grid endpoint, the unrounded time is at least
`ρ^(i-1)`. -/
theorem blockTime_unrounded_geometric_scale {N : ℕ} {ρ : ℝ} (hρ : 1 < ρ)
    {i : ℕ} (hi : 1 ≤ i) (hiK : i < Critical2DKPZ.blockCount N ρ) :
    ρ ^ ((i : ℝ) - 1) ≤
      (N : ℝ) * ρ ^ ((i : ℝ) - (Critical2DKPZ.blockCount N ρ : ℝ)) := by
  have hKgeTwo : 2 ≤ Critical2DKPZ.blockCount N ρ := by omega
  have hNne : N ≠ 0 := by
    by_contra h
    have hN : N = 0 := by omega
    subst N
    have hcount : Critical2DKPZ.blockCount 0 ρ = 1 := by
      simp [Critical2DKPZ.blockCount, Real.logb_zero]
    omega
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hNne
  have hNgeOne : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hNne)
  have hlogNonneg : 0 ≤ Real.logb ρ (N : ℝ) := Real.logb_nonneg hρ hNgeOne
  have hfloor :
      ((Critical2DKPZ.blockCount N ρ - 1 : ℕ) : ℝ) ≤ Real.logb ρ (N : ℝ) := by
    have hfloorCast :
        (⌊Real.logb ρ (N : ℝ)⌋₊ : ℝ) ≤ Real.logb ρ (N : ℝ) := Nat.floor_le hlogNonneg
    have hcount : Critical2DKPZ.blockCount N ρ - 1 =
        ⌊Real.logb ρ (N : ℝ)⌋₊ := by
      simp only [Critical2DKPZ.blockCount]
      omega
    simpa [hcount] using hfloorCast
  have hbase :
      ρ ^ ((Critical2DKPZ.blockCount N ρ - 1 : ℕ) : ℝ) ≤ (N : ℝ) :=
    (Real.le_logb_iff_rpow_le hρ hNpos).mp hfloor
  have hpowId :
      ρ ^ ((i : ℝ) - 1) =
        ρ ^ ((Critical2DKPZ.blockCount N ρ - 1 : ℕ) : ℝ) *
          ρ ^ ((i : ℝ) - (Critical2DKPZ.blockCount N ρ : ℝ)) := by
    rw [← Real.rpow_add (by linarith : 0 < ρ)]
    congr 1
    have hKcast :
        ((Critical2DKPZ.blockCount N ρ - 1 : ℕ) : ℝ) +
          ((i : ℝ) - (Critical2DKPZ.blockCount N ρ : ℝ)) = (i : ℝ) - 1 := by
      have hsub : Critical2DKPZ.blockCount N ρ - 1 + 1 =
          Critical2DKPZ.blockCount N ρ := by omega
      have hcast : ((Critical2DKPZ.blockCount N ρ - 1 : ℕ) : ℝ) + 1 =
          (Critical2DKPZ.blockCount N ρ : ℝ) := by exact_mod_cast hsub
      linarith
    linarith
  have hxNonneg : 0 ≤ ρ ^ ((i : ℝ) - (Critical2DKPZ.blockCount N ρ : ℝ)) :=
    Real.rpow_nonneg (by linarith : 0 ≤ ρ) _
  rw [hpowId]
  exact mul_le_mul_of_nonneg_right hbase hxNonneg

/-- At an interior geometric grid endpoint, the rounded time is at least
`ρ^(i-1)`. -/
theorem blockTime_lower_geometric_scale {N : ℕ} {ρ : ℝ} (hρ : 1 < ρ)
    {i : ℕ} (hi : 1 ≤ i) (hiK : i < Critical2DKPZ.blockCount N ρ) :
    ρ ^ ((i : ℝ) - 1) ≤ (Critical2DKPZ.blockTime N ρ i : ℝ) := by
  have htime : (Critical2DKPZ.blockTime N ρ i : ℝ) =
      Critical2DKPZ.evenCeil
        ((N : ℝ) * ρ ^ ((i : ℝ) - (Critical2DKPZ.blockCount N ρ : ℝ))) := by
    simp [Critical2DKPZ.blockTime, Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hi), hiK]
  calc
    ρ ^ ((i : ℝ) - 1) ≤
        (N : ℝ) * ρ ^ ((i : ℝ) - (Critical2DKPZ.blockCount N ρ : ℝ)) :=
      blockTime_unrounded_geometric_scale hρ hi hiK
    _ ≤ (Critical2DKPZ.blockTime N ρ i : ℝ) := by
      rw [htime]
      exact Critical2DKPZ.le_evenCeil _

/-- A geometric block before the terminal block has duration at least its
unrounded scale times `1 - ρ⁻¹`, up to the two-unit rounding error. -/
theorem blockTime_duration_lower_geometric_scale {N : ℕ} {ρ : ℝ} (hρ : 1 < ρ)
    {i : ℕ} (hi : 1 ≤ i) (hiK : i < Critical2DKPZ.blockCount N ρ) :
    (N : ℝ) * ρ ^ ((i : ℝ) - Critical2DKPZ.blockCount N ρ) * (1 - ρ⁻¹) - 2 ≤
      (Critical2DKPZ.blockTime N ρ i -
        Critical2DKPZ.blockTime N ρ (i - 1) : ℕ) := by
  have hNne : N ≠ 0 := by
    by_contra h
    have hN : N = 0 := by omega
    subst N
    have hcount : Critical2DKPZ.blockCount 0 ρ = 1 := by
      simp [Critical2DKPZ.blockCount, Real.logb_zero]
    omega
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hNne
  have hxprev : 0 ≤ (N : ℝ) *
      ρ ^ ((i - 1 : ℕ) - (Critical2DKPZ.blockCount N ρ : ℝ)) := by positivity
  have htimei : (Critical2DKPZ.blockTime N ρ i : ℝ) =
      Critical2DKPZ.evenCeil
        ((N : ℝ) * ρ ^ ((i : ℝ) - (Critical2DKPZ.blockCount N ρ : ℝ))) := by
    simp [Critical2DKPZ.blockTime, Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hi), hiK]
  have hiprevK : i - 1 < Critical2DKPZ.blockCount N ρ := by omega
  have htimeprev : (Critical2DKPZ.blockTime N ρ (i - 1) : ℝ) =
      Critical2DKPZ.evenCeil
        ((N : ℝ) * ρ ^ ((i - 1 : ℕ) - (Critical2DKPZ.blockCount N ρ : ℝ))) ∨
      Critical2DKPZ.blockTime N ρ (i - 1) = 0 := by
    by_cases hprev0 : i - 1 = 0
    · right
      simp [Critical2DKPZ.blockTime, hprev0]
    · left
      have hprevpos : 1 ≤ i - 1 := by omega
      have hprev : i - 1 ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt hprevpos)
      simp [Critical2DKPZ.blockTime, hprev, hiprevK]
  have hprevUpper :
      (Critical2DKPZ.blockTime N ρ (i - 1) : ℝ) <
        (N : ℝ) * ρ ^ ((i - 1 : ℕ) - (Critical2DKPZ.blockCount N ρ : ℝ)) + 2 := by
    rcases htimeprev with htimeprev | hprevzero
    · rw [htimeprev]
      exact Critical2DKPZ.evenCeil_lt_add_two hxprev
    · rw [hprevzero]
      have hx : 0 ≤ (N : ℝ) *
          ρ ^ ((i - 1 : ℕ) - (Critical2DKPZ.blockCount N ρ : ℝ)) := hxprev
      have hxplus : (2 : ℝ) ≤
          (N : ℝ) * ρ ^ ((i - 1 : ℕ) -
            (Critical2DKPZ.blockCount N ρ : ℝ)) + 2 := by
        simpa using add_le_add_right hx (2 : ℝ)
      exact lt_of_lt_of_le (by norm_num) hxplus
  have hExp :
      ((i - 1 : ℕ) : ℝ) - (Critical2DKPZ.blockCount N ρ : ℝ) ≤
        (i : ℝ) - (Critical2DKPZ.blockCount N ρ : ℝ) := by
    have hiCast : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by exact_mod_cast (Nat.sub_add_cancel hi)
    linarith
  have hxmono : (N : ℝ) *
      ρ ^ ((i - 1 : ℕ) - (Critical2DKPZ.blockCount N ρ : ℝ)) ≤
        (N : ℝ) * ρ ^ ((i : ℝ) - (Critical2DKPZ.blockCount N ρ : ℝ)) := by
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hρ.le hExp) (by positivity)
  have hroundmono : Critical2DKPZ.evenCeil
      ((N : ℝ) * ρ ^ ((i - 1 : ℕ) - (Critical2DKPZ.blockCount N ρ : ℝ))) ≤
        Critical2DKPZ.evenCeil
          ((N : ℝ) * ρ ^ ((i : ℝ) - (Critical2DKPZ.blockCount N ρ : ℝ))) :=
    Critical2DKPZ.evenCeil_mono hxmono
  have htimeiNat : Critical2DKPZ.blockTime N ρ i =
      Critical2DKPZ.evenCeil
        ((N : ℝ) * ρ ^ ((i : ℝ) - (Critical2DKPZ.blockCount N ρ : ℝ))) := by
    exact_mod_cast htimei
  have htimeMono : Critical2DKPZ.blockTime N ρ (i - 1) ≤
      Critical2DKPZ.blockTime N ρ i := by
    rcases htimeprev with htimeprev | hprevzero
    · have htimeprevNat : Critical2DKPZ.blockTime N ρ (i - 1) =
          Critical2DKPZ.evenCeil
            ((N : ℝ) * ρ ^ ((i - 1 : ℕ) -
              (Critical2DKPZ.blockCount N ρ : ℝ))) := by
        exact_mod_cast htimeprev
      rw [htimeprevNat, htimeiNat]
      exact hroundmono
    · rw [hprevzero]
      exact Nat.zero_le _
  have hcastSub :
      ((Critical2DKPZ.blockTime N ρ i -
        Critical2DKPZ.blockTime N ρ (i - 1) : ℕ) : ℝ) =
        (Critical2DKPZ.blockTime N ρ i : ℝ) -
          (Critical2DKPZ.blockTime N ρ (i - 1) : ℝ) := by
    rw [Nat.cast_sub htimeMono]
  have hxratio :
      (N : ℝ) * ρ ^ ((i : ℝ) - (Critical2DKPZ.blockCount N ρ : ℝ)) =
        ρ * ((N : ℝ) * ρ ^ ((i - 1 : ℕ) -
          (Critical2DKPZ.blockCount N ρ : ℝ))) := by
    have hpow : ρ ^ ((i : ℝ) - (Critical2DKPZ.blockCount N ρ : ℝ)) =
        ρ ^ (((i - 1 : ℕ) : ℝ) - (Critical2DKPZ.blockCount N ρ : ℝ)) * ρ := by
      have hiCast : ((i - 1 : ℕ) : ℝ) + 1 = (i : ℝ) := by exact_mod_cast (Nat.sub_add_cancel hi)
      rw [show (i : ℝ) - (Critical2DKPZ.blockCount N ρ : ℝ) =
        (((i - 1 : ℕ) : ℝ) - (Critical2DKPZ.blockCount N ρ : ℝ)) + 1 by linarith,
        Real.rpow_add (by linarith : 0 < ρ), Real.rpow_one]
    rw [hpow]
    ring
  have hgap :
      (N : ℝ) * ρ ^ ((i : ℝ) - (Critical2DKPZ.blockCount N ρ : ℝ)) -
        (N : ℝ) * ρ ^ ((i - 1 : ℕ) - (Critical2DKPZ.blockCount N ρ : ℝ)) =
      (N : ℝ) * ρ ^ ((i : ℝ) - (Critical2DKPZ.blockCount N ρ : ℝ)) * (1 - ρ⁻¹) := by
    rw [hxratio]
    field_simp [ne_of_gt (by linarith : 0 < ρ)]
  rw [hcastSub, htimei]
  have htimeLower := Critical2DKPZ.le_evenCeil
    ((N : ℝ) * ρ ^ ((i : ℝ) - (Critical2DKPZ.blockCount N ρ : ℝ)))
  linarith [htimeLower, hprevUpper, hgap]

/-- On a ratio range bounded away from one, a bounded interior block duration
forces its endpoint to remain in a bounded initial time window. -/
theorem blockTime_endpoint_lt_of_duration_le (L₀ : ℕ) {N i : ℕ}
    {ρ₀ ρ : ℝ} (hρ₀ : 1 < ρ₀) (hρ : ρ₀ ≤ ρ)
    (hi : 1 ≤ i) (hiK : i < Critical2DKPZ.blockCount N ρ)
    (hd : Critical2DKPZ.blockTime N ρ i -
      Critical2DKPZ.blockTime N ρ (i - 1) ≤ L₀) :
    (Critical2DKPZ.blockTime N ρ i : ℝ) <
      ((L₀ : ℝ) + 2) / (1 - ρ₀⁻¹) + 2 := by
  have hρ1 : 1 < ρ := lt_of_lt_of_le hρ₀ hρ
  have hρ₀pos : 0 < ρ₀ := by linarith
  have hρpos : 0 < ρ := by linarith
  have hρinv : ρ⁻¹ ≤ ρ₀⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hρ₀pos hρ
  have hden0 : 0 < 1 - ρ₀⁻¹ := by
    have hInvLt : ρ₀⁻¹ < 1 := (inv_lt_one₀ hρ₀pos).2 hρ₀
    linarith
  have hden : 1 - ρ₀⁻¹ ≤ 1 - ρ⁻¹ := by linarith
  have hduration := blockTime_duration_lower_geometric_scale hρ1 hi hiK
  have hdReal : (Critical2DKPZ.blockTime N ρ i -
      Critical2DKPZ.blockTime N ρ (i - 1) : ℕ) ≤ (L₀ : ℝ) := by
    exact_mod_cast hd
  let scale : ℝ := (N : ℝ) *
    ρ ^ ((i : ℝ) - (Critical2DKPZ.blockCount N ρ : ℝ))
  have hscale0 : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have hscaleBound : scale ≤ ((L₀ : ℝ) + 2) / (1 - ρ₀⁻¹) := by
    apply (le_div_iff₀ hden0).2
    have hraw := hduration.trans hdReal
    dsimp [scale] at hraw ⊢
    calc
      (N : ℝ) * ρ ^ ((i : ℝ) - (Critical2DKPZ.blockCount N ρ : ℝ)) *
          (1 - ρ₀⁻¹) ≤
        (N : ℝ) * ρ ^ ((i : ℝ) - (Critical2DKPZ.blockCount N ρ : ℝ)) *
          (1 - ρ⁻¹) :=
        mul_le_mul_of_nonneg_left hden hscale0
      _ ≤ (L₀ : ℝ) + 2 := by linarith
  have htime : (Critical2DKPZ.blockTime N ρ i : ℝ) =
      Critical2DKPZ.evenCeil scale := by
    simp [scale, Critical2DKPZ.blockTime,
      Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hi), hiK]
  have htimeUpper : (Critical2DKPZ.blockTime N ρ i : ℝ) < scale + 2 := by
    rw [htime]
    exact Critical2DKPZ.evenCeil_lt_add_two hscale0
  exact htimeUpper.trans_le (by nlinarith [add_le_add_right hscaleBound (2 : ℝ)])

/-- A horizon at least as large as the ratio has at least two geometric blocks. -/
theorem blockCount_ge_two_of_ratio_le_horizon {N : ℕ} {ρ : ℝ}
    (hρ : 1 < ρ) (hρN : ρ ≤ (N : ℝ)) :
    2 ≤ Critical2DKPZ.blockCount N ρ := by
  have hNpos : 0 < (N : ℝ) := lt_of_lt_of_le (by linarith) hρN
  have hlog : 1 ≤ Real.logb ρ (N : ℝ) := by
    apply (Real.le_logb_iff_rpow_le hρ hNpos).2
    simpa only [Real.rpow_one] using hρN
  have hfloor : 1 ≤ ⌊Real.logb ρ (N : ℝ)⌋₊ := by
    rw [Nat.le_floor_iff (by linarith : 0 ≤ Real.logb ρ (N : ℝ))]
    exact_mod_cast hlog
  unfold Critical2DKPZ.blockCount
  omega

/-- A block count of at least two is equivalent to fitting one geometric ratio
below the horizon; this direction is useful for the first block. -/
theorem ratio_le_horizon_of_blockCount_ge_two {N : ℕ} {ρ : ℝ}
    (hρ : 1 < ρ) (hK : 2 ≤ Critical2DKPZ.blockCount N ρ) :
    ρ ≤ (N : ℝ) := by
  have hNne : N ≠ 0 := by
    by_contra h
    have hN : N = 0 := by omega
    subst N
    have hcount : Critical2DKPZ.blockCount 0 ρ = 1 := by
      simp [Critical2DKPZ.blockCount, Real.logb_zero]
    omega
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hNne
  have hNgeOne : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hNne)
  have hlogNonneg : 0 ≤ Real.logb ρ (N : ℝ) := Real.logb_nonneg hρ hNgeOne
  have hfloorOne : 1 ≤ ⌊Real.logb ρ (N : ℝ)⌋₊ := by
    have := hK
    unfold Critical2DKPZ.blockCount at this
    omega
  have hlogOne : 1 ≤ Real.logb ρ (N : ℝ) := by
    calc
      1 ≤ (⌊Real.logb ρ (N : ℝ)⌋₊ : ℝ) := by exact_mod_cast hfloorOne
      _ ≤ Real.logb ρ (N : ℝ) := Nat.floor_le hlogNonneg
  have hpow : ρ ^ (1 : ℝ) ≤ (N : ℝ) :=
    (Real.le_logb_iff_rpow_le hρ hNpos).mp hlogOne
  simpa only [Real.rpow_one] using hpow

private theorem blockTime_le_horizon_of_roundBound {N : ℕ} {ρ : ℝ}
    (hρ : 1 < ρ)
    (hround : Critical2DKPZ.evenCeil ((N : ℝ) * ρ⁻¹) ≤ N) (i : ℕ) :
    Critical2DKPZ.blockTime N ρ i ≤ N := by
  by_cases hi0 : i = 0
  · simp [Critical2DKPZ.blockTime, hi0]
  by_cases hiK : i < Critical2DKPZ.blockCount N ρ
  · have hcast : (i : ℝ) - (Critical2DKPZ.blockCount N ρ : ℝ) ≤ -1 := by
      have hnat : i + 1 ≤ Critical2DKPZ.blockCount N ρ := Nat.succ_le_of_lt hiK
      have hreal : (i : ℝ) + 1 ≤ (Critical2DKPZ.blockCount N ρ : ℝ) := by
        exact_mod_cast hnat
      linarith
    have hpow := Real.rpow_le_rpow_of_exponent_le hρ.le hcast
    rw [Real.rpow_neg_one] at hpow
    rw [Critical2DKPZ.blockTime, ite_eq_right hi0, ite_eq_left hiK]
    exact le_trans (Critical2DKPZ.evenCeil_mono
      (mul_le_mul_of_nonneg_left hpow (by positivity))) hround
  · rw [Critical2DKPZ.blockTime, ite_eq_right hi0, ite_eq_right hiK]

/-- A single large-horizon threshold makes the geometric block clock
monotone for every ratio bounded below by `ρ₀ > 1`. -/
theorem blockTime_monotone_of_large_horizon {N : ℕ} {ρ₀ ρ : ℝ}
    (hρ₀ : 1 < ρ₀) (hρ₀ρ : ρ₀ ≤ ρ)
    (hN : ⌈2 * ρ₀ / (ρ₀ - 1)⌉₊ ≤ N) :
    Monotone (Critical2DKPZ.blockTime N ρ) := by
  have hρ : 1 < ρ := lt_of_lt_of_le hρ₀ hρ₀ρ
  have hρpos : 0 < ρ := by linarith
  have hρ0den : 0 < ρ₀ - 1 := by linarith
  have hρden : 0 < ρ - 1 := by linarith
  have hratio : 2 * ρ / (ρ - 1) ≤ 2 * ρ₀ / (ρ₀ - 1) := by
    rw [div_le_div_iff₀ hρden hρ0den]
    nlinarith
  have hthreshold : 2 * ρ₀ / (ρ₀ - 1) ≤ (N : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hratioN : 2 * ρ / (ρ - 1) ≤ (N : ℝ) := hratio.trans hthreshold
  have hmul : 2 * ρ ≤ (N : ℝ) * (ρ - 1) := (div_le_iff₀ hρden).mp hratioN
  have hdiv : (N : ℝ) / ρ + 2 ≤ N := by
    have h : (N : ℝ) / ρ ≤ (N : ℝ) - 2 :=
      (div_le_iff₀ hρpos).2 (by nlinarith [hmul])
    linarith
  have hlt : (Critical2DKPZ.evenCeil ((N : ℝ) * ρ⁻¹) : ℝ) < N := by
    calc
      (Critical2DKPZ.evenCeil ((N : ℝ) * ρ⁻¹) : ℝ) <
          (N : ℝ) * ρ⁻¹ + 2 :=
        Critical2DKPZ.evenCeil_lt_add_two (by positivity)
      _ = (N : ℝ) / ρ + 2 := by rw [div_eq_mul_inv]
      _ ≤ N := hdiv
  have hnat : Critical2DKPZ.evenCeil ((N : ℝ) * ρ⁻¹) < N := by exact_mod_cast hlt
  have hround : Critical2DKPZ.evenCeil ((N : ℝ) * ρ⁻¹) ≤ N := hnat.le
  have hKpos : 1 ≤ Critical2DKPZ.blockCount N ρ := by
    unfold Critical2DKPZ.blockCount
    omega
  intro i j hij
  by_cases hjK : j < Critical2DKPZ.blockCount N ρ
  · by_cases hi0 : i = 0
    · simp [Critical2DKPZ.blockTime, hi0]
    · have hj0 : j ≠ 0 := by omega
      have hiK : i < Critical2DKPZ.blockCount N ρ := lt_of_le_of_lt hij hjK
      have htimei : Critical2DKPZ.blockTime N ρ i = Critical2DKPZ.evenCeil
          ((N : ℝ) * ρ ^ ((i : ℝ) - Critical2DKPZ.blockCount N ρ)) := by
        simp [Critical2DKPZ.blockTime, hi0, hiK]
      have htimej : Critical2DKPZ.blockTime N ρ j = Critical2DKPZ.evenCeil
          ((N : ℝ) * ρ ^ ((j : ℝ) - Critical2DKPZ.blockCount N ρ)) := by
        simp [Critical2DKPZ.blockTime, hj0, hjK]
      rw [htimei, htimej]
      apply Critical2DKPZ.evenCeil_mono
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (N : ℝ))
      apply Real.rpow_le_rpow_of_exponent_le hρ.le
      have hcast : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      exact sub_le_sub_right hcast _
  · have hiBound := blockTime_le_horizon_of_roundBound hρ hround i
    have hj0 : j ≠ 0 := by omega
    have htimej : Critical2DKPZ.blockTime N ρ j = N := by
      simp [Critical2DKPZ.blockTime, hj0, hjK]
    rw [htimej]
    exact hiBound

/-- When the ratio fits below the horizon, the first geometric endpoint is
bounded by one ratio plus the even-ceiling error. -/
theorem blockTime_first_endpoint_lt {N : ℕ} {ρ : ℝ}
    (hρ : 1 < ρ) (hρN : ρ ≤ (N : ℝ)) :
    (Critical2DKPZ.blockTime N ρ 1 : ℝ) < ρ + 2 := by
  have hK := blockCount_ge_two_of_ratio_le_horizon hρ hρN
  have hNpos : 0 < (N : ℝ) := lt_of_lt_of_le (by linarith) hρN
  let K := Critical2DKPZ.blockCount N ρ
  have hloglt : Real.logb ρ (N : ℝ) < (K : ℝ) := by
    simpa [K, Critical2DKPZ.blockCount] using
      (Nat.lt_floor_add_one (Real.logb ρ (N : ℝ)))
  have hNlt : (N : ℝ) < ρ ^ (K : ℝ) :=
    (Real.logb_lt_iff_lt_rpow hρ hNpos).mp hloglt
  let x := (N : ℝ) * ρ ^ ((1 : ℝ) - (K : ℝ))
  have hxPos : 0 < ρ ^ ((1 : ℝ) - (K : ℝ)) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hxUpper : x < ρ := by
    have hmul := mul_lt_mul_of_pos_right hNlt hxPos
    dsimp [x]
    calc
      (N : ℝ) * ρ ^ ((1 : ℝ) - (K : ℝ)) <
          ρ ^ (K : ℝ) * ρ ^ ((1 : ℝ) - (K : ℝ)) := hmul
      _ = ρ := by
        rw [← Real.rpow_add (by linarith : 0 < ρ)]
        have hexp : (K : ℝ) + ((1 : ℝ) - (K : ℝ)) = 1 := by ring
        rw [hexp, Real.rpow_one]
  have htime : (Critical2DKPZ.blockTime N ρ 1 : ℝ) =
      Critical2DKPZ.evenCeil x := by
    have h1K : 1 < Critical2DKPZ.blockCount N ρ := by omega
    dsimp [x, K]
    simp [Critical2DKPZ.blockTime, h1K]
  calc
    (Critical2DKPZ.blockTime N ρ 1 : ℝ) < x + 2 := by
      rw [htime]
      exact Critical2DKPZ.evenCeil_lt_add_two (by positivity)
    _ < ρ + 2 := by nlinarith [hxUpper]

/-- The horizon is strictly below the ratio raised to the block count. -/
theorem horizon_lt_ratio_pow_blockCount {N : ℕ} {ρ : ℝ}
    (hρ : 1 < ρ) (hN : 0 < (N : ℝ)) :
    (N : ℝ) < ρ ^ (Critical2DKPZ.blockCount N ρ : ℝ) := by
  have hloglt : Real.logb ρ (N : ℝ) < (Critical2DKPZ.blockCount N ρ : ℝ) := by
    simpa only [Critical2DKPZ.blockCount, Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (Real.logb ρ (N : ℝ)))
  exact (Real.logb_lt_iff_lt_rpow hρ hN).mp hloglt

/-- The last endpoint ratio is at most `ρ²`, uniformly in the horizon. -/
theorem blockTime_final_endpoint_ratio_le {N : ℕ} {ρ : ℝ}
    (hρ : 1 < ρ) (hK : 2 ≤ Critical2DKPZ.blockCount N ρ) :
    (((max N 1 : ℕ) : ℝ) /
      ((max (Critical2DKPZ.blockTime N ρ
        (Critical2DKPZ.blockCount N ρ - 1)) 1 : ℕ) : ℝ)) ≤ ρ ^ (2 : ℝ) := by
  have hρN := ratio_le_horizon_of_blockCount_ge_two hρ hK
  have hNone : 1 ≤ N := by exact_mod_cast (show (1 : ℝ) ≤ (N : ℝ) by linarith)
  let K := Critical2DKPZ.blockCount N ρ
  let j := K - 1
  let s := Critical2DKPZ.blockTime N ρ j
  have hj : 1 ≤ j := by dsimp [j, K]; omega
  have hjK : j < K := by dsimp [j, K]; omega
  have hsLower := blockTime_lower_geometric_scale hρ hj (by simpa [K] using hjK)
  have hpowOne : 1 ≤ ρ ^ ((j : ℝ) - 1) := by
    apply Real.one_le_rpow hρ.le
    have hjCast : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    linarith
  have hsOneReal : (1 : ℝ) ≤ (s : ℝ) := by
    dsimp [s]
    exact hpowOne.trans hsLower
  have hsOne : 1 ≤ s := by exact_mod_cast hsOneReal
  have hpowEq : ρ ^ (K : ℝ) = ρ ^ ((j : ℝ) - 1) * ρ ^ (2 : ℝ) := by
    have hKpos : 1 ≤ K := by omega
    have hKnat : j + 1 = K := by dsimp [j]; exact Nat.sub_add_cancel hKpos
    have hKcast : (j : ℝ) + 1 = (K : ℝ) := by exact_mod_cast hKnat
    calc
      ρ ^ (K : ℝ) = ρ ^ ((j : ℝ) + 1) := by rw [← hKcast]
      _ = ρ ^ (((j : ℝ) - 1) + 2) := by congr 1; ring
      _ = ρ ^ ((j : ℝ) - 1) * ρ ^ (2 : ℝ) := by
        rw [Real.rpow_add (by linarith : 0 < ρ)]
  have hNlt := horizon_lt_ratio_pow_blockCount hρ (by positivity : 0 < (N : ℝ))
  have hNltK : (N : ℝ) < ρ ^ (K : ℝ) := by simpa [K] using hNlt
  have hNbound : (N : ℝ) ≤ ρ ^ (2 : ℝ) * (s : ℝ) := by
    calc
      (N : ℝ) ≤ ρ ^ (K : ℝ) := hNltK.le
      _ = ρ ^ ((j : ℝ) - 1) * ρ ^ (2 : ℝ) := hpowEq
      _ ≤ (s : ℝ) * ρ ^ (2 : ℝ) :=
        mul_le_mul_of_nonneg_right hsLower
          (Real.rpow_nonneg (le_of_lt (by linarith : 0 < ρ)) 2)
      _ = ρ ^ (2 : ℝ) * (s : ℝ) := by ring
  have hmaxN : max N 1 = N := max_eq_left hNone
  have hmaxs : max s 1 = s := max_eq_left hsOne
  rw [hmaxN, hmaxs]
  apply (div_le_iff₀ (by exact_mod_cast (show 0 < s by omega))).2
  simpa [s, j, K] using hNbound

/-- The terminal block has geometric duration when its unrounded gap is at least two. -/
theorem blockTime_final_duration_lower_geometric_scale {N : ℕ} {ρ : ℝ}
    (hρ : 1 < ρ) (hK : 2 ≤ Critical2DKPZ.blockCount N ρ)
    (hgap : 2 ≤ (N : ℝ) * (1 - ρ⁻¹)) :
    (N : ℝ) * (1 - ρ⁻¹) - 2 ≤
      (Critical2DKPZ.blockTime N ρ (Critical2DKPZ.blockCount N ρ) -
        Critical2DKPZ.blockTime N ρ (Critical2DKPZ.blockCount N ρ - 1) : ℕ) := by
  let K := Critical2DKPZ.blockCount N ρ
  have hKpos : 0 < K := by omega
  have hprevpos : 1 ≤ K - 1 := by dsimp [K]; omega
  have hprevlt : K - 1 < K := by dsimp [K]; omega
  have hprev : K - 1 ≠ 0 := by omega
  have hprevTime : (Critical2DKPZ.blockTime N ρ (K - 1) : ℝ) =
      Critical2DKPZ.evenCeil ((N : ℝ) * ρ⁻¹) := by
    have hcastSub : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ K)]
      norm_num
    simp [Critical2DKPZ.blockTime, K, hprev, hprevlt]
    rw [hcastSub]
    congr 1
    rw [show ((K : ℝ) - 1) - (K : ℝ) = -1 by ring, Real.rpow_neg_one]
  have hprevUpper : (Critical2DKPZ.blockTime N ρ (K - 1) : ℝ) <
      (N : ℝ) * ρ⁻¹ + 2 := by
    rw [hprevTime]
    have harg : 0 ≤ (N : ℝ) * ρ⁻¹ := by positivity
    exact Critical2DKPZ.evenCeil_lt_add_two harg
  have hprevLeN : Critical2DKPZ.blockTime N ρ (K - 1) ≤ N := by
    have hreal : (Critical2DKPZ.blockTime N ρ (K - 1) : ℝ) ≤ (N : ℝ) := by
      have hgap' := hgap
      have hidentity : (N : ℝ) = (N : ℝ) * (1 - ρ⁻¹) +
          (N : ℝ) * ρ⁻¹ := by ring
      rw [hidentity]
      have htwo : (2 : ℝ) ≤ (N : ℝ) * (1 - ρ⁻¹) := hgap'
      linarith [hprevUpper]
    exact_mod_cast hreal
  have hfinalTime : Critical2DKPZ.blockTime N ρ K = N := by
    simp [Critical2DKPZ.blockTime, K, Nat.ne_of_gt hKpos]
  have hcastSub :
      ((Critical2DKPZ.blockTime N ρ K -
        Critical2DKPZ.blockTime N ρ (K - 1) : ℕ) : ℝ) =
      (Critical2DKPZ.blockTime N ρ K : ℝ) -
        (Critical2DKPZ.blockTime N ρ (K - 1) : ℝ) := by
    rw [hfinalTime, Nat.cast_sub hprevLeN]
  rw [hcastSub, hfinalTime, hprevTime]
  have hiden : (N : ℝ) - ((N : ℝ) * ρ⁻¹ + 2) =
      (N : ℝ) * (1 - ρ⁻¹) - 2 := by ring
  linarith [hprevUpper, hiden]

end Critical2DKPZ.MomentBounds

end
