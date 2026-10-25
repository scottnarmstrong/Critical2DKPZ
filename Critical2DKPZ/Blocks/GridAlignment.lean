/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.Core
public import Critical2DKPZ.Definitions.BlockCount
public import Critical2DKPZ.Definitions.BlockTime
public import Critical2DKPZ.PolymerCalculus.Clocks
import Mathlib.Tactic

/-!
# Geometric grid alignment for the block expansion
-/

@[expose] public section

open Filter

namespace Critical2DKPZ.Blocks

private theorem grid_log_bounds {δ ρ : ℝ} (hρ : 1 < ρ) (hδ : 0 < δ)
    (hδρ : δ ≤ ρ⁻¹ ^ 2) :
    0 < Real.log ρ ∧ Real.log δ < 0 ∧ 2 * Real.log ρ ≤ |Real.log δ| := by
  have hρpos : 0 < ρ := by linarith
  have hinvpos : 0 < ρ⁻¹ := inv_pos.mpr hρpos
  have hinvlt : ρ⁻¹ < 1 := (inv_lt_one₀ hρpos).2 hρ
  have hpowlt : ρ⁻¹ ^ 2 < 1 := by
    calc
      ρ⁻¹ ^ 2 = ρ⁻¹ * ρ⁻¹ := by ring
      _ < 1 * ρ⁻¹ := mul_lt_mul_of_pos_right hinvlt hinvpos
      _ < 1 := by simpa using hinvlt
  have hδlt : δ < 1 := lt_of_le_of_lt hδρ hpowlt
  have hlogρ : 0 < Real.log ρ := Real.log_pos hρ
  have hlogδ : Real.log δ < 0 := Real.log_neg hδ hδlt
  have hlogPower : Real.log (ρ⁻¹ ^ 2) = -2 * Real.log ρ := by
    rw [Real.log_pow, Real.log_inv]
    ring
  have hlogle : Real.log δ ≤ -2 * Real.log ρ := by
    calc
      Real.log δ ≤ Real.log (ρ⁻¹ ^ 2) := Real.log_le_log hδ hδρ
      _ = -2 * Real.log ρ := hlogPower
  refine ⟨hlogρ, hlogδ, ?_⟩
  rw [abs_of_neg hlogδ]
  linarith

/-- The floor grid length lies between half its real value and that value. -/
theorem gridBlocks_bounds {δ ρ : ℝ} (hρ : 1 < ρ) (hδ : 0 < δ)
    (hδρ : δ ≤ ρ⁻¹ ^ 2) :
    1 ≤ gridBlocks δ ρ ∧ |Real.log δ| / (4 * Real.log ρ) ≤ gridBlocks δ ρ ∧
      (gridBlocks δ ρ : ℝ) ≤ |Real.log δ| / (2 * Real.log ρ) := by
  obtain ⟨hlogρ, hlogδ, hlogscale⟩ := grid_log_bounds hρ hδ hδρ
  let x := |Real.log δ| / (2 * Real.log ρ)
  have hx : 1 ≤ x := by
    dsimp [x]
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log ρ)).2
    nlinarith [hlogscale]
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hJ : 1 ≤ gridBlocks δ ρ := by
    unfold gridBlocks
    rw [Nat.le_floor_iff hx0]
    exact_mod_cast hx
  have hupper : (gridBlocks δ ρ : ℝ) ≤ x := by
    unfold gridBlocks
    exact Nat.floor_le hx0
  have hlower : x / 2 ≤ (gridBlocks δ ρ : ℝ) := by
    by_cases hx2 : x < 2
    · calc
        x / 2 ≤ 1 := by linarith
        _ ≤ (gridBlocks δ ρ : ℝ) := by exact_mod_cast hJ
    · have hfloor : x < (gridBlocks δ ρ : ℝ) + 1 := by
        simpa [gridBlocks, x] using (Nat.lt_floor_add_one x)
      linarith
  have hratio : x / 2 = |Real.log δ| / (4 * Real.log ρ) := by
    dsimp [x]
    field_simp [ne_of_gt hlogρ]; ring
  refine ⟨hJ, ?_, ?_⟩
  · rw [← hratio]
    exact hlower
  · simpa [x] using hupper

/-- The adjusted ratio is between the nominal ratio and its square. -/
theorem gridRatio_mem {δ ρ : ℝ} (hρ : 1 < ρ) (hδ : 0 < δ)
    (hδρ : δ ≤ ρ⁻¹ ^ 2) : gridRatio δ ρ ∈ Set.Icc ρ (ρ ^ 2) := by
  obtain ⟨hlogρ, hlogδ, hlogscale⟩ := grid_log_bounds hρ hδ hδρ
  obtain ⟨hJnat, hJlower, hJupper⟩ := gridBlocks_bounds hρ hδ hδρ
  have hJ : 0 < (gridBlocks δ ρ : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hJnat)
  have hlow : Real.log ρ ≤ |Real.log δ| / (2 * gridBlocks δ ρ) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * (gridBlocks δ ρ : ℝ))).2
    have h := (le_div_iff₀ (by positivity : 0 < 2 * Real.log ρ)).mp hJupper
    nlinarith [h]
  have hhigh : |Real.log δ| / (2 * gridBlocks δ ρ) ≤ 2 * Real.log ρ := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (gridBlocks δ ρ : ℝ))).2
    have h := (div_le_iff₀ (by positivity : 0 < 4 * Real.log ρ)).mp hJlower
    nlinarith [h]
  have hgrid : gridRatio δ ρ =
      Real.exp (|Real.log δ| / (2 * gridBlocks δ ρ)) := by
    unfold gridRatio
    rw [Real.rpow_def_of_pos hδ, abs_of_neg hlogδ]
    congr 1
    field_simp [ne_of_gt hJ]
  rw [hgrid]
  constructor
  · calc
      ρ = Real.exp (Real.log ρ) := (Real.exp_log (by linarith : 0 < ρ)).symm
      _ ≤ Real.exp (|Real.log δ| / (2 * gridBlocks δ ρ)) := Real.exp_le_exp.mpr hlow
  · calc
      Real.exp (|Real.log δ| / (2 * gridBlocks δ ρ)) ≤ Real.exp (2 * Real.log ρ) :=
        Real.exp_le_exp.mpr hhigh
      _ = ρ ^ 2 := by rw [show (2 : ℝ) * Real.log ρ = Real.log ρ + Real.log ρ by ring,
        Real.exp_add, Real.exp_log (by linarith : 0 < ρ)]; ring

/-- The number of geometric blocks diverges as the lattice horizon tends to infinity. -/
theorem blockCount_tendsto_atTop {ρ : ℝ} (hρ : 1 < ρ) :
    Tendsto (fun N : ℕ => blockCount N ρ) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro m
  refine ⟨⌈ρ ^ m⌉₊, ?_⟩
  intro N hN
  have hceil : (ρ ^ m : ℝ) ≤ (⌈ρ ^ m⌉₊ : ℝ) := Nat.le_ceil _
  have hceilN : (⌈ρ ^ m⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hbase : 1 ≤ ρ ^ (m : ℝ) := Real.one_le_rpow hρ.le (by positivity)
  have hpow : ρ ^ (m : ℝ) ≤ (N : ℝ) := by
    rw [Real.rpow_natCast]
    exact hceil.trans hceilN
  have hNpos : 0 < (N : ℝ) := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hbase) hpow
  have hNone : 1 ≤ (N : ℝ) := (le_trans hbase hpow)
  have hlog : (m : ℝ) ≤ Real.logb ρ (N : ℝ) :=
    (Real.le_logb_iff_rpow_le hρ hNpos).2 hpow
  have hlog0 : 0 ≤ Real.logb ρ (N : ℝ) := Real.logb_nonneg hρ hNone
  have hfloor : m ≤ ⌊Real.logb ρ (N : ℝ)⌋₊ := by
    rw [Nat.le_floor_iff hlog0]
    exact hlog
  unfold blockCount
  omega

/-- The adjusted grid ratio raised to minus twice the grid length is the cutoff. -/
theorem gridRatio_pow_double (δ ρ : ℝ) (hδ : 0 < δ)
    (hJ : 0 < (gridBlocks δ ρ : ℝ)) :
    gridRatio δ ρ ^ (-(2 * (gridBlocks δ ρ : ℝ))) = δ := by
  unfold gridRatio
  rw [← Real.rpow_mul (le_of_lt hδ)]
  rw [show (-(1 : ℝ) / (2 * (gridBlocks δ ρ : ℝ))) *
      (-(2 * (gridBlocks δ ρ : ℝ))) = 1 by
        field_simp [ne_of_gt hJ]]
  exact Real.rpow_one δ

private theorem gridRatio_pow_single (δ ρ : ℝ) (hδ : 0 < δ)
    (hJ : 0 < (gridBlocks δ ρ : ℝ)) :
    gridRatio δ ρ ^ (-(gridBlocks δ ρ : ℝ)) = Real.sqrt δ := by
  unfold gridRatio
  rw [← Real.rpow_mul (le_of_lt hδ)]
  rw [show (-(1 : ℝ) / (2 * (gridBlocks δ ρ : ℝ))) *
      (-(gridBlocks δ ρ : ℝ)) = 1 / 2 by
        field_simp [ne_of_gt hJ]]
  exact (Real.sqrt_eq_rpow δ).symm

private theorem blockTime_gridIndex_left (N : ℕ) (δ ρ : ℝ)
    (hδ : 0 < δ) (hJnat : 1 ≤ gridBlocks δ ρ)
    (hK : 2 * gridBlocks δ ρ < blockCount N (gridRatio δ ρ)) :
    blockTime N (gridRatio δ ρ) (blockCount N (gridRatio δ ρ) -
      2 * gridBlocks δ ρ) = evenCeil (δ * N) := by
  let J := gridBlocks δ ρ
  let K := blockCount N (gridRatio δ ρ)
  have hJpos : 0 < (J : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hJnat)
  have hstart : 1 ≤ K - 2 * J := by dsimp [K, J]; omega
  have hstop : K - 2 * J < K := by dsimp [K, J]; omega
  have hcast : ((K - 2 * J : ℕ) : ℝ) - (K : ℝ) = -(2 * (J : ℝ)) := by
    have hle : 2 * J ≤ K := by dsimp [K, J]; omega
    rw [Nat.cast_sub hle]
    push_cast
    ring
  rw [blockTime, ite_eq_right (Nat.ne_of_gt hstart), ite_eq_left hstop, hcast]
  rw [gridRatio_pow_double δ ρ hδ hJpos]
  congr 1
  ring

private theorem blockTime_gridIndex_right (N : ℕ) (δ ρ : ℝ)
    (hδ : 0 < δ) (hJnat : 1 ≤ gridBlocks δ ρ)
    (hK : 2 * gridBlocks δ ρ < blockCount N (gridRatio δ ρ)) :
    blockTime N (gridRatio δ ρ) (blockCount N (gridRatio δ ρ) -
      gridBlocks δ ρ) = evenCeil (Real.sqrt δ * N) := by
  let J := gridBlocks δ ρ
  let K := blockCount N (gridRatio δ ρ)
  have hJpos : 0 < (J : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hJnat)
  have hstart : 1 ≤ K - J := by dsimp [K, J]; omega
  have hstop : K - J < K := by dsimp [K, J]; omega
  have hcast : ((K - J : ℕ) : ℝ) - (K : ℝ) = -(J : ℝ) := by
    have hle : J ≤ K := by dsimp [K, J]; omega
    rw [Nat.cast_sub hle]
    ring
  rw [blockTime, ite_eq_right (Nat.ne_of_gt hstart), ite_eq_left hstop, hcast]
  rw [gridRatio_pow_single δ ρ hδ hJpos]
  congr 1
  ring

/-- The adjusted grid places its two selected endpoints exactly at the requested scales. -/
theorem blockTime_gridRatio {δ ρ : ℝ} (hρ : 1 < ρ) (hδ : 0 < δ)
    (hδρ : δ ≤ ρ⁻¹ ^ 2) :
    ∀ᶠ N : ℕ in atTop, 2 * gridBlocks δ ρ < blockCount N (gridRatio δ ρ) ∧
      blockTime N (gridRatio δ ρ) (blockCount N (gridRatio δ ρ) -
        2 * gridBlocks δ ρ) = evenCeil (δ * N) ∧
      blockTime N (gridRatio δ ρ) (blockCount N (gridRatio δ ρ) -
        gridBlocks δ ρ) = evenCeil (Real.sqrt δ * N) := by
  have hgrid := gridRatio_mem hρ hδ hδρ
  have hγ : 1 < gridRatio δ ρ := lt_of_lt_of_le hρ hgrid.1
  have hJ := gridBlocks_bounds hρ hδ hδρ
  have hJnat := hJ.1
  have hK := (blockCount_tendsto_atTop hγ).eventually_gt_atTop (2 * gridBlocks δ ρ)
  filter_upwards [hK] with N hN
  exact ⟨hN, blockTime_gridIndex_left N δ ρ hδ hJnat hN,
    blockTime_gridIndex_right N δ ρ hδ hJnat hN⟩

private theorem evenCeil_scale_inv_le {ρ : ℝ} (hρ : 1 < ρ) (N : ℕ)
    (hN : ⌈2 * ρ / (ρ - 1)⌉₊ ≤ N) : evenCeil ((N : ℝ) * ρ⁻¹) ≤ N := by
  have hρpos : 0 < ρ := by linarith
  have hden : 0 < ρ - 1 := by linarith
  have hbound : 2 * ρ / (ρ - 1) ≤ (N : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hmul : 2 * ρ ≤ (N : ℝ) * (ρ - 1) := (div_le_iff₀ hden).mp hbound
  have hdiv : (N : ℝ) / ρ + 2 ≤ N := by
    have h : (N : ℝ) / ρ ≤ (N : ℝ) - 2 :=
      (div_le_iff₀ hρpos).2 (by nlinarith [hmul])
    linarith
  have hlt : (evenCeil ((N : ℝ) * ρ⁻¹) : ℝ) < N := by
    calc
      (evenCeil ((N : ℝ) * ρ⁻¹) : ℝ) < (N : ℝ) * ρ⁻¹ + 2 :=
        evenCeil_lt_add_two (by positivity)
      _ = (N : ℝ) / ρ + 2 := by rw [div_eq_mul_inv]
      _ ≤ N := hdiv
  have hnat : evenCeil ((N : ℝ) * ρ⁻¹) < N := by exact_mod_cast hlt
  exact hnat.le

private theorem blockTime_le_horizon {ρ : ℝ} (hρ : 1 < ρ) (N : ℕ)
    (hround : evenCeil ((N : ℝ) * ρ⁻¹) ≤ N) (i : ℕ) :
    blockTime N ρ i ≤ N := by
  by_cases hi0 : i = 0
  · simp [blockTime, hi0]
  by_cases hiK : i < blockCount N ρ
  · have hcast : (i : ℝ) - (blockCount N ρ : ℝ) ≤ -1 := by
      have hnat : i + 1 ≤ blockCount N ρ := Nat.succ_le_of_lt hiK
      have hreal : (i : ℝ) + 1 ≤ (blockCount N ρ : ℝ) := by exact_mod_cast hnat
      linarith
    have hpow := Real.rpow_le_rpow_of_exponent_le hρ.le hcast
    rw [Real.rpow_neg_one] at hpow
    rw [blockTime, ite_eq_right hi0, ite_eq_left hiK]
    exact le_trans (evenCeil_mono (mul_le_mul_of_nonneg_left hpow (by positivity))) hround
  · rw [blockTime, ite_eq_right hi0, ite_eq_right hiK]

/-- For all sufficiently large horizons, the geometric block clock is monotone. -/
theorem blockTime_monotone {ρ : ℝ} (hρ : 1 < ρ) :
    ∀ᶠ N : ℕ in atTop, Monotone (blockTime N ρ) := by
  let C := ⌈2 * ρ / (ρ - 1)⌉₊
  filter_upwards [eventually_ge_atTop C] with N hN
  have hround := evenCeil_scale_inv_le hρ N (by simpa [C] using hN)
  have hKpos : 1 ≤ blockCount N ρ := by unfold blockCount; omega
  intro i j hij
  by_cases hjK : j < blockCount N ρ
  · by_cases hi0 : i = 0
    · simp [blockTime, hi0]
    · have hj0 : j ≠ 0 := by omega
      have hiK : i < blockCount N ρ := lt_of_le_of_lt hij hjK
      have htimei : blockTime N ρ i = evenCeil
          ((N : ℝ) * ρ ^ ((i : ℝ) - blockCount N ρ)) := by
        simp [blockTime, hi0, hiK]
      have htimej : blockTime N ρ j = evenCeil
          ((N : ℝ) * ρ ^ ((j : ℝ) - blockCount N ρ)) := by
        simp [blockTime, hj0, hjK]
      rw [htimei, htimej]
      apply evenCeil_mono
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (N : ℝ))
      apply Real.rpow_le_rpow_of_exponent_le hρ.le
      have hcast : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      exact sub_le_sub_right hcast _
  · have hiBound := blockTime_le_horizon hρ N hround i
    have hj0 : j ≠ 0 := by omega
    have htimej : blockTime N ρ j = N := by simp [blockTime, hj0, hjK]
    rw [htimej]
    exact hiBound

end Critical2DKPZ.Blocks
