/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.BlockTime
import Critical2DKPZ.MomentBounds.BlockClockBounds
import Critical2DKPZ.PolymerCalculus.Clocks
import Mathlib.Tactic

/-! # Uniform bounds for the half-shifted geometric block grid -/

@[expose] public noncomputable section

open Filter

namespace Critical2DKPZ.Blocks

private def gridScale (N : ℕ) (ρ : ℝ) (i : ℕ) : ℝ :=
  N * ρ ^ ((i : ℝ) - blockCount N ρ)

private def shiftedTime (N : ℕ) (ρ : ℝ) (i : ℕ) : ℝ :=
  (blockTime N ρ i : ℝ) + 1 / 2

private theorem gridScale_pos {N : ℕ} {ρ : ℝ} (hN : 0 < N) (hρ : 0 < ρ) (i : ℕ) :
    0 < gridScale N ρ i := by
  dsimp [gridScale]
  positivity

private theorem gridScale_mul {N i j : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (hij : i ≤ j) :
    gridScale N ρ i * ρ ^ (j - i) = gridScale N ρ j := by
  unfold gridScale
  rw [← Real.rpow_natCast, mul_assoc, ← Real.rpow_add hρ, Nat.cast_sub hij]
  congr 2
  ring

private theorem shiftedTime_bounds {N i : ℕ} {ρ : ℝ} (hρ : 1 < ρ)
    (hi : 1 ≤ i) (hiK : i < blockCount N ρ) :
    1 ≤ gridScale N ρ i ∧ gridScale N ρ i ≤ shiftedTime N ρ i ∧
      shiftedTime N ρ i ≤ 4 * gridScale N ρ i := by
  have hscale := MomentBounds.blockTime_unrounded_geometric_scale hρ hi hiK
  have hone : 1 ≤ ρ ^ ((i : ℝ) - 1) :=
    Real.one_le_rpow hρ.le (sub_nonneg.mpr (show (1 : ℝ) ≤ i by exact_mod_cast hi))
  have hg : 1 ≤ gridScale N ρ i := hone.trans hscale
  have htime : blockTime N ρ i = evenCeil (gridScale N ρ i) := by
    simp only [blockTime, Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hi),
      ite_false, hiK, ite_true, gridScale]
  have hlo := le_evenCeil (gridScale N ρ i)
  have hhi := evenCeil_lt_add_two (show 0 ≤ gridScale N ρ i by linarith)
  dsimp [shiftedTime]
  rw [htime]
  exact ⟨hg, by linarith, by linarith⟩

private theorem shiftedTime_zero (N : ℕ) (ρ : ℝ) : shiftedTime N ρ 0 = 1 / 2 := by
  simp [shiftedTime, blockTime]

private theorem shiftedTime_pos (N : ℕ) (ρ : ℝ) (i : ℕ) : 0 < shiftedTime N ρ i := by
  dsimp [shiftedTime]
  positivity

/-- Half-shifted geometric cells satisfy uniform bounds on cell separation, ratios and logarithmic size. -/
theorem halfShiftedGrid_bounds :
    ∃ C ρ₀ : ℝ, 0 < C ∧ 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ →
      ∀ᶠ N : ℕ in atTop,
        (∀ i, 1 ≤ i → i < blockCount N ρ →
          4 * ((blockTime N ρ (i - 1) : ℝ) + 1 / 2) ≤ blockTime N ρ i + 1 / 2) ∧
        (∀ i j, 1 ≤ i → i ≤ j → j < blockCount N ρ →
          (blockTime N ρ i : ℝ) + 1 / 2 ≤
            (C / ρ) ^ (j - i) * ((blockTime N ρ j : ℝ) + 1 / 2)) ∧
        (∀ i, 1 ≤ i → i < blockCount N ρ →
          ((blockCount N ρ : ℝ) - i) * Real.log ρ ≤
            C * -Real.log (((blockTime N ρ i : ℝ) + 1 / 2) / N)) ∧
        (∀ i, 1 ≤ i → i < blockCount N ρ →
          Real.log (((blockTime N ρ i : ℝ) + 1 / 2) /
            ((blockTime N ρ (i - 1) : ℝ) + 1 / 2)) ≤ C * Real.log ρ) := by
  refine ⟨16, 256, by norm_num, by norm_num, ?_⟩
  intro ρ hρlarge
  have hρ : 1 < ρ := by linarith
  have hρpos : 0 < ρ := by linarith
  have hlog : 0 < Real.log ρ := Real.log_pos hρ
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog4ρ : 2 * Real.log 4 ≤ Real.log ρ := by
    calc
      2 * Real.log 4 = Real.log ((4 : ℝ) ^ 2) := (Real.log_pow 4 2).symm
      _ ≤ Real.log ρ := Real.log_le_log (by norm_num) (by norm_num; linarith)
  filter_upwards [eventually_ge_atTop (⌈ρ⌉₊)] with N hN
  have hρN : ρ ≤ (N : ℝ) := (Nat.le_ceil ρ).trans (by exact_mod_cast hN)
  have hNpos : 0 < (N : ℝ) := hρpos.trans_le hρN
  have hNnat : 0 < N := by exact_mod_cast hNpos
  change (∀ i, 1 ≤ i → i < blockCount N ρ →
      4 * shiftedTime N ρ (i - 1) ≤ shiftedTime N ρ i) ∧
    (∀ i j, 1 ≤ i → i ≤ j → j < blockCount N ρ →
      shiftedTime N ρ i ≤ (16 / ρ) ^ (j - i) * shiftedTime N ρ j) ∧
    (∀ i, 1 ≤ i → i < blockCount N ρ →
      ((blockCount N ρ : ℝ) - i) * Real.log ρ ≤
        16 * -Real.log (shiftedTime N ρ i / N)) ∧
    (∀ i, 1 ≤ i → i < blockCount N ρ →
      Real.log (shiftedTime N ρ i / shiftedTime N ρ (i - 1)) ≤ 16 * Real.log ρ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi hiK
    obtain ⟨hg, hlo, _⟩ := shiftedTime_bounds hρ hi hiK
    by_cases hi1 : i = 1
    · subst i
      rw [Nat.sub_self, shiftedTime_zero]
      have heven : 2 ≤ blockTime N ρ 1 := by
        have htime : blockTime N ρ 1 = evenCeil (gridScale N ρ 1) := by
          simp [blockTime, gridScale, hiK]
        rw [htime, evenCeil]
        have : 1 ≤ ⌈gridScale N ρ 1 / 2⌉₊ := by
          exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by linarith)).ne'
        omega
      have : (2 : ℝ) ≤ blockTime N ρ 1 := by exact_mod_cast heven
      dsimp [shiftedTime]
      linarith
    · obtain ⟨_, _, hprev⟩ := shiftedTime_bounds (N := N) hρ (i := i - 1) (by omega) (by omega)
      have hid := gridScale_mul (N := N) hρpos (show i - 1 ≤ i by omega)
      have hgap : i - (i - 1) = 1 := by omega
      rw [hgap, pow_one] at hid
      have hgprev := (gridScale_pos hNnat hρpos (i - 1)).le
      calc
        4 * shiftedTime N ρ (i - 1) ≤ 16 * gridScale N ρ (i - 1) := by linarith
        _ ≤ gridScale N ρ (i - 1) * ρ := by
          simpa only [mul_comm] using
            mul_le_mul_of_nonneg_right (show (16 : ℝ) ≤ ρ by linarith) hgprev
        _ = gridScale N ρ i := hid
        _ ≤ shiftedTime N ρ i := hlo
  · intro i j hi hij hjK
    by_cases heq : i = j
    · subst j
      simp
    · obtain ⟨_, _, hbi⟩ := shiftedTime_bounds hρ hi (lt_of_le_of_lt hij hjK)
      obtain ⟨_, hbj, _⟩ := shiftedTime_bounds hρ (by omega : 1 ≤ j) hjK
      have hd : 1 ≤ j - i := by omega
      have hp : (4 : ℝ) ≤ 16 ^ (j - i) := by
        calc
          (4 : ℝ) ≤ 16 ^ (1 : ℕ) := by norm_num
          _ ≤ 16 ^ (j - i) := pow_le_pow_right₀ (by norm_num) hd
      have hscale := gridScale_mul (N := N) hρpos hij
      have hpow : 0 < ρ ^ (j - i) := pow_pos hρpos _
      rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ hpow]
      calc
        shiftedTime N ρ i * ρ ^ (j - i) ≤ 4 * gridScale N ρ j := by
          rw [← hscale, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right hbi hpow.le
        _ ≤ 16 ^ (j - i) * shiftedTime N ρ j :=
          mul_le_mul hp hbj (by positivity) (by norm_num)
  · intro i hi hiK
    obtain ⟨_, _, hbi⟩ := shiftedTime_bounds hρ hi hiK
    have hratio : shiftedTime N ρ i / N ≤
        4 * ρ ^ ((i : ℝ) - blockCount N ρ) := by
      apply (div_le_iff₀ hNpos).2
      simpa only [gridScale, mul_left_comm, mul_comm, mul_assoc] using hbi
    have hlogratio := Real.log_le_log
      (div_pos (shiftedTime_pos N ρ i) hNpos) hratio
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
      (Real.rpow_pos_of_pos hρpos _).ne', Real.log_rpow hρpos] at hlogratio
    have hgap : (1 : ℝ) ≤ (blockCount N ρ : ℝ) - i := by
      have : (i : ℝ) + 1 ≤ blockCount N ρ := by
        exact_mod_cast Nat.succ_le_iff.2 hiK
      linarith
    have hprod := mul_le_mul_of_nonneg_right hgap hlog.le
    nlinarith only [hlogratio, hprod, hlog4ρ, hlog.le]
  · intro i hi hiK
    by_cases hi1 : i = 1
    · subst i
      rw [Nat.sub_self, shiftedTime_zero]
      have htime := MomentBounds.blockTime_first_endpoint_lt hρ hρN
      have hbound : shiftedTime N ρ 1 / (1 / 2) ≤ ρ ^ (2 : ℕ) := by
        dsimp [shiftedTime]
        have : 16 ≤ ρ := by linarith
        nlinarith [sq_nonneg (ρ - 2)]
      have hlogbound := Real.log_le_log
        (div_pos (shiftedTime_pos N ρ 1) (by norm_num : (0 : ℝ) < 1 / 2)) hbound
      rw [Real.log_pow] at hlogbound
      norm_num at hlogbound
      linarith
    · obtain ⟨_, _, hbi⟩ := shiftedTime_bounds hρ hi hiK
      obtain ⟨_, hprev, _⟩ := shiftedTime_bounds (N := N) hρ (i := i - 1) (by omega) (by omega)
      have hid := gridScale_mul (N := N) hρpos (show i - 1 ≤ i by omega)
      have hgap : i - (i - 1) = 1 := by omega
      rw [hgap, pow_one] at hid
      have hratio : shiftedTime N ρ i / shiftedTime N ρ (i - 1) ≤ 4 * ρ := by
        apply (div_le_iff₀ (shiftedTime_pos N ρ (i - 1))).2
        calc
          shiftedTime N ρ i ≤ 4 * gridScale N ρ i := hbi
          _ = (4 * ρ) * gridScale N ρ (i - 1) := by rw [← hid]; ring
          _ ≤ (4 * ρ) * shiftedTime N ρ (i - 1) :=
            mul_le_mul_of_nonneg_left hprev (by positivity)
      have hlogratio := Real.log_le_log
        (div_pos (shiftedTime_pos N ρ i) (shiftedTime_pos N ρ (i - 1))) hratio
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hρpos.ne'] at hlogratio
      linarith

end Critical2DKPZ.Blocks
