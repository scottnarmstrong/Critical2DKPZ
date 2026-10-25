/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.ChainSummability
import Mathlib.Tactic

/-! # Summable word-counted majorants for conjugated diagrams -/

@[expose] public noncomputable section

open MeasureTheory Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- One admissible damping rate bounds the word-counted diagram majorants by a summable cubic polynomial times `2⁻ᵐ`. -/
theorem exists_summable_conjugated_diagram_majorant (n : ℕ) (c T : ℝ) (hc : 1 ≤ c) :
    ∃ rate B : ℝ, c + 3 ≤ rate ∧ 0 ≤ rate ∧ 0 ≤ B ∧
      Summable (fun m : ℕ => B * ((m : ℝ) + 1) ^ 3 * (1 / 2 : ℝ) ^ m) ∧
      ∀ m : ℕ, (Fintype.card (CollisionWord n (m + 1)) : ℝ) *
        (c ^ (m + 1) * ((m : ℝ) + 1) ^ 3 * (c / Real.log (rate - c - 1)) ^ m *
          Real.exp (rate * max T 1)) ≤
        B * ((m : ℝ) + 1) ^ 3 * (1 / 2 : ℝ) ^ m := by
  classical
  let N : ℝ := max (Fintype.card (CollisionPair n) : ℝ) 1
  have hN1 : 1 ≤ N := le_max_right _ _
  have hN : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  have hcPos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hc0 : 0 ≤ c := hcPos.le
  let rate : ℝ := correctedChainRate N 1 c
  have hlog : Real.log (rate - c - 1) = 2 * N * c ^ 2 := by
    simpa only [mul_one] using correctedChainRate_log N 1 c
  have hL : 0 < Real.log (rate - c - 1) := by rw [hlog]; positivity
  have hNc : 1 ≤ N * c ^ 2 := by
    simpa only [one_mul] using mul_le_mul hN1 (one_le_pow₀ hc) zero_le_one hN.le
  have hArg : 2 ≤ 2 * N * c ^ 2 := by
    calc
      2 = 2 * (1 : ℝ) := by ring
      _ ≤ 2 * (N * c ^ 2) := mul_le_mul_of_nonneg_left hNc (by norm_num)
      _ = _ := by ring
  have hExp : 3 ≤ Real.exp (2 * N * c ^ 2) := by
    have h := Real.add_one_le_exp (2 * N * c ^ 2)
    linarith only [h, hArg]
  have hRateDef : rate = Real.exp (2 * N * c ^ 2) + c + 1 := by
    simp only [rate, correctedChainRate, mul_one]
  have hRate : c + 3 ≤ rate := by rw [hRateDef]; linarith only [hExp]
  have hRate0 : 0 ≤ rate := by linarith only [hRate, hc]
  have hRatio : (N * c) * (c / Real.log (rate - c - 1)) = (1 / 2 : ℝ) := by
    rw [hlog]
    field_simp
  let B : ℝ := N * c * Real.exp (rate * max T 1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hSum : Summable (fun m : ℕ => B * ((m : ℝ) + 1) ^ 3 * (1 / 2 : ℝ) ^ m) := by
    have h := (summable_natSucc_cube_mul_pow (q := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left B
    simpa only [mul_assoc] using h
  refine ⟨rate, B, hRate, hRate0, hB, hSum, ?_⟩
  intro m
  have hCardBase : (Fintype.card (CollisionWord n (m + 1)) : ℝ) ≤
      (Fintype.card (CollisionPair n) : ℝ) ^ (m + 1) := by
    exact_mod_cast collisionWord_card_le_pow n (m + 1)
  have hCard : (Fintype.card (CollisionWord n (m + 1)) : ℝ) ≤ N ^ (m + 1) :=
    hCardBase.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (le_max_left _ _) _)
  have hPower : N ^ (m + 1) * c ^ (m + 1) * (c / Real.log (rate - c - 1)) ^ m =
      N * c * (1 / 2 : ℝ) ^ m := by
    rw [← mul_pow, pow_succ]
    calc
      _ = (N * c) * ((N * c) * (c / Real.log (rate - c - 1))) ^ m := by
        simp only [mul_pow]
        ring
      _ = _ := by rw [hRatio]
  calc
    _ ≤ N ^ (m + 1) *
        (c ^ (m + 1) * ((m : ℝ) + 1) ^ 3 * (c / Real.log (rate - c - 1)) ^ m *
          Real.exp (rate * max T 1)) := mul_le_mul_of_nonneg_right hCard (by positivity)
    _ = (N ^ (m + 1) * c ^ (m + 1) * (c / Real.log (rate - c - 1)) ^ m) *
        ((m : ℝ) + 1) ^ 3 * Real.exp (rate * max T 1) := by ac_rfl
    _ = _ := by rw [hPower]; dsimp [B]; ac_rfl

end Critical2DKPZ.SHF.Tsai

end
