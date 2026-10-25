/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25FiniteOperators
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-! # The finite Schur estimate for counting Lp norms -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- Schur's test on a finite set, with matching row and column bounds. -/
theorem finiteLpNorm_finiteKernelApply_le_of_rowCol {α : Type*} (s : Finset α)
    (K : α → α → ℝ) (hK : ∀ x y, 0 ≤ K x y) {q : ℝ} (hq : 1 ≤ q) {a : ℝ}
    (hrow : ∀ x ∈ s, ∑ y ∈ s, K x y ≤ a)
    (hcol : ∀ y ∈ s, ∑ x ∈ s, K x y ≤ a) (f : α → ℝ) :
    finiteLpNorm s q (finiteKernelApply s K f) ≤ a * finiteLpNorm s q f := by
  by_cases hs : s.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hs
    have hrowNonneg (x : α) : 0 ≤ ∑ y ∈ s, K x y :=
      Finset.sum_nonneg fun y hy => hK x y
    have ha : 0 ≤ a := (hrowNonneg x₀).trans (hrow x₀ hx₀)
    have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
    let row (x : α) : ℝ := ∑ y ∈ s, K x y
    let weighted (x : α) : ℝ := ∑ y ∈ s, K x y * |f y| ^ q
    have hweightedNonneg (x : α) : 0 ≤ weighted x := by
      dsimp [weighted]
      exact Finset.sum_nonneg fun y hy => mul_nonneg (hK x y) (Real.rpow_nonneg (abs_nonneg _) _)
    have hpoint (x : α) (hx : x ∈ s) :
        |finiteKernelApply s K f x| ^ q ≤ a ^ (q - 1) * weighted x := by
      have hraw :
          |finiteKernelApply s K f x| ≤ ∑ y ∈ s, K x y * |f y| := by
        rw [finiteKernelApply]
        calc
          |∑ y ∈ s, K x y * f y| ≤ ∑ y ∈ s, |K x y * f y| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ y ∈ s, K x y * |f y| := by
            apply Finset.sum_le_sum
            intro y hy
            rw [abs_mul, abs_of_nonneg (hK x y)]
      have hrowLp := Real.inner_le_weight_mul_Lp_of_nonneg s hq
        (fun y => K x y) (fun y => |f y|)
        (fun y => hK x y) (fun y => abs_nonneg (f y))
      have hrowLp' :
          ∑ y ∈ s, K x y * |f y| ≤
            row x ^ (1 - q⁻¹) * weighted x ^ q⁻¹ := by
        simpa only [row, weighted] using hrowLp
      have hrowPow : row x ^ (q - 1) ≤ a ^ (q - 1) := by
        apply Real.rpow_le_rpow (hrowNonneg x) (hrow x hx)
        linarith
      have hrawSumNonneg : 0 ≤ ∑ y ∈ s, K x y * |f y| :=
        Finset.sum_nonneg fun y hy => mul_nonneg (hK x y) (abs_nonneg _)
      have hraise := Real.rpow_le_rpow hrawSumNonneg hrowLp' hqpos.le
      have hmoment :
          (∑ y ∈ s, K x y * |f y|) ^ q ≤ row x ^ (q - 1) * weighted x := by
        calc
          _ ≤ (row x ^ (1 - q⁻¹) * weighted x ^ q⁻¹) ^ q := hraise
          _ = row x ^ (q - 1) * weighted x := by
            rw [Real.mul_rpow (Real.rpow_nonneg (hrowNonneg x) _)
              (Real.rpow_nonneg (hweightedNonneg x) _), ← Real.rpow_mul (hrowNonneg x),
              ← Real.rpow_mul (hweightedNonneg x)]
            rw [show (1 - q⁻¹) * q = q - 1 by field_simp,
              show q⁻¹ * q = 1 by field_simp, Real.rpow_one]
      have hrawPow := Real.rpow_le_rpow (abs_nonneg _) hraw hqpos.le
      calc
        |finiteKernelApply s K f x| ^ q ≤
            (∑ y ∈ s, K x y * |f y|) ^ q := hrawPow
        _ ≤ row x ^ (q - 1) * weighted x := hmoment
        _ ≤ a ^ (q - 1) * weighted x :=
          mul_le_mul_of_nonneg_right hrowPow (hweightedNonneg x)
    have hsum :
        (∑ x ∈ s, |finiteKernelApply s K f x| ^ q) ≤
          a ^ q * ∑ y ∈ s, |f y| ^ q := by
      calc
        _ ≤ ∑ x ∈ s, a ^ (q - 1) * weighted x :=
          Finset.sum_le_sum fun x hx => hpoint x hx
        _ = a ^ (q - 1) * ∑ x ∈ s, weighted x := by rw [Finset.mul_sum]
        _ = a ^ (q - 1) * ∑ y ∈ s, |f y| ^ q * (∑ x ∈ s, K x y) := by
          congr 1
          simp only [weighted]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y hy
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          ring
        _ ≤ a ^ (q - 1) * ∑ y ∈ s, |f y| ^ q * a := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ha _)
          apply Finset.sum_le_sum
          intro y hy
          exact mul_le_mul_of_nonneg_left (hcol y hy)
            (Real.rpow_nonneg (abs_nonneg (f y)) _)
        _ = a ^ q * ∑ y ∈ s, |f y| ^ q := by
          rw [← Finset.sum_mul]
          calc
            a ^ (q - 1) * ((∑ y ∈ s, |f y| ^ q) * a) =
                (a ^ (q - 1) * a) * ∑ y ∈ s, |f y| ^ q := by ring
            _ = a ^ q * ∑ y ∈ s, |f y| ^ q := by
              congr 1
              calc
                a ^ (q - 1) * a = a ^ (q - 1) * a ^ (1 : ℝ) := by
                  rw [Real.rpow_one]
                _ = a ^ ((q - 1) + 1) := by
                  by_cases ha0 : a = 0
                  · simp [ha0, Real.zero_rpow, hqpos.ne']
                  · rw [← Real.rpow_add (lt_of_le_of_ne ha (Ne.symm ha0))]
                _ = a ^ q := by
                  congr 1
                  ring
    have hroot := Real.rpow_le_rpow
      (Finset.sum_nonneg fun x hx => Real.rpow_nonneg (abs_nonneg _) _)
      hsum (by positivity : 0 ≤ 1 / q)
    calc
      finiteLpNorm s q (finiteKernelApply s K f) =
          (∑ x ∈ s, |finiteKernelApply s K f x| ^ q) ^ (1 / q) := rfl
      _ ≤ (a ^ q * ∑ y ∈ s, |f y| ^ q) ^ (1 / q) := hroot
      _ = a * finiteLpNorm s q f := by
        rw [Real.mul_rpow (Real.rpow_nonneg ha _) (Finset.sum_nonneg fun y hy =>
          Real.rpow_nonneg (abs_nonneg _) _), ← Real.rpow_mul ha]
        rw [show q * (1 / q) = 1 by field_simp]
        rw [Real.rpow_one]
        rfl
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    have hqpos : 0 < q := by linarith
    have hzero : (0 : ℝ) ^ (1 / q) = 0 := Real.zero_rpow (by positivity)
    have hzero' : (0 : ℝ) ^ q⁻¹ = 0 := by simpa only [one_div] using hzero
    simp [finiteLpNorm, finiteKernelApply, hzero']

end

end Critical2DKPZ.MomentBounds
