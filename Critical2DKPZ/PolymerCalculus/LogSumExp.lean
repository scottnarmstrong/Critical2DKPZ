/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

/-! A finite nonnegative weighted sum of exponentials of convex functions has convex logarithm whenever at least one weight is positive. -/

@[expose] public section

open Set
open scoped BigOperators

namespace Critical2DKPZ.PolymerCalculus

variable {ι : Type*} [Fintype ι]

/-- A nonnegative weighted exponential sum is positive if one weight is positive. -/
theorem weighted_exp_sum_pos {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hpos : ∃ i, 0 < w i) (u : ι → ℝ) : 0 < ∑ i, w i * Real.exp (u i) := by
  obtain ⟨i, hi⟩ := hpos
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hw j) (Real.exp_pos _).le)
    ⟨i, Finset.mem_univ _, mul_pos hi (Real.exp_pos _)⟩

/-- Finite weighted Hölder in logarithmic coordinates, including zero endpoint weights. -/
theorem log_sum_exp_interpolate {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hpos : ∃ i, 0 < w i) (u v : ι → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    Real.log (∑ i, w i * Real.exp (a * u i + b * v i)) ≤
      a * Real.log (∑ i, w i * Real.exp (u i)) +
        b * Real.log (∑ i, w i * Real.exp (v i)) := by
  let U := ∑ i, w i * Real.exp (u i)
  let V := ∑ i, w i * Real.exp (v i)
  let L := a * Real.log U + b * Real.log V
  have hU : 0 < U := weighted_exp_sum_pos hw hpos u
  have hV : 0 < V := weighted_exp_sum_pos hw hpos v
  have hterm (i : ι) : Real.exp (a * u i + b * v i - L) ≤
      a * (Real.exp (u i) / U) + b * (Real.exp (v i) / V) := by
    have h := convexOn_exp.2 (mem_univ (u i - Real.log U))
      (mem_univ (v i - Real.log V)) ha hb hab
    simp only [smul_eq_mul, Real.exp_sub, Real.exp_log hU, Real.exp_log hV] at h
    convert h using 1
    congr 1
    dsimp only [L]
    ring
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => mul_le_mul_of_nonneg_left (hterm i) (hw i))
  have hnorm : (∑ i, w i *
      (a * (Real.exp (u i) / U) + b * (Real.exp (v i) / V))) = 1 := by
    simp only [mul_add, Finset.sum_add_distrib]
    simp_rw [show ∀ i, w i * (a * (Real.exp (u i) / U)) =
      a * (w i * Real.exp (u i)) / U by intro i; ring]
    simp_rw [show ∀ i, w i * (b * (Real.exp (v i) / V)) =
      b * (w i * Real.exp (v i)) / V by intro i; ring]
    rw [← Finset.sum_div, ← Finset.mul_sum, ← Finset.sum_div, ← Finset.mul_sum]
    change a * U / U + b * V / V = 1
    rw [mul_div_cancel_right₀ a hU.ne', mul_div_cancel_right₀ b hV.ne', hab]
  rw [hnorm] at hsum
  simp_rw [Real.exp_sub, ← mul_div_assoc] at hsum
  rw [← Finset.sum_div, div_le_one (Real.exp_pos L)] at hsum
  have hp := weighted_exp_sum_pos hw hpos (fun i => a * u i + b * v i)
  have hlog := Real.log_le_log hp hsum
  rwa [Real.log_exp] at hlog


/-- A positive weighted log sum of exponentials preserves convexity. -/
theorem convexOn_log_weighted_exp_sum {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} {w : ι → ℝ} {f : ι → E → ℝ} (hs : Convex ℝ s)
    (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i) (hf : ∀ i, ConvexOn ℝ s (f i)) :
    ConvexOn ℝ s (fun x => Real.log (∑ i, w i * Real.exp (f i x))) := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  calc
    _ ≤ Real.log (∑ i, w i * Real.exp (a * f i x + b * f i y)) := by
      apply Real.log_le_log (weighted_exp_sum_pos hw hpos _)
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr ((hf i).2 hx hy ha hb hab)) (hw i)
    _ ≤ _ := log_sum_exp_interpolate hw hpos _ _ ha hb hab

/-- Coordinate monotonicity is preserved by nonnegative exponential sums. -/
theorem monotone_weighted_exp_sum {E : Type*} [Preorder E]
    {w : ι → ℝ} {f : ι → E → ℝ} (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, Monotone (f i)) :
    Monotone (fun x => ∑ i, w i * Real.exp (f i x)) := by
  intro x y hxy
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (hf i hxy)) (hw i)

/-- Positivity makes the logarithm of an increasing path sum increasing. -/
theorem monotone_log_weighted_exp_sum {E : Type*} [Preorder E]
    {w : ι → ℝ} {f : ι → E → ℝ} (hw : ∀ i, 0 ≤ w i) (hpos : ∃ i, 0 < w i)
    (hf : ∀ i, Monotone (f i)) :
    Monotone (fun x => Real.log (∑ i, w i * Real.exp (f i x))) := by
  intro x y hxy
  exact Real.log_le_log (weighted_exp_sum_pos hw hpos _)
    (monotone_weighted_exp_sum hw hf hxy)

end Critical2DKPZ.PolymerCalculus
