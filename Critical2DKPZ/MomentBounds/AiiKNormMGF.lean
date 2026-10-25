/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.AiiKWalkMGF
public import Critical2DKPZ.RandomWalk.Estimates
import Mathlib.Tactic

/-! # Radial exponential moments of the planar walk kernel -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

private theorem exp_mul_norm_le_four_coord_exp {t : ℝ} (ht : 0 ≤ t) (z : Site) :
    Real.exp (t * ‖siteToPlane z‖) ≤
      Real.exp (2 * t * (z 0 : ℝ)) + Real.exp (-(2 * t * (z 0 : ℝ))) +
        Real.exp (2 * t * (z 1 : ℝ)) + Real.exp (-(2 * t * (z 1 : ℝ))) := by
  let x := (z 0 : ℝ)
  let y := (z 1 : ℝ)
  have hnorm : ‖siteToPlane z‖ ≤ |x| + |y| := by
    have hnormsq := norm_siteToPlane_sq z
    have hcross : 0 ≤ |x| * |y| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have ha : 0 ≤ |x| + |y| := add_nonneg (abs_nonneg _) (abs_nonneg _)
    dsimp [x, y] at hcross hnormsq ⊢
    nlinarith [sq_abs (z 0 : ℝ), sq_abs (z 1 : ℝ),
      norm_nonneg (siteToPlane z), hnormsq, hcross, ha]
  have hmax : |x| + |y| ≤ 2 * max |x| |y| := by
    nlinarith [le_max_left |x| |y|, le_max_right |x| |y|]
  have hexp : Real.exp (t * ‖siteToPlane z‖) ≤ Real.exp (2 * t * max |x| |y|) :=
    Real.exp_le_exp.mpr (by nlinarith [hnorm, hmax, mul_nonneg ht (norm_nonneg (siteToPlane z))])
  have habsx (w : ℝ) :
      Real.exp (2 * t * |w|) ≤ Real.exp (2 * t * w) + Real.exp (-(2 * t * w)) := by
    by_cases hw : 0 ≤ w
    · rw [abs_of_nonneg hw]
      exact le_add_of_nonneg_right (Real.exp_nonneg _)
    · rw [abs_of_neg (lt_of_not_ge hw)]
      have heq : 2 * t * -w = -(2 * t * w) := by ring
      rw [heq]
      exact le_add_of_nonneg_left (Real.exp_nonneg _)
  by_cases hxy : |x| ≤ |y|
  · rw [max_eq_right hxy] at hexp
    calc
      Real.exp (t * ‖siteToPlane z‖) ≤ Real.exp (2 * t * |y|) := hexp
      _ ≤ Real.exp (2 * t * y) + Real.exp (-(2 * t * y)) := habsx y
      _ ≤ _ := by nlinarith [Real.exp_nonneg (2 * t * (z 1 : ℝ)),
        Real.exp_nonneg (-(2 * t * (z 1 : ℝ))),
        Real.exp_nonneg (2 * t * (z 0 : ℝ)),
        Real.exp_nonneg (-(2 * t * (z 0 : ℝ)))]
  · have hyx : |y| ≤ |x| := le_of_not_ge hxy
    rw [max_eq_left hyx] at hexp
    calc
      Real.exp (t * ‖siteToPlane z‖) ≤ Real.exp (2 * t * |x|) := hexp
      _ ≤ Real.exp (2 * t * x) + Real.exp (-(2 * t * x)) := habsx x
      _ ≤ _ := by nlinarith [Real.exp_nonneg (2 * t * (z 0 : ℝ)),
        Real.exp_nonneg (-(2 * t * (z 0 : ℝ))),
        Real.exp_nonneg (2 * t * (z 1 : ℝ)),
        Real.exp_nonneg (-(2 * t * (z 1 : ℝ)))]

private theorem tsum_mul_srwKernel_eq_sum_endpoints (n : ℕ) (f : Site → ℝ) :
    ∑' z : Site, f z * srwKernel n z =
      ∑ z ∈ Polymer.endpoints 0 n, f z * srwKernel n z := by
  apply tsum_eq_sum
  intro z hz
  have h := Polymer.srwKernel_eq_zero_of_not_mem n 0 z hz
  have hq : srwKernel n z = 0 := by simpa only [sub_zero] using h
  simp [hq]

private theorem exp_norm_mul_srwKernel_pointwise_le
    (c CG cG t : ℝ) (hc : CG ≤ c) (hCG : 0 ≤ CG) (hcG : 0 < cG)
    (hcc : 1 / (8 * cG) ≤ c)
    (hgauss : ∀ n : ℕ, 1 ≤ n → ∀ z : Site,
      srwKernel n z ≤ CG / n * Real.exp (-cG * ‖siteToPlane z‖ ^ 2 / n))
    (n : ℕ) (hn : 1 ≤ n) (z : Site) :
    Real.exp (t * ‖siteToPlane z‖) * srwKernel n z ≤
      c * Real.exp (2 * c * t ^ 2 * n) / n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hr : 0 ≤ ‖siteToPlane z‖ := norm_nonneg _
  have hcomplete :
      t * ‖siteToPlane z‖ - cG * ‖siteToPlane z‖ ^ 2 / n ≤
        t ^ 2 * n / (4 * cG) := by
    have hsq := sq_nonneg (2 * cG * ‖siteToPlane z‖ - t * n)
    apply (le_div_iff₀ (by positivity : 0 < 4 * cG)).2
    field_simp [ne_of_gt hnR] at hsq ⊢
    nlinarith [hsq]
  have hcoeff : 1 / (4 * cG) ≤ 2 * c := by
    have hmul := mul_le_mul_of_nonneg_right hcc (by norm_num : (0 : ℝ) ≤ 2)
    calc
      1 / (4 * cG) = 2 * (1 / (8 * cG)) := by field_simp; norm_num
      _ ≤ 2 * c := by nlinarith [hmul]
  have hexp :
      Real.exp (t * ‖siteToPlane z‖ - cG * ‖siteToPlane z‖ ^ 2 / n) ≤
        Real.exp (2 * c * t ^ 2 * n) := by
    apply Real.exp_le_exp.mpr
    calc
      t * ‖siteToPlane z‖ - cG * ‖siteToPlane z‖ ^ 2 / n ≤ t ^ 2 * n / (4 * cG) := hcomplete
      _ ≤ 2 * c * t ^ 2 * n := by
        have hnonneg : 0 ≤ t ^ 2 * n := by positivity
        have hh := mul_le_mul_of_nonneg_right hcoeff hnonneg
        calc
          t ^ 2 * n / (4 * cG) = (1 / (4 * cG)) * (t ^ 2 * n) := by ring
          _ ≤ (2 * c) * (t ^ 2 * n) := hh
          _ = 2 * c * t ^ 2 * n := by ring
  have hq := hgauss n hn z
  calc
    Real.exp (t * ‖siteToPlane z‖) * srwKernel n z ≤
        Real.exp (t * ‖siteToPlane z‖) *
          (CG / n * Real.exp (-cG * ‖siteToPlane z‖ ^ 2 / n)) :=
      mul_le_mul_of_nonneg_left hq (Real.exp_nonneg _)
    _ = CG / n * (Real.exp (t * ‖siteToPlane z‖) *
          Real.exp (-cG * ‖siteToPlane z‖ ^ 2 / n)) := by ring_nf
    _ = CG / n * Real.exp
          (t * ‖siteToPlane z‖ - cG * ‖siteToPlane z‖ ^ 2 / n) := by
      rw [← Real.exp_add]
      ring_nf
    _ ≤ CG / n * Real.exp (2 * c * t ^ 2 * n) :=
      mul_le_mul_of_nonneg_left hexp (div_nonneg hCG hnR.le)
    _ ≤ c / n * Real.exp (2 * c * t ^ 2 * n) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact div_le_div_of_nonneg_right hc hnR.le
    _ = c * Real.exp (2 * c * t ^ 2 * n) / n := by ring

/-- Radial exponential moment and pointwise Gaussian bounds for the planar walk kernel. -/
theorem tsum_exp_mul_norm_srwKernel_le :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ t : ℝ, 0 ≤ t → ∀ n : ℕ,
      (∑' x : Site, Real.exp (t * ‖siteToPlane x‖) * srwKernel n x ≤
        c * Real.exp (2 * c * t ^ 2 * n)) ∧
      (1 ≤ n → ∀ x : Site,
        Real.exp (t * ‖siteToPlane x‖) * srwKernel n x ≤
          c * Real.exp (2 * c * t ^ 2 * n) / n) := by
  obtain ⟨Ccoord, hCcoord, hcoord⟩ := tsum_exp_mul_coord_srwKernel_le
  obtain ⟨CG, cG, hcG, hgauss⟩ := srwKernel_gaussianBound
  have hCG : 0 ≤ CG := by
    have h0 := hgauss 2 (by norm_num) 0
    have hq : 0 < srwKernel 2 0 := srwKernel_two_zero_pos
    have he : 0 < Real.exp (-cG * ‖siteToPlane (0 : Site)‖ ^ 2 / 2) / 2 := by positivity
    have hnonneg : 0 ≤ CG *
        (Real.exp (-cG * ‖siteToPlane (0 : Site)‖ ^ 2 / 2) / 2) := by
      have hh : 0 ≤ CG / 2 *
          Real.exp (-cG * ‖siteToPlane (0 : Site)‖ ^ 2 / 2) := hq.le.trans h0
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hh
    by_contra hnot
    exact (not_lt_of_ge hnonneg) (mul_neg_of_neg_of_pos (lt_of_not_ge hnot) he)
  let c := max 4 (max Ccoord (max CG (1 / (8 * cG))))
  have hc4 : 4 ≤ c := le_max_left _ _
  have hcC : Ccoord ≤ c :=
    (le_max_left Ccoord (max CG (1 / (8 * cG)))).trans (le_max_right 4 _)
  have hcCG : CG ≤ c :=
    (le_max_left CG (1 / (8 * cG))).trans
      ((le_max_right Ccoord (max CG (1 / (8 * cG)))).trans (le_max_right 4 _))
  have hccomp : 1 / (8 * cG) ≤ c :=
    (le_max_right CG (1 / (8 * cG))).trans
      ((le_max_right Ccoord (max CG (1 / (8 * cG)))).trans (le_max_right 4 _))
  have hc1 : 1 ≤ c := by linarith
  refine ⟨c, hc1, fun t ht n => ?_⟩
  constructor
  · let E := Polymer.endpoints (0 : Site) n
    have hsum := tsum_mul_srwKernel_eq_sum_endpoints n
      (fun x => Real.exp (t * ‖siteToPlane x‖))
    calc
      ∑' x : Site, Real.exp (t * ‖siteToPlane x‖) * srwKernel n x =
          ∑ x ∈ E, Real.exp (t * ‖siteToPlane x‖) * srwKernel n x := hsum
      _ ≤ ∑ x ∈ E,
          (Real.exp (2 * t * (x 0 : ℝ)) + Real.exp (-(2 * t * (x 0 : ℝ))) +
            Real.exp (2 * t * (x 1 : ℝ)) + Real.exp (-(2 * t * (x 1 : ℝ)))) * srwKernel n x := by
          apply Finset.sum_le_sum
          intro x hx
          exact mul_le_mul_of_nonneg_right (exp_mul_norm_le_four_coord_exp ht x)
            (srwKernel_nonneg n x)
      _ = (∑' x : Site, Real.exp (2 * t * (x 0 : ℝ)) * srwKernel n x) +
            (∑' x : Site, Real.exp (-(2 * t * (x 0 : ℝ))) * srwKernel n x) +
            (∑' x : Site, Real.exp (2 * t * (x 1 : ℝ)) * srwKernel n x) +
            (∑' x : Site, Real.exp (-(2 * t * (x 1 : ℝ))) * srwKernel n x) := by
          have hs0 := (tsum_mul_srwKernel_eq_sum_endpoints n
            (fun x => Real.exp (2 * t * (x 0 : ℝ)))).symm
          have hs1 := (tsum_mul_srwKernel_eq_sum_endpoints n
            (fun x => Real.exp (-(2 * t * (x 0 : ℝ))))).symm
          have hs2 := (tsum_mul_srwKernel_eq_sum_endpoints n
            (fun x => Real.exp (2 * t * (x 1 : ℝ)))).symm
          have hs3 := (tsum_mul_srwKernel_eq_sum_endpoints n
            (fun x => Real.exp (-(2 * t * (x 1 : ℝ))))).symm
          simp only [add_mul]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
          rw [hs0, hs1, hs2, hs3]
      _ ≤ 4 * Real.exp (2 * Ccoord * t ^ 2 * n) := by
          have h0 := (hcoord (2 * t) 0 n).1
          have h1 := (hcoord (-(2 * t)) 0 n).1
          have h2 := (hcoord (2 * t) 1 n).1
          have h3 := (hcoord (-(2 * t)) 1 n).1
          have h0exp : Ccoord * (2 * t) ^ 2 * n / 2 = 2 * Ccoord * t ^ 2 * n := by ring
          have h1exp : Ccoord * (-(2 * t)) ^ 2 * n / 2 = 2 * Ccoord * t ^ 2 * n := by ring
          rw [h0exp] at h0
          rw [h0exp] at h2
          rw [h1exp] at h1
          rw [h1exp] at h3
          have h0' : (∑' x : Site, Real.exp (2 * t * (x 0 : ℝ)) * srwKernel n x) ≤
              Real.exp (2 * Ccoord * t ^ 2 * n) := h0
          have h1' : (∑' x : Site, Real.exp (-(2 * t * (x 0 : ℝ))) * srwKernel n x) ≤
              Real.exp (2 * Ccoord * t ^ 2 * n) := by
            convert h1 using 1
            all_goals
              congr 1
              ring_nf
          have h2' : (∑' x : Site, Real.exp (2 * t * (x 1 : ℝ)) * srwKernel n x) ≤
              Real.exp (2 * Ccoord * t ^ 2 * n) := h2
          have h3' : (∑' x : Site, Real.exp (-(2 * t * (x 1 : ℝ))) * srwKernel n x) ≤
              Real.exp (2 * Ccoord * t ^ 2 * n) := by
            convert h3 using 1
            all_goals
              congr 1
              ring_nf
          linarith
      _ ≤ c * Real.exp (2 * c * t ^ 2 * n) := by
          have hcoeff : Ccoord ≤ c := hcC
          have hdiff : 0 ≤ c - Ccoord := sub_nonneg.mpr hcoeff
          have hmul : 0 ≤ (c - Ccoord) * (2 * t ^ 2 * n) := mul_nonneg hdiff (by positivity)
          have harg : 2 * Ccoord * t ^ 2 * n ≤ 2 * c * t ^ 2 * n := by nlinarith [hmul]
          have hexp : Real.exp (2 * Ccoord * t ^ 2 * n) ≤ Real.exp (2 * c * t ^ 2 * n) :=
            Real.exp_le_exp.mpr harg
          calc
            4 * Real.exp (2 * Ccoord * t ^ 2 * n) ≤ 4 * Real.exp (2 * c * t ^ 2 * n) :=
              mul_le_mul_of_nonneg_left hexp (by norm_num)
            _ ≤ c * Real.exp (2 * c * t ^ 2 * n) :=
              mul_le_mul_of_nonneg_right hc4 (Real.exp_nonneg _)
  · intro hn x
    exact exp_norm_mul_srwKernel_pointwise_le c CG cG t hcCG hCG hcG hccomp hgauss n hn x

end Critical2DKPZ.MomentBounds

end
