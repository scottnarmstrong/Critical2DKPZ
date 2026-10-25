/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.ProfileKernelPerturbation
public import Critical2DKPZ.Smoothing.ProfileL2Perturbation
import Mathlib.Tactic

/-! # Squared-`ℓ²` control of finite profile perturbations -/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.Smoothing

/-- A random-walk collision kernel contracts the squared norm of a finite signed profile.
The estimate is the discrete Schur bound with both kernel marginals equal to one. -/
theorem finite_kernel_quadratic_le_sq (r : ℕ) (μ : Site → ℝ) (A : Finset Site) :
    (∑ w ∈ A, ∑ v ∈ A, μ w * μ v * srwKernel (2 * r) (v - w)) ≤
      ∑ w ∈ A, μ w ^ 2 := by
  classical
  have hkernel (w v : Site) : 0 ≤ srwKernel (2 * r) (v - w) :=
    Polymer.kernel_nonneg _ _
  have hrow (w : Site) : ∑ v ∈ A, srwKernel (2 * r) (v - w) ≤ 1 := by
    let E := Polymer.endpoints w (2 * r)
    calc
      _ ≤ ∑ v ∈ A ∪ E, srwKernel (2 * r) (v - w) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        intro v hv hnot
        exact hkernel w v
      _ = ∑ v ∈ E, srwKernel (2 * r) (v - w) := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro v hv hnot
        exact Polymer.srwKernel_eq_zero_of_not_mem (2 * r) w v (by simpa [E] using hnot)
      _ = 1 := Polymer.sum_srwKernel_endpoints (2 * r) w
  have hcolumn (v : Site) : ∑ w ∈ A, srwKernel (2 * r) (v - w) ≤ 1 := by
    calc
      _ = ∑ w ∈ A, srwKernel (2 * r) (w - v) := by
        apply Finset.sum_congr rfl
        intro w hw
        exact Polymer.srwKernel_sub_swap (2 * r) v w
      _ ≤ 1 := hrow v
  have hterm (w v : Site) :
      μ w * μ v * srwKernel (2 * r) (v - w) ≤
        ((μ w ^ 2 + μ v ^ 2) / 2) * srwKernel (2 * r) (v - w) := by
    have hmul : μ w * μ v ≤ (μ w ^ 2 + μ v ^ 2) / 2 := by
      nlinarith [sq_nonneg (μ w - μ v)]
    exact mul_le_mul_of_nonneg_right hmul (hkernel w v)
  have hsumIdentity :
      (∑ w ∈ A, ∑ v ∈ A,
        ((μ w ^ 2 + μ v ^ 2) / 2) * srwKernel (2 * r) (v - w)) =
        (∑ w ∈ A, μ w ^ 2 * (∑ v ∈ A, srwKernel (2 * r) (v - w)) +
          ∑ v ∈ A, μ v ^ 2 * (∑ w ∈ A, srwKernel (2 * r) (v - w))) / 2 := by
    have hterms : ∀ w v : Site,
        ((μ w ^ 2 + μ v ^ 2) / 2) * srwKernel (2 * r) (v - w) =
          (μ w ^ 2 * srwKernel (2 * r) (v - w) +
            μ v ^ 2 * srwKernel (2 * r) (v - w)) / 2 := by
      intro w v
      ring
    calc
      _ = ∑ w ∈ A, ∑ v ∈ A,
          (μ w ^ 2 * srwKernel (2 * r) (v - w) +
            μ v ^ 2 * srwKernel (2 * r) (v - w)) / 2 := by
              apply Finset.sum_congr rfl
              intro w hw
              apply Finset.sum_congr rfl
              intro v hv
              exact hterms w v
      _ = (∑ w ∈ A, ∑ v ∈ A,
            (μ w ^ 2 * srwKernel (2 * r) (v - w) +
              μ v ^ 2 * srwKernel (2 * r) (v - w))) / 2 := by
            simp only [Finset.sum_div]
      _ = ((∑ w ∈ A, μ w ^ 2 * (∑ v ∈ A, srwKernel (2 * r) (v - w))) +
          ∑ v ∈ A, μ v ^ 2 * (∑ w ∈ A, srwKernel (2 * r) (v - w))) / 2 := by
            congr 1
            calc
              _ = (∑ w ∈ A, ∑ v ∈ A,
                    μ w ^ 2 * srwKernel (2 * r) (v - w)) +
                  (∑ w ∈ A, ∑ v ∈ A,
                    μ v ^ 2 * srwKernel (2 * r) (v - w)) := by
                      simp only [Finset.sum_add_distrib]
              _ = _ := by
                    congr 1
                    · apply Finset.sum_congr rfl
                      intro w hw
                      rw [← Finset.mul_sum]
                    · rw [Finset.sum_comm]
                      apply Finset.sum_congr rfl
                      intro v hv
                      rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ w ∈ A, ∑ v ∈ A,
        ((μ w ^ 2 + μ v ^ 2) / 2) * srwKernel (2 * r) (v - w) := by
      apply Finset.sum_le_sum
      intro w hw
      apply Finset.sum_le_sum
      intro v hv
      exact hterm w v
    _ = _ := hsumIdentity
    _ ≤ (∑ w ∈ A, μ w ^ 2 + ∑ v ∈ A, μ v ^ 2) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
      apply add_le_add
      · calc
          _ ≤ ∑ w ∈ A, μ w ^ 2 * 1 := by
            apply Finset.sum_le_sum
            intro w hw
            exact mul_le_mul_of_nonneg_left (hrow w) (sq_nonneg _)
          _ = ∑ w ∈ A, μ w ^ 2 := by simp only [mul_one]
      · calc
          _ ≤ ∑ v ∈ A, μ v ^ 2 * 1 := by
            apply Finset.sum_le_sum
            intro v hv
            exact mul_le_mul_of_nonneg_left (hcolumn v) (sq_nonneg _)
          _ = ∑ v ∈ A, μ v ^ 2 := by simp only [mul_one]
    _ = ∑ w ∈ A, μ w ^ 2 := by
      have hsum : (∑ v ∈ A, μ v ^ 2) = ∑ w ∈ A, μ w ^ 2 := rfl
      rw [hsum]
      ring


end Critical2DKPZ.Smoothing

end
