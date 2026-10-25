/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonPairFreeRows
public import Critical2DKPZ.MomentBounds.CSZ25GreenCalculus
import Mathlib.Tactic

/-! # L1 and supremum bounds for the leading fourth-moment boundary -/

@[expose] public noncomputable section

open Critical2DKPZ.MomentBounds
open scoped BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

private theorem summable_walk_kernel (n : ℕ) (y : Site) :
    Summable (fun x : Site => srwKernel n (x - y)) := by
  apply summable_of_ne_finset_zero (s := Polymer.endpoints y n)
  intro x hx
  exact Polymer.srwKernel_eq_zero_of_not_mem n y x hx

/-- Finite entrance smoothing preserves the total profile mass exactly. -/
theorem summable_tsum_finiteBoundaryConvolution (n : ℕ) (S : Finset Site) (φ : Site → ℝ) :
    Summable (finiteBoundaryConvolution n S φ) ∧
      (∑' x : Site, finiteBoundaryConvolution n S φ x) = ∑ y ∈ S, φ y := by
  have hs (y : Site) : Summable (fun x : Site => srwKernel n (x - y) * φ y) :=
    (summable_walk_kernel n y).mul_right _
  refine ⟨summable_sum (fun y (_ : y ∈ S) => hs y), ?_⟩
  unfold finiteBoundaryConvolution
  rw [Summable.tsum_finsetSum (fun y _ => hs y)]
  simp_rw [tsum_mul_right, Polymer.tsum_srwKernel, one_mul]

/-- Finite entrance smoothing also preserves a nonnegative supremum bound. -/
theorem finiteBoundaryConvolution_nonneg_le (n : ℕ) (S : Finset Site) (φ : Site → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ y ∈ S, 0 ≤ φ y) (hφB : ∀ y ∈ S, φ y ≤ B)
    (x : Site) : 0 ≤ finiteBoundaryConvolution n S φ x ∧ finiteBoundaryConvolution n S φ x ≤ B := by
  refine ⟨Finset.sum_nonneg (fun y hy => mul_nonneg (Polymer.kernel_nonneg _ _) (hφ y hy)), ?_⟩
  have hrow : (∑ y ∈ S, srwKernel n (x - y)) ≤ 1 := by
    have h := (summable_walk_kernel n x).sum_le_tsum S
      (fun y _ => Polymer.kernel_nonneg n (y - x))
    rw [Polymer.tsum_srwKernel] at h
    simpa only [Polymer.srwKernel_sub_swap n x] using h
  calc
    _ ≤ ∑ y ∈ S, srwKernel n (x - y) * B :=
      Finset.sum_le_sum (fun y hy => mul_le_mul_of_nonneg_left (hφB y hy) (Polymer.kernel_nonneg _ _))
    _ = (∑ y ∈ S, srwKernel n (x - y)) * B := (Finset.sum_mul S _ B).symm
    _ ≤ B := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hrow hB

/-- A bounded nonnegative summable lattice profile has a uniformly bounded
walk quadratic form at every even time, including time zero. -/
theorem tsum_profile_even_energy_le (m : ℕ) (F : Site → ℝ)
    (hF : ∀ x, 0 ≤ F x) (hs : Summable F) {B : ℝ}
    (hFB : ∀ x, F x ≤ B) :
    Summable (fun p : Site × Site => F p.1 * F p.2 * srwKernel (2 * m) (p.2 - p.1)) ∧
    (∑' p : Site × Site, F p.1 * F p.2 * srwKernel (2 * m) (p.2 - p.1)) ≤
      B * ∑' x : Site, F x := by
  have he : Summable (fun p : Site × Site => F p.1 * F p.2 * srwKernel (2 * m) (p.2 - p.1)) := by
    apply (summable_evenTimeEnergy_terms m F hF hs).congr
    intro p
    rw [Polymer.srwKernel_sub_swap (2 * m) p.1 p.2]
    ring
  have hrow (x : Site) : (∑' y : Site, F y * srwKernel (2 * m) (y - x)) ≤ B := by
    have ht : Summable (fun y : Site => F y * srwKernel (2 * m) (y - x)) :=
      Summable.of_nonneg_of_le (fun y => mul_nonneg (hF y) (Polymer.kernel_nonneg _ _))
        (fun y => mul_le_of_le_one_right (hF y) (Polymer.srwKernel_le_one _ _)) hs
    have hmajor := (summable_walk_kernel (2 * m) x).mul_left B
    have hle := ht.tsum_le_tsum
      (fun y => mul_le_mul_of_nonneg_right (hFB y) (Polymer.kernel_nonneg _ _)) hmajor
    simpa only [tsum_mul_left, Polymer.tsum_srwKernel, mul_one] using hle
  refine ⟨he, ?_⟩
  rw [he.tsum_prod]
  calc
    _ ≤ ∑' x : Site, F x * B := by
      apply he.prod.tsum_le_tsum _ (hs.mul_right B)
      intro x
      have heq : (fun y : Site => F x * F y * srwKernel (2 * m) (y - x)) =
          (fun y => F x * (F y * srwKernel (2 * m) (y - x))) := by funext y; ring
      rw [heq, tsum_mul_left]
      exact mul_le_mul_of_nonneg_left (hrow x) (hF x)
    _ = B * ∑' x : Site, F x := by rw [tsum_mul_right, mul_comm]

end Critical2DKPZ.Extensions.GffTangent
