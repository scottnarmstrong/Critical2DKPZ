/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.ChapmanKolmogorov
import Critical2DKPZ.Polymer.SmoothedCovariance
import Mathlib.Tactic

/-! # Support and normalization of smoothed endpoint distributions -/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.Smoothing

/-- The smoothed endpoint distribution is supported on the union of the two walk ranges. -/
theorem smoothedEndpointDist_eq_zero_of_not_mem (β : ℝ) {m n : ℕ}
    (z w : Site) (ω : Disorder)
    (hw : w ∉ (Polymer.endpoints z m).biUnion (fun y => Polymer.endpoints y (n - m))) :
    smoothedEndpointDist β m n z ω w = 0 := by
  classical
  let A := Polymer.endpoints z m
  let B := A.biUnion (fun y => Polymer.endpoints y (n - m))
  have hterm : ∀ y, srwKernel m (y - z) * pointToPoint β m (n - m) y w ω = 0 := by
    intro y
    by_cases hy : y ∈ A
    · have hwy : w ∉ Polymer.endpoints y (n - m) := by
        intro hreach
        exact hw (Finset.mem_biUnion.mpr ⟨y, hy, hreach⟩)
      rw [Polymer.pointToPoint_eq_zero_of_not_mem β m (n - m) y w ω hwy, mul_zero]
    · rw [Polymer.srwKernel_eq_zero_of_not_mem m z y hy, zero_mul]
  have hnum : (∑' y, srwKernel m (y - z) * pointToPoint β m (n - m) y w ω) = 0 := by
    calc
      _ = ∑' y, (0 : ℝ) := tsum_congr hterm
      _ = 0 := tsum_zero
  unfold smoothedEndpointDist
  rw [hnum, zero_div]

/-- Smoothed endpoint distributions have nonnegative site masses. -/
theorem smoothedEndpointDist_nonneg (β : ℝ) {m n : ℕ}
    (z w : Site) (ω : Disorder) :
    0 ≤ smoothedEndpointDist β m n z ω w := by
  classical
  let A := Polymer.endpoints z m
  have hq : ∀ y ∉ A, srwKernel m (y - z) = 0 := by
    intro y hy
    exact Polymer.srwKernel_eq_zero_of_not_mem m z y hy
  have hnum : (∑' y, srwKernel m (y - z) * pointToPoint β m (n - m) y w ω) =
      ∑ y ∈ A, srwKernel m (y - z) * pointToPoint β m (n - m) y w ω := by
    apply tsum_eq_sum
    intro y hy
    rw [hq y hy, zero_mul]
  unfold smoothedEndpointDist
  rw [hnum]
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro y hy
    exact mul_nonneg (Polymer.kernel_nonneg m (y - z))
      (Polymer.pointToPoint_nonneg β m (n - m) y w ω)
  · exact (Polymer.smoothedP2Plane_pos β m n z ω).le

/-- The smoothed endpoint distribution has total mass one. -/
theorem tsum_smoothedEndpointDist (β : ℝ) {m n : ℕ} (hmn : m ≤ n)
    (z : Site) (ω : Disorder) :
    ∑' w, smoothedEndpointDist β m n z ω w = 1 := by
  have hCK := profileP2Fun_srwKernel_eq_mul β hmn (Nat.le_refl n) z (fun _ => 1) ω
  have hflat : profileP2Fun β m n (fun w => srwKernel m (w - z)) (fun _ => 1) ω =
      smoothedP2Plane β m n z ω :=
    Polymer.profileP2Fun_srw_flat β m n z ω
  have hzero (ν : Site → ℝ) :
      profileP2Fun β n n ν (fun _ => 1) ω = ∑' w, ν w := by
    unfold profileP2Fun
    simp [Polymer.pointToPoint_eq_sum]
  rw [hflat, hzero] at hCK
  exact (mul_eq_left₀ (Polymer.smoothedP2Plane_pos β m n z ω).ne').mp hCK.symm

/-- Endpoint distributions are finitely supported probability profiles. -/
theorem endpointDist_probability (β : ℝ) (n : ℕ) (z : Site) (ω : Disorder) :
    (∀ w ∉ Polymer.endpoints z n, endpointDist β n z ω w = 0) ∧
    (∀ w, 0 ≤ endpointDist β n z ω w) ∧
    (∑ w ∈ Polymer.endpoints z n, endpointDist β n z ω w) = 1 := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    exact Polymer.endpointDist_eq_zero_of_not_mem β n z w ω hw
  · intro w
    exact Polymer.endpointDist_nonneg β n z w ω
  · calc
      (∑ w ∈ Polymer.endpoints z n, endpointDist β n z ω w) =
          ∑' w, endpointDist β n z ω w := by
            symm
            exact tsum_eq_sum fun w hw =>
              Polymer.endpointDist_eq_zero_of_not_mem β n z w ω hw
      _ = 1 := Polymer.tsum_endpointDist β n z ω

/-- Smoothed endpoint distributions are finitely supported probability profiles. -/
theorem smoothedEndpointDist_probability (β : ℝ) {m n : ℕ} (hmn : m ≤ n)
    (z : Site) (ω : Disorder) :
    (∀ w ∉ (Polymer.endpoints z m).biUnion (fun y => Polymer.endpoints y (n - m)),
      smoothedEndpointDist β m n z ω w = 0) ∧
    (∀ w, 0 ≤ smoothedEndpointDist β m n z ω w) ∧
    (∑ w ∈ (Polymer.endpoints z m).biUnion (fun y => Polymer.endpoints y (n - m)),
      smoothedEndpointDist β m n z ω w) = 1 := by
  classical
  let A := (Polymer.endpoints z m).biUnion (fun y => Polymer.endpoints y (n - m))
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    exact smoothedEndpointDist_eq_zero_of_not_mem β z w ω (by simpa [A] using hw)
  · intro w
    exact smoothedEndpointDist_nonneg β z w ω
  · calc
      (∑ w ∈ A, smoothedEndpointDist β m n z ω w) =
          ∑' w, smoothedEndpointDist β m n z ω w := by
            symm
            exact tsum_eq_sum fun w hw =>
              smoothedEndpointDist_eq_zero_of_not_mem β z w ω (by simpa [A] using hw)
      _ = 1 := tsum_smoothedEndpointDist β hmn z ω

end Critical2DKPZ.Smoothing

end
