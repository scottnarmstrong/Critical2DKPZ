/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.ChapmanKolmogorov
public import Critical2DKPZ.FutureProfiles.Basic
import Mathlib.Tactic

/-! # The profile of a smoothed endpoint law -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.FutureProfiles

private theorem endpoints_add {m n : ℕ} {x y z : Site}
    (hy : y ∈ Polymer.endpoints x m) (hz : z ∈ Polymer.endpoints y n) :
    z ∈ Polymer.endpoints x (m + n) := by
  apply (Polymer.mem_endpoints_iff x z (m + n)).2
  obtain ⟨s, hs⟩ := (Polymer.mem_endpoints_iff x y m).1 hy
  obtain ⟨t, ht⟩ := (Polymer.mem_endpoints_iff y z n).1 hz
  exact ⟨Fin.append s t, by rw [Polymer.walkPosition_append_end, hs, ht]⟩

/-- The profile of a smoothed endpoint law is the ratio of its smoothed masses. -/
theorem profileP2Fun_smoothedEndpointDist_eq_div (β : ℝ) {m n N : ℕ}
    (hmn : m ≤ n) (hnN : n ≤ N) (x : Site) (ω : Disorder) :
    profileP2Fun β n N (smoothedEndpointDist β m n x ω) (fun _ => 1) ω =
      smoothedP2Plane β m N x ω / smoothedP2Plane β m n x ω := by
  let A : Finset Site := Polymer.endpoints x m
  let S : Finset Site := Polymer.endpoints x n
  let den : ℝ := smoothedP2Plane β m n x ω
  let num (z : Site) : ℝ :=
    ∑' y, srwKernel m (y - x) * pointToPoint β m (n - m) y z ω
  have hden : 0 < den := by
    dsimp [den]
    exact Polymer.smoothedP2Plane_pos β m n x ω
  have hnum (z : Site) :
      num z = ∑ y ∈ A,
        srwKernel m (y - x) * pointToPoint β m (n - m) y z ω := by
    dsimp [num, A]
    apply tsum_eq_sum
    intro y hy
    rw [Polymer.srwKernel_eq_zero_of_not_mem m x y hy]
    simp
  have hprofileSupport : ∀ z ∉ S, smoothedEndpointDist β m n x ω z = 0 := by
    intro z hz
    unfold smoothedEndpointDist
    have hnumzero : num z = 0 := by
      rw [hnum]
      apply Finset.sum_eq_zero
      intro y hy
      have hznot : z ∉ Polymer.endpoints y (n - m) := by
        intro hreach
        apply hz
        have hadd := endpoints_add hy hreach
        simpa [Nat.add_sub_of_le hmn] using hadd
      rw [Polymer.pointToPoint_eq_zero_of_not_mem β m (n - m) y z ω hznot]
      simp
    dsimp [num] at hnumzero
    rw [hnumzero, zero_div]
  have hdist (z : Site) :
      smoothedEndpointDist β m n x ω z = num z / den := by
    rfl
  have hconv (y : Site) (hy : y ∈ A) :
      (∑ z ∈ S,
        pointToPoint β m (n - m) y z ω * pointToPlane β n (N - n) z ω) =
        pointToPlane β m (N - m) y ω := by
    let B : Finset Site := Polymer.endpoints y (n - m)
    have hBsub : B ⊆ S := by
      intro z hz
      have hadd := endpoints_add (by simpa [A] using hy) (by simpa [B] using hz)
      simpa [S, Nat.add_sub_of_le hmn] using hadd
    have hfinite :
        (∑ z ∈ S,
          pointToPoint β m (n - m) y z ω * pointToPlane β n (N - n) z ω) =
        ∑ z ∈ B,
          pointToPoint β m (n - m) y z ω * pointToPlane β n (N - n) z ω := by
      symm
      apply Finset.sum_subset hBsub
      intro z hzS hzB
      rw [Polymer.pointToPoint_eq_zero_of_not_mem β m (n - m) y z ω (by simpa [B] using hzB)]
      simp
    have htsum :
        (∑ z ∈ B,
          pointToPoint β m (n - m) y z ω * pointToPlane β n (N - n) z ω) =
        ∑' z,
          pointToPoint β m (n - m) y z ω * pointToPlane β n (N - n) z ω := by
      symm
      apply tsum_eq_sum
      intro z hz
      rw [Polymer.pointToPoint_eq_zero_of_not_mem β m (n - m) y z ω (by simpa [B] using hz)]
      simp
    have hCK := Polymer.pointToPlane_chapmanKolmogorov β m (n - m) (N - n) y ω
    have htimes : m + (n - m) = n ∧ (n - m) + (N - n) = N - m := by omega
    rw [htimes.1, htimes.2] at hCK
    exact hfinite.trans (htsum.trans hCK.symm)
  have htotal :
      (∑ z ∈ S, num z * pointToPlane β n (N - n) z ω) =
        smoothedP2Plane β m N x ω := by
    have hnumFun : num = fun z =>
        ∑ y ∈ A, srwKernel m (y - x) * pointToPoint β m (n - m) y z ω := by
      funext z
      exact hnum z
    rw [hnumFun]
    change (∑ z ∈ S,
        (∑ y ∈ A, srwKernel m (y - x) * pointToPoint β m (n - m) y z ω) *
          pointToPlane β n (N - n) z ω) = _
    calc
      _ = ∑ z ∈ S, ∑ y ∈ A,
          srwKernel m (y - x) * pointToPoint β m (n - m) y z ω *
            pointToPlane β n (N - n) z ω := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [Finset.sum_mul]
      _ = ∑ y ∈ A, ∑ z ∈ S,
          srwKernel m (y - x) * pointToPoint β m (n - m) y z ω *
            pointToPlane β n (N - n) z ω := by
          rw [Finset.sum_comm]
      _ = ∑ y ∈ A,
          srwKernel m (y - x) *
            (∑ z ∈ S,
              pointToPoint β m (n - m) y z ω * pointToPlane β n (N - n) z ω) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z hz
          ring
      _ = ∑ y ∈ A, srwKernel m (y - x) * pointToPlane β m (N - m) y ω := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [hconv y hy]
      _ = smoothedP2Plane β m N x ω := by
          symm
          exact Polymer.smoothedP2Plane_eq_sum β m N x ω
  have hprofile :
      profileP2Fun β n N (smoothedEndpointDist β m n x ω) (fun _ => 1) ω =
        (∑ z ∈ S, num z * pointToPlane β n (N - n) z ω) / den := by
    rw [Polymer.profileP2Fun_eq_sum β n N (smoothedEndpointDist β m n x ω)
      (fun _ => 1) S hprofileSupport ω]
    simp only [mul_one, Polymer.tsum_pointToPoint]
    calc
      _ = ∑ z ∈ S, (num z * pointToPlane β n (N - n) z ω) / den := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [hdist]
          field_simp [ne_of_gt hden]
      _ = _ := by rw [Finset.sum_div]
  rw [hprofile, htotal]

end Critical2DKPZ.FutureProfiles

end
