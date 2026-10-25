/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.ProfileCovariance
import Mathlib.Tactic

/-! Smoothed polymer partition functions satisfy exact first-collision and local two-replica identities. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.Polymer

/-- The walk-kernel convolution identity holds as a finite endpoint sum. -/
theorem kernel_convolution_finset (n k : ℕ) (w v : Site) :
    (∑ x ∈ endpoints w n, srwKernel n (x - w) * srwKernel k (v - x)) =
      srwKernel (n + k) (v - w) := by
  rw [srwKernel_convolution]
  symm
  apply tsum_eq_sum
  intro x hx
  rw [srwKernel_eq_zero_of_not_mem n w x hx, zero_mul]

/-- Sandwiching a kernel between walk kernels adds their time durations. -/
theorem kernel_sandwich (s k : ℕ) (w v : Site) :
    (∑ x ∈ endpoints w s, ∑ y ∈ endpoints v s,
      srwKernel s (x - w) * srwKernel s (y - v) * srwKernel k (y - x)) =
      srwKernel (2 * s + k) (v - w) := by
  have hinner (x : Site) :
      (∑ y ∈ endpoints v s, srwKernel s (x - w) *
          srwKernel s (y - v) * srwKernel k (y - x)) =
        srwKernel s (x - w) * srwKernel (s + k) (x - v) := by
    calc
      _ = srwKernel s (x - w) *
          ∑ y ∈ endpoints v s, srwKernel s (y - v) * srwKernel k (x - y) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        rw [srwKernel_sub_swap k y x, mul_assoc]
      _ = _ := by rw [kernel_convolution_finset]
  simp_rw [hinner, srwKernel_sub_swap (s + k) _ v]
  rw [kernel_convolution_finset]
  congr 1
  omega

/-- A walk-kernel initial profile with flat terminal equals the smoothed partition function. -/
theorem profileP2Fun_srw_flat (β : ℝ) (s n : ℕ) (x : Site) (ω : Disorder) :
    profileP2Fun β s n (fun y => srwKernel s (y - x)) (fun _ => 1) ω =
      smoothedP2Plane β s n x ω := by
  unfold profileP2Fun smoothedP2Plane
  simp only [mul_one, tsum_pointToPoint]

/-- The mixed second moment of smoothed partition functions has a first-collision expansion. -/
theorem smoothedP2Plane_firstCollision (β : ℝ) (s n : ℕ) (hs : s ≤ n) (x y : Site) :
    (∫ ω, smoothedP2Plane β s n x ω * smoothedP2Plane β s n y ω ∂disorderLaw) - 1 =
      ∑ r ∈ Finset.Icc 1 (n - s), srwKernel (2 * (s + r)) (y - x) *
        sigmaSq β * (∫ ω, pointToPlane β 0 (n - s - r) 0 ω ^ 2 ∂disorderLaw) := by
  have h := probability_profile_firstCollision_finset β s (n - s)
    (fun w => srwKernel s (w - x)) (fun v => srwKernel s (v - y))
    (endpoints x s) (endpoints y s)
    (fun w hw => srwKernel_eq_zero_of_not_mem s x w hw)
    (fun v hv => srwKernel_eq_zero_of_not_mem s y v hv)
    (sum_srwKernel_endpoints s x) (sum_srwKernel_endpoints s y)
  simp only [Nat.add_sub_of_le hs, profileP2Fun_srw_flat] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = (∑ w ∈ endpoints x s, ∑ v ∈ endpoints y s,
          srwKernel s (w - x) * srwKernel s (v - y) * srwKernel (2 * r) (v - w)) *
        sigmaSq β * (∫ ω, pointToPlane β 0 (n - s - r) 0 ω ^ 2 ∂disorderLaw) := by
      simp only [Finset.sum_mul]
    _ = _ := by
      rw [kernel_sandwich]
      congr 3
      omega

/-- Shifting a finite integer interval reindexes its sum. -/
theorem sum_Icc_shift (s m : ℕ) (f : ℕ → ℝ) :
    (∑ r ∈ Finset.Icc 1 m, f (s + r)) =
      ∑ r ∈ Finset.Icc (s + 1) (s + m), f r := by
  apply Finset.sum_bij (fun r _ => s + r)
  · intro r hr
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hr
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  · intro r hr r' hr' heq
    omega
  · intro r hr
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hr
    exact ⟨r - s, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩
  · intro r _
    rfl

/-- The mixed smoothed second moment equals the local two-replica collision formula. -/
theorem local_replica_formula (β : ℝ) (s n : ℕ) (hs : s ≤ n) (x y : Site) :
    (∫ ω, smoothedP2Plane β s n x ω * smoothedP2Plane β s n y ω ∂disorderLaw) - 1 =
      ∑ r ∈ Finset.Icc (s + 1) n, srwKernel (2 * r) (y - x) *
        sigmaSq β * (∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw) := by
  rw [smoothedP2Plane_firstCollision β s n hs]
  have h := sum_Icc_shift s (n - s) (fun r =>
    srwKernel (2 * r) (y - x) * sigmaSq β *
      (∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw))
  rw [Nat.add_sub_of_le hs] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro r _
  rw [Nat.sub_add_eq]

end Critical2DKPZ.Polymer
