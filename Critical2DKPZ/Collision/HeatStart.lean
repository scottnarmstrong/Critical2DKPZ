/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.SmoothedCovariance
import Mathlib.Tactic

/-! # First-collision identity for heat starts of unequal widths

The two free initial walks may have different ages.  Their collision kernel retains the sum of
both ages and the doubled time elapsed in the interacting slab.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.Collision

open Critical2DKPZ.Polymer

/-- Convolution of two possibly different heat starts against a third walk kernel. -/
theorem kernel_mixed_sandwich (m l k : ℕ) (x y : Site) :
    (∑ u ∈ endpoints x m, ∑ v ∈ endpoints y l,
      srwKernel m (u - x) * srwKernel l (v - y) * srwKernel k (v - u)) =
      srwKernel (m + l + k) (y - x) := by
  have hinner (u : Site) :
      (∑ v ∈ endpoints y l,
        srwKernel l (v - y) * srwKernel k (v - u)) =
        srwKernel (l + k) (u - y) := by
    calc
      _ = ∑ v ∈ endpoints y l,
          srwKernel l (v - y) * srwKernel k (u - v) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [srwKernel_sub_swap k v u]
      _ = srwKernel (l + k) (u - y) := kernel_convolution_finset l k y u
  calc
    _ = ∑ u ∈ endpoints x m,
        srwKernel m (u - x) * srwKernel (l + k) (u - y) := by
      apply Finset.sum_congr rfl
      intro u hu
      calc
        _ = ∑ v ∈ endpoints y l,
            srwKernel m (u - x) *
              (srwKernel l (v - y) * srwKernel k (v - u)) := by
          apply Finset.sum_congr rfl
          intro v hv
          ring
        _ = srwKernel m (u - x) *
            ∑ v ∈ endpoints y l,
              srwKernel l (v - y) * srwKernel k (v - u) := by rw [Finset.mul_sum]
        _ = _ := by rw [hinner]
    _ = ∑ u ∈ endpoints x m,
        srwKernel m (u - x) * srwKernel (l + k) (y - u) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [srwKernel_sub_swap (l + k) u y]
    _ = srwKernel (m + (l + k)) (y - x) := kernel_convolution_finset m (l + k) x y
    _ = srwKernel (m + l + k) (y - x) := by
      congr 1
      omega

/-- Polarized first-selected-collision formula for two heat starts with unequal widths.

The noise interval is `(a,a+n]`, so the terminal slice is included. -/
theorem heatStart_mixed_firstCollision (β : ℝ) (a n m l : ℕ) (x y : Site) :
    (∫ ω, profileP2Fun β a (a + n)
        (fun u => srwKernel m (u - x)) (fun _ => 1) ω *
      profileP2Fun β a (a + n)
        (fun v => srwKernel l (v - y)) (fun _ => 1) ω ∂disorderLaw) - 1 =
      ∑ r ∈ Finset.Icc 1 n,
        srwKernel (m + l + 2 * r) (y - x) * sigmaSq β *
          (∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw) := by
  have h := probability_profile_firstCollision_finset β a n
    (fun u => srwKernel m (u - x)) (fun v => srwKernel l (v - y))
    (endpoints x m) (endpoints y l)
    (fun u hu => srwKernel_eq_zero_of_not_mem m x u hu)
    (fun v hv => srwKernel_eq_zero_of_not_mem l y v hv)
    (sum_srwKernel_endpoints m x) (sum_srwKernel_endpoints l y)
  rw [h]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← kernel_mixed_sandwich m l (2 * r) x y]
  simp_rw [Finset.sum_mul]

end Critical2DKPZ.Collision

end
