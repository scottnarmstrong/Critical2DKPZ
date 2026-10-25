/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.Endpoints
public import Critical2DKPZ.Smoothing.TimeShiftEnvironment
import Mathlib.Tactic

/-! # The smoothed profile as a time-shifted profile pairing -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

/-- Reindexing the disorder times identifies the point-to-plane partition
function after a common time shift. -/
theorem pointToPlane_timeShift (β : ℝ) (d n : ℕ) (w : Site) (ω : Disorder) :
    pointToPlane β d n w ω =
      pointToPlane β 0 n w (Smoothing.shiftEnvironment d ω) := by
  rw [Polymer.pointToPlane_eq_sum, Polymer.pointToPlane_eq_sum]
  apply Finset.sum_congr rfl
  intro s hs
  exact congrArg (fun z => (4 : ℝ)⁻¹ ^ n * z)
    (by simpa only [Nat.add_zero] using Smoothing.pathWeight_timeShift β d 0 w s ω)

/-- The smoothed observable is a profile pairing after shifting the environment past its initial smoothing interval. -/
theorem smoothedP2Plane_eq_profileP2Fun_shift (β : ℝ) {s n : ℕ} (_hsn : s ≤ n) (ω : Disorder) :
    smoothedP2Plane β s n 0 ω =
      profileP2Fun β 0 (n - s) (fun y => srwKernel s y) (fun _ => 1)
        (Smoothing.shiftEnvironment s ω) := by
  have hsum :
      (∑' y : Site, srwKernel s y *
        pointToPlane β 0 (n - s) y (Smoothing.shiftEnvironment s ω)) =
      ∑ y ∈ Polymer.endpoints 0 s, srwKernel s y *
        pointToPlane β 0 (n - s) y (Smoothing.shiftEnvironment s ω) := by
    apply tsum_eq_sum
    intro y hy
    have hz := Polymer.srwKernel_eq_zero_of_not_mem s 0 y hy
    have hz' : srwKernel s y = 0 := by simpa only [sub_zero] using hz
    rw [hz', zero_mul]
  calc
    smoothedP2Plane β s n 0 ω =
        ∑ y ∈ Polymer.endpoints 0 s, srwKernel s y *
          pointToPlane β 0 (n - s) y (Smoothing.shiftEnvironment s ω) := by
      rw [Polymer.smoothedP2Plane_eq_sum]
      apply Finset.sum_congr rfl
      intro y hy
      simp only [sub_zero]
      rw [pointToPlane_timeShift]
    _ = ∑' y : Site, srwKernel s y *
          pointToPlane β 0 (n - s) y (Smoothing.shiftEnvironment s ω) := hsum.symm
    _ = profileP2Fun β 0 (n - s) (fun y => srwKernel s y) (fun _ => 1)
          (Smoothing.shiftEnvironment s ω) := by
      unfold profileP2Fun
      simp only [mul_one]
      congr 1
      funext y
      rw [← Polymer.tsum_pointToPoint]
      simp only [Nat.sub_zero]

end Critical2DKPZ.MomentBounds
