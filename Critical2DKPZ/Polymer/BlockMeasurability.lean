/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.Locality
public import Critical2DKPZ.Polymer.SmoothedCovariance
public import Critical2DKPZ.Definitions.EndpointDist
public import Critical2DKPZ.Definitions.SmoothedEndpointDist
import Mathlib.Tactic

/-! # Block locality of averaged partition functions and endpoint distributions -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.Polymer

/-- The profile-tested partition function is measurable with respect to its disorder block. -/
theorem measurable_profileP2Fun_block (β : ℝ) (a b : ℕ) (hab : a ≤ b)
    (ν f : Site → ℝ) :
    Measurable[Gaussian.disorderBlock a b] (profileP2Fun β a b ν f) := by
  let : MeasurableSpace Disorder := Gaussian.disorderBlock a b
  have hp (w z : Site) :
      Measurable[Gaussian.disorderBlock a b] (pointToPoint β a (b - a) w z) := by
    convert measurable_pointToPoint_block β a (b - a) w z using 1
    rw [Nat.add_sub_of_le hab]
  unfold profileP2Fun
  exact Measurable.tsum fun w => measurable_const.mul
    (Measurable.tsum fun z => (hp w z).mul_const _)

/-- The smoothed partition function is measurable with respect to its disorder block. -/
theorem measurable_smoothedP2Plane_block (β : ℝ) (s n : ℕ) (hs : s ≤ n) (x : Site) :
    Measurable[Gaussian.disorderBlock s n] (smoothedP2Plane β s n x) := by
  have heq : smoothedP2Plane β s n x =
      profileP2Fun β s n (fun y => srwKernel s (y - x)) (fun _ => 1) := by
    funext ω
    exact (profileP2Fun_srw_flat β s n x ω).symm
  rw [heq]
  exact measurable_profileP2Fun_block β s n hs _ _

/-- The polymer endpoint distribution is measurable. -/
theorem measurable_endpointDist (β : ℝ) (n : ℕ) (w z : Site) :
    Measurable (fun ω => endpointDist β n w ω z) :=
  (measurable_pointToPoint β 0 n w z).div (measurable_pointToPlane β 0 n w)

/-- The endpoint distribution is measurable with respect to the past disorder. -/
theorem measurable_endpointDist_past (β : ℝ) (n : ℕ) (w z : Site) :
    Measurable[disorderPast n] (fun ω => endpointDist β n w ω z) :=
  (measurable_pointToPoint_past β n w z).div (measurable_pointToPlane_past β n w)

/-- The smoothed polymer endpoint distribution is measurable. -/
theorem measurable_smoothedEndpointDist (β : ℝ) (m n : ℕ) (x w : Site) :
    Measurable (fun ω => smoothedEndpointDist β m n x ω w) := by
  unfold smoothedEndpointDist
  apply Measurable.div
  · exact Measurable.tsum fun y =>
      measurable_const.mul (measurable_pointToPoint β m (n - m) y w)
  · exact measurable_smoothedP2Plane β m n x

/-- The smoothed endpoint distribution is measurable with respect to its disorder block. -/
theorem measurable_smoothedEndpointDist_block (β : ℝ) (m n : ℕ)
    (hmn : m ≤ n) (x w : Site) :
    Measurable[Gaussian.disorderBlock m n] (fun ω => smoothedEndpointDist β m n x ω w) := by
  let : MeasurableSpace Disorder := Gaussian.disorderBlock m n
  have hp (y : Site) :
      Measurable[Gaussian.disorderBlock m n] (pointToPoint β m (n - m) y w) := by
    convert measurable_pointToPoint_block β m (n - m) y w using 1
    rw [Nat.add_sub_of_le hmn]
  unfold smoothedEndpointDist
  exact (Measurable.tsum fun y => measurable_const.mul (hp y)).div
    (measurable_smoothedP2Plane_block β m n hmn x)

end Critical2DKPZ.Polymer
