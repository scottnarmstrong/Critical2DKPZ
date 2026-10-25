/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.HeatKernel
public import Critical2DKPZ.Definitions.SiteToPlane
public import Critical2DKPZ.RandomWalk.Port.Walk.GaussianFourier
public import Critical2DKPZ.RandomWalk.Port.Walk.SRW
import Mathlib

/-!
# Gaussian normalization and parity bridges in dimension two

The product Gaussian at time `t` has coordinate variance `t/2`, hence equals
the heat kernel at time `t/2`. Graph distance has coordinate-sum parity.
-/

@[expose] public section

namespace Critical2DKPZ

/-- The squared Euclidean norm of a lattice site is the sum of coordinate squares. -/
theorem norm_siteToPlane_sq (z : Site) :
    ‖siteToPlane z‖ ^ 2 = (z 0 : ℝ) ^ 2 + (z 1 : ℝ) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  rfl

/-- The product Gaussian has the normalization of the planar heat kernel. -/
theorem ctGauss_two_eq_heatKernel {t : ℝ} (ht : 0 < t) (z : Site) :
    LatticeProb.ContinuousTime.ctGauss 2 t z = heatKernel (t / 2) (siteToPlane z) := by
  unfold LatticeProb.ContinuousTime.ctGauss
  rw [Fin.prod_univ_two]
  simp only [LatticeProb.ContinuousTime.lineGauss, Nat.cast_ofNat]
  unfold heatKernel
  rw [norm_siteToPlane_sq]
  have hA : 0 ≤ 2 * Real.pi * (t / 2) := by positivity
  calc
    (Real.sqrt (2 * Real.pi * (t / 2)))⁻¹ * Real.exp (-(z 0 : ℝ) ^ 2 / (2 * (t / 2))) *
        ((Real.sqrt (2 * Real.pi * (t / 2)))⁻¹ *
          Real.exp (-(z 1 : ℝ) ^ 2 / (2 * (t / 2))))
      = (Real.sqrt (2 * Real.pi * (t / 2)) ^ 2)⁻¹ *
          Real.exp (-(z 0 : ℝ) ^ 2 / (2 * (t / 2)) +
            -(z 1 : ℝ) ^ 2 / (2 * (t / 2))) := by rw [Real.exp_add]; ring
    _ = (2 * Real.pi * (t / 2))⁻¹ *
          Real.exp (-((z 0 : ℝ) ^ 2 + (z 1 : ℝ) ^ 2) / (2 * (t / 2))) := by
      rw [Real.sq_sqrt hA]
      congr 2
      ring

/-- The parity condition is exactly the graph-distance parity condition. -/
theorem graphNorm_parity_of_even {n : ℕ} {z : Site} (hz : Even (z 0 + z 1 + n)) :
    (LatticeProb.graphNorm z : ZMod 2) = (n : ZMod 2) := by
  rw [LatticeProb.graphNorm_cast_zmod, Fin.sum_univ_two]
  obtain ⟨k, hk⟩ := hz
  have h : ((z 0 : ZMod 2) + (z 1 : ZMod 2)) + (n : ZMod 2) = 0 := by
    have he := congrArg (fun a : ℤ => (a : ZMod 2)) hk
    simpa only [Int.cast_add, Int.cast_natCast, CharTwo.add_self_eq_zero] using he
  have he := congrArg (fun a : ZMod 2 => a + (n : ZMod 2)) h
  simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add, Int.cast_add] using he

/-- Euclidean distance is bounded by graph distance. -/
theorem norm_siteToPlane_sq_le_graphNorm_sq (z : Site) :
    ‖siteToPlane z‖ ^ 2 ≤ (LatticeProb.graphNorm z : ℝ) ^ 2 := by
  rw [norm_siteToPlane_sq, LatticeProb.graphNorm, Fin.sum_univ_two]
  push_cast
  have hc0 : ((z 0).natAbs : ℝ) = |(z 0 : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have hc1 : ((z 1).natAbs : ℝ) = |(z 1 : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [hc0, hc1]
  nlinarith only [sq_abs (z 0 : ℝ), sq_abs (z 1 : ℝ),
    mul_nonneg (abs_nonneg (z 0 : ℝ)) (abs_nonneg (z 1 : ℝ))]

/-- Absorbing the fixed four-step shift in the Gaussian denominator. -/
theorem gaussian_exponent_le {A B t : ℝ} (ht : 1 ≤ t) (hB : 0 ≤ B) (hBA : B ≤ A) :
    -A / (8 * (t + 4)) ≤ -(1 / 40 : ℝ) * B / t := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  rw [div_le_div_iff₀ (by positivity) ht0]
  nlinarith only [mul_nonneg hB (sub_nonneg.mpr ht),
    mul_nonneg (sub_nonneg.mpr hBA) ht0.le]

end Critical2DKPZ
