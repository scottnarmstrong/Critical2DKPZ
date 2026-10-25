/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.WeightedLatticeKernel
public import Critical2DKPZ.MomentBounds.WeightedRadialBound
public import Critical2DKPZ.MomentBounds.RadialSums
import Mathlib.Tactic

/-!
# The weighted lattice estimate of LZ21 Lemma A.1

The positive domain 0 < a p < 1 is explicit. An elementary shell comparison
provides the safe numerical constant 33 uniformly in all parameters. The
endpoint r=1 is included, and summability is part of the conclusion.
-/

public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

/-- On each lattice shell, the weighted kernel with denominator power one is bounded by its radial envelope. -/
theorem weightedLatticeKernel_one_le_shell {L a p : ℝ} (hL : 0 < L) (ha : 0 < a)
    (hp : 0 < p) {z : Site} {k : ℕ} (hz : z ∈ latticeShell k) :
    weightedLatticeKernel L 1 a p z ≤
      ((k : ℝ) + 1) ^ (-(2 * (a * p))) / (L + ((k : ℝ) + 1) ^ 2) := by
  have hnorm := norm_sq_ge_of_mem_latticeShell hz
  push_cast at hnorm
  have hfree : (L + ‖siteToPlane z‖ ^ 2) ^ (-(1 : ℝ)) ≤
      (L + ((k : ℝ) + 1) ^ 2) ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (add_le_add le_rfl hnorm) (by norm_num)
  calc
    _ ≤ (L + ((k : ℝ) + 1) ^ 2) ^ (-(1 : ℝ)) *
        ((k : ℝ) + 1) ^ (-(2 * (a * p))) :=
      mul_le_mul hfree (weight_le_shell ha hp hz) (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg (by positivity) _)
    _ = _ := by rw [Real.rpow_neg_one]; ring

/-- The weighted kernel with denominator power one satisfies the stated scale-dependent lattice-sum bound. -/
theorem sum_latticeBox_weighted_one_le {L a p : ℝ} (hL : 1 ≤ L) (ha : 0 < a)
    (hp : 0 < p) (hap : a * p < 1) (K : ℕ) :
    (∑ z ∈ latticeBox K, weightedLatticeKernel L 1 a p z) ≤
      33 * L ^ (-(a * p)) / (a * p * (1 - a * p)) := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hb : 0 < a * p := mul_pos ha hp
  have hden : 0 < a * p * (1 - a * p) := mul_pos hb (sub_pos.mpr hap)
  have hr := sum_latticeBox_le_radial (weightedLatticeKernel L 1 a p)
    (fun j => (j : ℝ) ^ (-(2 * (a * p))) / (L + (j : ℝ) ^ 2)) K
    (fun j z hz => by
      simpa only [Nat.cast_add_one] using weightedLatticeKernel_one_le_shell hLpos ha hp hz)
  rw [weightedLatticeKernel_origin L 1 a p ha] at hr
  have hid (j : ℕ) : (8 * ((j : ℝ) + 1)) *
      (((j + 1 : ℕ) : ℝ) ^ (-(2 * (a * p))) / (L + ((j + 1 : ℕ) : ℝ) ^ 2)) =
        8 * radialIntegrand L (1 - 2 * (a * p)) ((j : ℝ) + 1) := by
    have hj : 0 < (j : ℝ) + 1 := by positivity
    have he : ((j : ℝ) + 1) ^ (1 - 2 * (a * p)) =
        ((j : ℝ) + 1) * ((j : ℝ) + 1) ^ (-(2 * (a * p))) := by
      rw [sub_eq_add_neg, Real.rpow_add hj, Real.rpow_one]
    simp only [Nat.cast_add_one, radialIntegrand, he]
    ring
  simp_rw [hid] at hr
  rw [← Finset.mul_sum] at hr
  have hs := mul_le_mul_of_nonneg_left (sum_weighted_radial_bound hLpos hb hap K)
    (by norm_num : (0 : ℝ) ≤ 8)
  have ho : L ^ (-(1 : ℝ)) ≤ L ^ (-(a * p)) / (a * p * (1 - a * p)) := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hL (show -(1 : ℝ) ≤ -(a * p) by linarith only [hap])
    apply hpow.trans
    apply (le_div_iff₀ hden).mpr
    apply mul_le_of_le_one_right (Real.rpow_nonneg hLpos.le _)
    nlinarith only [sq_nonneg (a * p - 1 / 2)]
  calc
    _ ≤ L ^ (-(1 : ℝ)) + 8 *
        ∑ j ∈ Finset.range K, radialIntegrand L (1 - 2 * (a * p)) ((j : ℝ) + 1) := hr
    _ ≤ L ^ (-(a * p)) / (a * p * (1 - a * p)) +
        8 * (4 * L ^ (-(a * p)) / (a * p * (1 - a * p))) := add_le_add ho hs
    _ = _ := by ring

/-- The weighted lattice sum in LZ21 Lemma A.1 is bounded with constant 33 for `0 < a * p < 1`. -/
theorem weighted_lattice_sum_bound {L r a p : ℝ} (hL : 1 ≤ L) (hr : 1 ≤ r)
    (ha : 0 < a) (hp : 0 < p) (hap : a * p < 1) :
    Summable (weightedLatticeKernel L r a p) ∧
      (∑' z : Site, weightedLatticeKernel L r a p z) ≤
        33 * L ^ (1 - r - a * p) / (a * p * (1 - a * p)) := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  apply summable_and_tsum_le_of_latticeBox_bound (weightedLatticeKernel_nonneg hLpos.le r a p)
  intro K
  calc
    _ ≤ ∑ z ∈ latticeBox K, L ^ (1 - r) * weightedLatticeKernel L 1 a p z :=
      Finset.sum_le_sum fun z _ => weightedLatticeKernel_le_scaled_one hLpos hr a p z
    _ = L ^ (1 - r) * ∑ z ∈ latticeBox K, weightedLatticeKernel L 1 a p z :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ L ^ (1 - r) * (33 * L ^ (-(a * p)) / (a * p * (1 - a * p))) :=
      mul_le_mul_of_nonneg_left (sum_latticeBox_weighted_one_le hL ha hp hap K)
        (Real.rpow_nonneg hLpos.le _)
    _ = _ := by
      rw [show 1 - r - a * p = (1 - r) + -(a * p) by ring, Real.rpow_add hLpos]
      ring

end Critical2DKPZ.MomentBounds
