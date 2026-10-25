/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.TwoCoordinateKernel
import Mathlib.Tactic

/-! # Uniform finite sums for the two-coordinate LZ21 kernel -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- The two-coordinate row sum is uniform in its common reference site. -/
theorem sum_twoCoordinateKernel_le {L a p : ℝ} (hL : 1 ≤ L) (ha : 0 < a)
    (hp : 0 < p) (hap : a * p < 1) (u : Site) (s : Finset (Site × Site)) :
    (∑ v ∈ s, twoCoordinateKernel L a p u v) ≤
      1188 * L ^ (-(a * p)) / (a * p * (1 - a * p)) := by
  let E := pairSumDifference u
  let T := s.image E
  let W := T.image Prod.fst
  let Z := T.image Prod.snd
  have hTsubset : T ⊆ W ×ˢ Z := by
    intro v hv
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ hv, Finset.mem_image_of_mem _ hv⟩
  have htrans_nonneg (v : Site × Site) : 0 ≤ transformedPairKernel L a p v := by
    unfold transformedPairKernel
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
  have hmap :
      (∑ v ∈ s, 4 * transformedPairKernel L a p (E v)) =
        ∑ v ∈ T, 4 * transformedPairKernel L a p v := by
    dsimp [T, E]
    symm
    exact Finset.sum_image (pairSumDifference_injective u).injOn
  have hsum_subset :
      (∑ v ∈ T, 4 * transformedPairKernel L a p v) ≤
        ∑ v ∈ W ×ˢ Z, 4 * transformedPairKernel L a p v :=
    Finset.sum_le_sum_of_subset_of_nonneg hTsubset (fun v _ _ =>
      mul_nonneg (by norm_num) (htrans_nonneg v))
  have hprod :
      (∑ v ∈ W ×ˢ Z, 4 * transformedPairKernel L a p v) =
        ∑ w ∈ W, ∑ z ∈ Z, 4 * transformedPairKernel L a p (w, z) := by
    simpa only [Prod.eta] using
      (Finset.sum_product' W Z (fun w z => 4 * transformedPairKernel L a p (w, z)))
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hweightNonneg (w : Site) :
      0 ≤ (1 + ‖siteToPlane w‖ ^ (2 * a)) ^ (-p) :=
    Real.rpow_nonneg (by positivity) _
  have hinner (w : Site) :
      (∑ z ∈ Z, 4 * transformedPairKernel L a p (w, z)) ≤
        36 * weightedLatticeKernel L 1 a p w := by
    let M := L + ‖siteToPlane w‖ ^ 2
    have hM : 1 ≤ M := by dsimp [M]; linarith [sq_nonneg (‖siteToPlane w‖)]
    have hz := sum_shifted_lattice_rpow_le hM (by norm_num : (2 : ℝ) ≤ 2)
      (0 : Site) Z
    have hz' : (∑ z ∈ Z, (M + ‖siteToPlane z‖ ^ 2) ^ (-2 : ℝ)) ≤ 9 * M ^ (-1 : ℝ) := by
      simpa [M, siteToPlane_zero, Real.rpow_neg_one,
        show (1 : ℝ) - 2 = -1 by norm_num] using hz
    have hfactor :
        (∑ z ∈ Z, 4 * transformedPairKernel L a p (w, z)) =
          4 * (1 + ‖siteToPlane w‖ ^ (2 * a)) ^ (-p) *
            ∑ z ∈ Z, (M + ‖siteToPlane z‖ ^ 2) ^ (-2 : ℝ) := by
      calc
        (∑ z ∈ Z, 4 * transformedPairKernel L a p (w, z)) =
            ∑ z ∈ Z, (4 * (1 + ‖siteToPlane w‖ ^ (2 * a)) ^ (-p)) *
              (M + ‖siteToPlane z‖ ^ 2) ^ (-2 : ℝ) := by
                apply Finset.sum_congr rfl
                intro z hz
                unfold transformedPairKernel
                simp only [M]
                ring
        _ = _ := by rw [← Finset.mul_sum]
    rw [hfactor]
    have hmul := mul_le_mul_of_nonneg_left hz'
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (hweightNonneg w))
    have hkernel : weightedLatticeKernel L 1 a p w =
        M ^ (-1 : ℝ) * (1 + ‖siteToPlane w‖ ^ (2 * a)) ^ (-p) := by
      simp [weightedLatticeKernel, M, Real.rpow_neg_one, mul_comm]
    rw [hkernel]
    calc
      4 * (1 + ‖siteToPlane w‖ ^ (2 * a)) ^ (-p) *
          ∑ z ∈ Z, (M + ‖siteToPlane z‖ ^ 2) ^ (-2 : ℝ) ≤
          4 * (1 + ‖siteToPlane w‖ ^ (2 * a)) ^ (-p) * (9 * M ^ (-1 : ℝ)) := hmul
      _ = 36 * (M ^ (-1 : ℝ) * (1 + ‖siteToPlane w‖ ^ (2 * a)) ^ (-p)) := by ring
  have hweighted := weighted_lattice_sum_bound hL (by norm_num : 1 ≤ (1 : ℝ)) ha hp hap
  have hfiniteW : (∑ w ∈ W, weightedLatticeKernel L 1 a p w) ≤
      33 * L ^ (-(a * p)) / (a * p * (1 - a * p)) := by
    simpa only [show (1 : ℝ) - 1 - a * p = -(a * p) by ring] using
      (hweighted.1.sum_le_tsum W
        (fun w _ => weightedLatticeKernel_nonneg (le_trans (by norm_num) hL) 1 a p w)).trans
        hweighted.2
  calc
    (∑ v ∈ s, twoCoordinateKernel L a p u v) ≤
        ∑ v ∈ s, 4 * transformedPairKernel L a p (E v) :=
      Finset.sum_le_sum fun v _ => twoCoordinateKernel_le_transformed hLpos u v
    _ = ∑ v ∈ T, 4 * transformedPairKernel L a p v := hmap
    _ ≤ ∑ v ∈ W ×ˢ Z, 4 * transformedPairKernel L a p v := hsum_subset
    _ = ∑ w ∈ W, ∑ z ∈ Z, 4 * transformedPairKernel L a p (w, z) := hprod
    _ ≤ ∑ w ∈ W, 36 * weightedLatticeKernel L 1 a p w :=
      Finset.sum_le_sum fun w _ => hinner w
    _ = 36 * ∑ w ∈ W, weightedLatticeKernel L 1 a p w := by rw [← Finset.mul_sum]
    _ ≤ 36 * (33 * L ^ (-(a * p)) / (a * p * (1 - a * p))) :=
      mul_le_mul_of_nonneg_left hfiniteW (by norm_num)
    _ = _ := by ring

end

end Critical2DKPZ.MomentBounds
