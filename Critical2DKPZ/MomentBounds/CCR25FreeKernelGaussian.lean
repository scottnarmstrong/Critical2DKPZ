/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.PairStratumBilinear
public import Critical2DKPZ.MomentBounds.CCR25Operators
public import Critical2DKPZ.Lattice.Basic
public import Critical2DKPZ.RandomWalk.Estimates
import Mathlib.Tactic

/-! # Gaussian upper bound for the CCR25 free replica kernel -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

/-- A finite sum of inverse squared positive times is at most two. -/
theorem ccr25_time_inverse_square_sum_le_two (L : ℕ) :
    (∑ n ∈ Finset.range L, ((n : ℝ) + 1)⁻¹ ^ 2) ≤ 2 := by
  have hstrong (L : ℕ) :
      (∑ n ∈ Finset.range (L + 1), ((n : ℝ) + 1)⁻¹ ^ 2) ≤
        2 - ((L : ℝ) + 1)⁻¹ := by
    induction L with
    | zero => norm_num
    | succ L ih =>
        have h1 : 0 < (L : ℝ) + 1 := by positivity
        have h2 : 0 < ((L + 1 : ℕ) : ℝ) + 1 := by positivity
        have harith :
            2 - ((L : ℝ) + 1)⁻¹ + (((L + 1 : ℕ) : ℝ) + 1)⁻¹ ^ 2 ≤
              2 - (((L + 1 : ℕ) : ℝ) + 1)⁻¹ := by
          push_cast
          field_simp [ne_of_gt h1, ne_of_gt h2]
          nlinarith
        have hsum :
            (∑ n ∈ Finset.range (L + 1), ((n : ℝ) + 1)⁻¹ ^ 2) +
                (((L + 1 : ℕ) : ℝ) + 1)⁻¹ ^ 2 ≤
              (2 - ((L : ℝ) + 1)⁻¹) + (((L + 1 : ℕ) : ℝ) + 1)⁻¹ ^ 2 :=
          by simpa only [add_comm] using
            (add_le_add_left ih ((((L + 1 : ℕ) : ℝ) + 1)⁻¹ ^ 2))
        calc
          (∑ n ∈ Finset.range (L + 1 + 1), ((n : ℝ) + 1)⁻¹ ^ 2) =
              (∑ n ∈ Finset.range (L + 1), ((n : ℝ) + 1)⁻¹ ^ 2) +
                (((L + 1 : ℕ) : ℝ) + 1)⁻¹ ^ 2 := by
                  rw [Finset.sum_range_succ]
          _ ≤ (2 - ((L : ℝ) + 1)⁻¹) +
                (((L + 1 : ℕ) : ℝ) + 1)⁻¹ ^ 2 := hsum
          _ ≤ 2 - (((L + 1 : ℕ) : ℝ) + 1)⁻¹ := harith
  by_cases hL : L = 0
  · simp [hL]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hL
    have h := hstrong k
    have hpos : 0 ≤ ((k : ℝ) + 1)⁻¹ := by positivity
    simpa using le_trans h (by linarith)

/-- The Gaussian one-walk estimate tensorizes over the replicas, including
the CCR collision indicators. The constants are the one-walk constants and
do not depend on the number of replicas, the collision partitions, or the
initial and terminal configurations. -/
theorem freeReplicaKernel_gaussian_bound :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
      ∀ {h : ℕ} (n : ℕ), 1 ≤ n →
        ∀ I J : ReplicaPartition h, ∀ z x : LatticeConfiguration h,
          freeReplicaKernel n I J z x ≤
            C ^ h / (n : ℝ) ^ h *
              Real.exp (-c * replicaDistanceEnergy z x / (n : ℝ)) := by
  obtain ⟨C, c, hc, hwalk⟩ := Critical2DKPZ.srwKernel_gaussianBound
  have hC : 0 ≤ C := by
    have hbase := hwalk 1 (by omega) (0 : Site)
    have hkernel : 0 ≤ Critical2DKPZ.srwKernel 1 (0 : Site) :=
      Critical2DKPZ.srwKernel_nonneg 1 0
    have hbound : Critical2DKPZ.srwKernel 1 (0 : Site) ≤ C := by
      have hz : Critical2DKPZ.siteToPlane (0 : Site) = 0 := by
        ext i
        simp [Critical2DKPZ.siteToPlane]
      simpa [hz] using hbase
    by_contra hC'
    have hCneg : C < 0 := lt_of_not_ge hC'
    linarith
  refine ⟨C, c, hC, hc, ?_⟩
  intro h n hn I J z x
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hcoord (i : Fin h) :
      Critical2DKPZ.srwKernel n (x i - z i) ≤
        C / (n : ℝ) *
          Real.exp (-c * ‖Critical2DKPZ.siteToPlane (x i - z i)‖ ^ 2 / (n : ℝ)) :=
    hwalk n hn (x i - z i)
  have hprod :
      (∏ i : Fin h, Critical2DKPZ.srwKernel n (x i - z i)) ≤
        ∏ i : Fin h, C / (n : ℝ) *
          Real.exp (-c * ‖Critical2DKPZ.siteToPlane (x i - z i)‖ ^ 2 / (n : ℝ)) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      exact Critical2DKPZ.srwKernel_nonneg n (x i - z i)
    · intro i hi
      exact hcoord i
  have hprod_eq :
      (∏ i : Fin h, C / (n : ℝ) *
        Real.exp (-c * ‖Critical2DKPZ.siteToPlane (x i - z i)‖ ^ 2 / (n : ℝ))) =
        C ^ h / (n : ℝ) ^ h *
          Real.exp (-c * replicaDistanceEnergy z x / (n : ℝ)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin, ← Real.exp_sum]
    have henergy :
        (∑ i : Fin h,
          -c * ‖Critical2DKPZ.siteToPlane (x i - z i)‖ ^ 2 / (n : ℝ)) =
          -c * replicaDistanceEnergy z x / (n : ℝ) := by
      calc
        _ = (-c / (n : ℝ)) *
            ∑ i : Fin h, ‖Critical2DKPZ.siteToPlane (x i - z i)‖ ^ 2 := by
              calc
                _ = ∑ i : Fin h,
                    (-c / (n : ℝ)) *
                      ‖Critical2DKPZ.siteToPlane (x i - z i)‖ ^ 2 := by
                        apply Finset.sum_congr rfl
                        intro i hi
                        ring
                _ = _ := by rw [← Finset.mul_sum]
        _ = -c * replicaDistanceEnergy z x / (n : ℝ) := by
              simp only [replicaDistanceEnergy, replicaCoordinateEnergy]
              ring
    rw [henergy, div_pow]
  unfold freeReplicaKernel
  split_ifs with hcollision
  · exact hprod.trans_eq hprod_eq
  · positivity


end Critical2DKPZ.MomentBounds

end
