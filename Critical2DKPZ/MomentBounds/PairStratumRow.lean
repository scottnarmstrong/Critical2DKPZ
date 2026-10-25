/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.PairStratumKernel
import Mathlib.Tactic

/-! # The weighted LZ21 row estimate on a finite collision stratum -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- The full h-replica kernel with the two reciprocal collision weights used
in the LZ21 weighted-Hölder step. -/
def pairStratumWeightedKernel {h : ℕ} (a p : ℝ) (m n k l : Fin h)
    (x y : LatticeConfiguration h) : ℝ :=
  (1 + replicaDistanceEnergy x y) ^ (-((h : ℝ) - 1)) *
    (1 + ‖siteToPlane (x m - x n)‖ ^ (2 * a)) ^ p *
    (1 + ‖siteToPlane (y k - y l)‖ ^ (2 * a)) ^ (-p)

/-- The reduced denominator is bounded by four times the full denominator,
and this converts the weighted full kernel to the collision-profile kernel. -/
theorem pairStratum_weighted_le_profile {h : ℕ} (m n k l : Fin h)
    (hmn : m ≠ n) (hmk : m ≠ k) (hml : m ≠ l) (hkl : k ≠ l)
    (e : PairSpectatorLabels h m k l ≃ Fin (h - 3))
    {a p : ℝ}
    {x y : LatticeConfiguration h} (hxy : x k = x l) (hy : y m = y n) :
    pairStratumWeightedKernel a p m n k l x y ≤
      4 ^ ((h : ℝ) - 1) *
        (1 + ‖siteToPlane (x m - x n)‖ ^ (2 * a)) ^ p *
        collisionProfileKernel (1 + ‖siteToPlane (x m - x n)‖ ^ 2)
          ((h - 3 : ℕ) + 2) a p
          (fun j => x (e.symm j).val) (x k)
          (fun j => y (e.symm j).val) (y k, y l) := by
  let L : ℝ := 1 + ‖siteToPlane (x m - x n)‖ ^ 2
  let anchor : Fin (h - 3) → Site := fun j => x (e.symm j).val
  let z : Fin (h - 3) → Site := fun j => y (e.symm j).val
  let r : ℝ := (h : ℝ) - 1
  let R : ℝ := 1 + ‖siteToPlane (x m - x n)‖ ^ 2 +
    replicaEnergy anchor z + ‖siteToPlane (y k - x k)‖ ^ 2 +
      ‖siteToPlane (y l - x l)‖ ^ 2
  have hthree := three_le_of_distinct_labels m k l hmk hml hkl
  have hthreeR : (3 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hthree
  have hr : 0 < r := by dsimp [r]; linarith
  have hexp : ((h - 3 : ℕ) + 2 : ℝ) = r := by
    dsimp [r]
    rw [Nat.cast_sub hthree]
    norm_num
    ring
  have hden : R ≤ 4 * (1 + replicaDistanceEnergy x y) := by
    simpa [R, anchor, z, L] using
      pairProfileDenominator_le_four m n k l hmn hmk hml hkl e hy
  have hRpos : 0 < R := by
    dsimp [R]
    have henergy : 0 ≤ replicaEnergy anchor z := by
      unfold replicaEnergy
      apply Finset.sum_nonneg
      intro i hi
      exact sq_nonneg _
    positivity
  have hfullpos : 0 < 1 + replicaDistanceEnergy x y := by
    have hnonneg : 0 ≤ replicaDistanceEnergy x y := by
      unfold replicaDistanceEnergy
      apply Finset.sum_nonneg
      intro i hi
      exact sq_nonneg _
    positivity
  have hdiv : R / 4 ≤ 1 + replicaDistanceEnergy x y := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    linarith
  have hpow :
      (1 + replicaDistanceEnergy x y) ^ (-r) ≤ (R / 4) ^ (-r) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hdiv (by linarith)
  have hfour : (4 : ℝ) ^ (-r) = ((4 : ℝ) ^ r)⁻¹ := by
    rw [Real.rpow_neg_eq_inv_rpow, Real.inv_rpow (by norm_num) r]
  have hscale : (R / 4) ^ (-r) = 4 ^ r * R ^ (-r) := by
    rw [Real.div_rpow hRpos.le (by norm_num : (0 : ℝ) ≤ 4) (-r), hfour]
    field_simp
  have hfullpow :
      (1 + replicaDistanceEnergy x y) ^ (-r) ≤ 4 ^ r * R ^ (-r) :=
    hpow.trans_eq hscale
  have hbase :
      L + replicaEnergy anchor z + ‖siteToPlane (y k - x k)‖ ^ 2 +
          ‖siteToPlane (y l - x k)‖ ^ 2 = R := by
    dsimp [L, R, anchor, z]
    rw [hxy.symm]
  have hkernel :
      collisionProfileKernel L ((h - 3 : ℕ) + 2) a p anchor (x k) z (y k, y l) =
        R ^ (-r) * (1 + ‖siteToPlane (y k - y l)‖ ^ (2 * a)) ^ (-p) := by
    unfold collisionProfileKernel
    rw [hbase, hexp]
  have hA : 0 ≤ (1 + ‖siteToPlane (x m - x n)‖ ^ (2 * a)) ^ p := by
    positivity
  have hB : 0 ≤ (1 + ‖siteToPlane (y k - y l)‖ ^ (2 * a)) ^ (-p) := by
    positivity
  have hweight : 0 ≤
      (1 + ‖siteToPlane (x m - x n)‖ ^ (2 * a)) ^ p *
        (1 + ‖siteToPlane (y k - y l)‖ ^ (2 * a)) ^ (-p) :=
    mul_nonneg hA hB
  unfold pairStratumWeightedKernel
  dsimp [r]
  calc
    _ = (1 + replicaDistanceEnergy x y) ^ (-r) *
        ((1 + ‖siteToPlane (x m - x n)‖ ^ (2 * a)) ^ p *
          (1 + ‖siteToPlane (y k - y l)‖ ^ (2 * a)) ^ (-p)) := by ring
    _ ≤ (4 ^ r * R ^ (-r)) *
        ((1 + ‖siteToPlane (x m - x n)‖ ^ (2 * a)) ^ p *
          (1 + ‖siteToPlane (y k - y l)‖ ^ (2 * a)) ^ (-p)) :=
      mul_le_mul_of_nonneg_right hfullpow hweight
    _ = 4 ^ r * (1 + ‖siteToPlane (x m - x n)‖ ^ (2 * a)) ^ p *
        collisionProfileKernel L ((h - 3 : ℕ) + 2) a p anchor (x k) z (y k, y l) := by
      rw [hkernel]
      ring

/-- The full weighted row sum is uniform in its finite support and cutoff. -/
theorem sum_pairStratum_weightedKernel_le {h : ℕ} (m n k l : Fin h)
    (hmn : m ≠ n) (hmk : m ≠ k) (hml : m ≠ l) (hkl : k ≠ l)
    (e : PairSpectatorLabels h m k l ≃ Fin (h - 3))
    {a p : ℝ} (ha : 0 < a) (hp : 0 < p) (hap : a * p < 1)
    (x : LatticeConfiguration h) (hxy : x k = x l)
    (s : Finset (LatticeConfiguration h)) (K : ℕ)
    (hcollision : ∀ y ∈ s, y m = y n)
    (hbox : ∀ y ∈ s, ∀ i, y i ∈ latticeBox K) :
    (∑ y ∈ s, pairStratumWeightedKernel a p m n k l x y) ≤
      4 ^ ((h : ℝ) - 1) * 2 ^ p *
        ((9 : ℝ) ^ (h - 3) * 1188 / (a * p * (1 - a * p))) := by
  let L : ℝ := 1 + ‖siteToPlane (x m - x n)‖ ^ 2
  let anchor : Fin (h - 3) → Site := fun j => x (e.symm j).val
  have hL : 1 ≤ L := by
    change 1 ≤ 1 + ‖siteToPlane (x m - x n)‖ ^ 2
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hprofile := sum_pairStratum_profile_le m n k l hmn e hL ha hp hap
    anchor (x k) s K hcollision hbox
  have hprofile0 :
      (∑ y ∈ s, collisionProfileKernel L ((h - 3 : ℕ) + 2) a p anchor (x k)
        (fun j => y (e.symm j).val) (y k, y l)) ≤
        (9 : ℝ) ^ (h - 3) * 1188 * L ^ (-(a * p)) /
          (a * p * (1 - a * p)) := by
    simpa [encodePairStratumFin] using hprofile
  have hC : 0 ≤ (9 : ℝ) ^ (h - 3) * 1188 / (a * p * (1 - a * p)) := by
    positivity
  have hrow :
      (∑ y ∈ s, pairStratumWeightedKernel a p m n k l x y) ≤
        4 ^ ((h : ℝ) - 1) *
          (1 + ‖siteToPlane (x m - x n)‖ ^ (2 * a)) ^ p *
          ∑ y ∈ s, collisionProfileKernel L ((h - 3 : ℕ) + 2) a p anchor (x k)
            (fun j => y (e.symm j).val) (y k, y l) := by
    calc
      _ ≤ ∑ y ∈ s, 4 ^ ((h : ℝ) - 1) *
            (1 + ‖siteToPlane (x m - x n)‖ ^ (2 * a)) ^ p *
              collisionProfileKernel L ((h - 3 : ℕ) + 2) a p anchor (x k)
                (fun j => y (e.symm j).val) (y k, y l) :=
          Finset.sum_le_sum fun y hy =>
            pairStratum_weighted_le_profile m n k l hmn hmk hml hkl e hxy
              (hcollision y hy)
      _ = 4 ^ ((h : ℝ) - 1) *
            (1 + ‖siteToPlane (x m - x n)‖ ^ (2 * a)) ^ p *
              ∑ y ∈ s, collisionProfileKernel L ((h - 3 : ℕ) + 2) a p anchor (x k)
                (fun j => y (e.symm j).val) (y k, y l) := by
          rw [← Finset.mul_sum]
  have hscaled :
      (1 + ‖siteToPlane (x m - x n)‖ ^ (2 * a)) ^ p *
        ∑ y ∈ s, collisionProfileKernel L ((h - 3 : ℕ) + 2) a p anchor (x k)
          (fun j => y (e.symm j).val) (y k, y l) ≤
        2 ^ p * ((9 : ℝ) ^ (h - 3) * 1188 /
          (a * p * (1 - a * p))) := by
    have hprofile' :
        ∑ y ∈ s, collisionProfileKernel L ((h - 3 : ℕ) + 2) a p anchor (x k)
          (fun j => y (e.symm j).val) (y k, y l) ≤
          ((9 : ℝ) ^ (h - 3) * 1188 / (a * p * (1 - a * p))) *
            L ^ (-(a * p)) := by
      calc
        _ ≤ (9 : ℝ) ^ (h - 3) * 1188 * L ^ (-(a * p)) /
            (a * p * (1 - a * p)) := hprofile0
        _ = ((9 : ℝ) ^ (h - 3) * 1188 /
            (a * p * (1 - a * p))) * L ^ (-(a * p)) := by ring
    have hAnum : 0 ≤ (1 + ‖siteToPlane (x m - x n)‖ ^ (2 * a)) ^ p := by
      positivity
    have hprod := mul_le_mul_of_nonneg_left hprofile' hAnum
    have hcancel := collision_numerator_cancel (norm_nonneg (siteToPlane (x m - x n))) ha hp
    calc
      _ ≤ (1 + ‖siteToPlane (x m - x n)‖ ^ (2 * a)) ^ p *
          ((9 : ℝ) ^ (h - 3) * 1188 /
            (a * p * (1 - a * p)) * L ^ (-(a * p))) := hprod
      _ = ((9 : ℝ) ^ (h - 3) * 1188 /
            (a * p * (1 - a * p))) *
          ((1 + ‖siteToPlane (x m - x n)‖ ^ (2 * a)) ^ p * L ^ (-(a * p))) := by
          ring
      _ ≤ ((9 : ℝ) ^ (h - 3) * 1188 /
            (a * p * (1 - a * p))) * 2 ^ p :=
          mul_le_mul_of_nonneg_left hcancel hC
      _ = 2 ^ p * ((9 : ℝ) ^ (h - 3) * 1188 /
            (a * p * (1 - a * p))) := by ring
  calc
    _ ≤ 4 ^ ((h : ℝ) - 1) *
        (1 + ‖siteToPlane (x m - x n)‖ ^ (2 * a)) ^ p *
          ∑ y ∈ s, collisionProfileKernel L ((h - 3 : ℕ) + 2) a p anchor (x k)
            (fun j => y (e.symm j).val) (y k, y l) := hrow
    _ ≤ 4 ^ ((h : ℝ) - 1) *
        (2 ^ p * ((9 : ℝ) ^ (h - 3) * 1188 /
          (a * p * (1 - a * p)))) := by
      calc
        _ = 4 ^ ((h : ℝ) - 1) *
            ((1 + ‖siteToPlane (x m - x n)‖ ^ (2 * a)) ^ p *
              ∑ y ∈ s, collisionProfileKernel L ((h - 3 : ℕ) + 2) a p anchor (x k)
                (fun j => y (e.symm j).val) (y k, y l)) := by ring
        _ ≤ 4 ^ ((h : ℝ) - 1) *
            (2 ^ p * ((9 : ℝ) ^ (h - 3) * 1188 /
              (a * p * (1 - a * p)))) :=
          mul_le_mul_of_nonneg_left hscaled
            (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) ((h : ℝ) - 1))
        _ = _ := by ring
    _ = _ := by ring

end

end Critical2DKPZ.MomentBounds
