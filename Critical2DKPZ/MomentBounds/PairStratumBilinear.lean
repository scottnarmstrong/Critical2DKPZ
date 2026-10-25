/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.PairStratumRow
public import Critical2DKPZ.MomentBounds.FiniteSchur
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-! # The finite LZ21 bilinear estimate for two distinct collision pairs -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- The unweighted h-replica lattice kernel in LZ21 Eq. (3.21). -/
def replicaGreenKernel {h : ℕ} (x y : LatticeConfiguration h) : ℝ :=
  (1 + replicaDistanceEnergy x y) ^ (-((h : ℝ) - 1))

/-- The replica distance energy is nonnegative. -/
theorem replicaDistanceEnergy_nonneg {h : ℕ} (x y : LatticeConfiguration h) :
    0 ≤ replicaDistanceEnergy x y := by
  unfold replicaDistanceEnergy
  apply Finset.sum_nonneg
  intro i hi
  exact sq_nonneg _

/-- The replica distance energy is symmetric in its arguments. -/
theorem replicaDistanceEnergy_symm {h : ℕ} (x y : LatticeConfiguration h) :
    replicaDistanceEnergy x y = replicaDistanceEnergy y x := by
  unfold replicaDistanceEnergy
  apply Finset.sum_congr rfl
  intro i hi
  exact (siteDistance_sq_symm (x i) (y i)).symm

/-- The replica Green kernel is strictly positive. -/
theorem replicaGreenKernel_pos {h : ℕ} (x y : LatticeConfiguration h) :
    0 < replicaGreenKernel x y := by
  unfold replicaGreenKernel
  apply Real.rpow_pos_of_pos
  have hE := replicaDistanceEnergy_nonneg x y
  linarith

/-- The replica Green kernel is symmetric in its arguments. -/
theorem replicaGreenKernel_symm {h : ℕ} (x y : LatticeConfiguration h) :
    replicaGreenKernel x y = replicaGreenKernel y x := by
  simp [replicaGreenKernel, replicaDistanceEnergy_symm]

/-- Every finite family of replica configurations is contained in one common
coordinate box. -/
theorem exists_configurations_in_box {h : ℕ} (s : Finset (LatticeConfiguration h)) :
    ∃ K : ℕ, ∀ x ∈ s, ∀ i, x i ∈ latticeBox K := by
  classical
  refine ⟨∑ x ∈ s, ∑ i : Fin h, latticeRadius (x i), ?_⟩
  intro x hx i
  rw [mem_latticeBox]
  have hi : latticeRadius (x i) ≤ ∑ j : Fin h, latticeRadius (x j) :=
    Finset.single_le_sum (f := fun j : Fin h => latticeRadius (x j))
      (fun j hj => Nat.zero_le (latticeRadius (x j))) (Finset.mem_univ i)
  have hxsum : (∑ j : Fin h, latticeRadius (x j)) ≤
      ∑ z ∈ s, ∑ j : Fin h, latticeRadius (z j) :=
    Finset.single_le_sum (f := fun z : LatticeConfiguration h =>
      ∑ j : Fin h, latticeRadius (z j))
      (fun z hz => Finset.sum_nonneg fun j hj => Nat.zero_le (latticeRadius (z j))) hx
  exact hi.trans hxsum

/-- Taking a real power of the collision-weight ratio gives the corresponding power ratio. -/
theorem collisionWeightRatio_rpow {A B r : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (A / B) ^ r = A ^ r * B ^ (-r) := by
  rw [Real.div_rpow hA.le hB.le r, Real.rpow_neg hB.le r, div_eq_mul_inv]

/-- Hölder-conjugate roots of the two Schur constants multiply to four times the common bound. -/
theorem schur_row_root_product {p q S : ℝ} (hpq : p.HolderConjugate q) (hS : 0 < S) :
    (S * 2 ^ p) ^ (1 / p) * (S * 2 ^ q) ^ (1 / q) = 4 * S := by
  have hinvsum : 1 / p + 1 / q = 1 := by
    simpa [one_div] using hpq.inv_add_inv_eq_one
  have hSroot : S ^ (1 / p) * S ^ (1 / q) = S := by
    rw [← Real.rpow_add hS, hinvsum, Real.rpow_one]
  have h2p : ((2 : ℝ) ^ p) ^ (1 / p) = 2 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hpone : p * (1 / p) = 1 := by field_simp [hpq.ne_zero]
    rw [hpone, Real.rpow_one]
  have h2q : ((2 : ℝ) ^ q) ^ (1 / q) = 2 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hqone : q * (1 / q) = 1 := by field_simp [hpq.symm.ne_zero]
    rw [hqone, Real.rpow_one]
  calc
    (S * 2 ^ p) ^ (1 / p) * (S * 2 ^ q) ^ (1 / q) =
        (S ^ (1 / p) * ((2 : ℝ) ^ p) ^ (1 / p)) *
          (S ^ (1 / q) * ((2 : ℝ) ^ q) ^ (1 / q)) := by
            rw [Real.mul_rpow hS.le (by positivity), Real.mul_rpow hS.le (by positivity)]
    _ = (S ^ (1 / p) * S ^ (1 / q)) *
          (((2 : ℝ) ^ p) ^ (1 / p) * ((2 : ℝ) ^ q) ^ (1 / q)) := by ring
    _ = 4 * S := by rw [hSroot, h2p, h2q]; ring

/-- LZ21's weighted-Hölder argument, with both row and column estimates, for
two collision pairs admitting a label outside the other pair in each direction. -/
theorem finite_pair_stratum_bilinear_le {h : ℕ}
    (m n k l : Fin h)
    (hmn : m ≠ n) (hmk : m ≠ k) (hml : m ≠ l) (hkl : k ≠ l)
    (hkm : k ≠ m) (hkn : k ≠ n)
    (e₁ : PairSpectatorLabels h m k l ≃ Fin (h - 3))
    (e₂ : PairSpectatorLabels h k m n ≃ Fin (h - 3))
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (s t : Finset (LatticeConfiguration h))
    (hs : ∀ x ∈ s, x k = x l) (ht : ∀ y ∈ t, y m = y n)
    (f g : LatticeConfiguration h → ℝ) :
    (∑ x ∈ s, ∑ y ∈ t, |f x| * replicaGreenKernel x y * |g y|) ≤
      4 ^ ((h : ℝ) - 1) * 4 * (9 : ℝ) ^ (h - 3) * 1188 * (p * q) *
        (∑ x ∈ s, |f x| ^ p) ^ (1 / p) *
        (∑ y ∈ t, |g y| ^ q) ^ (1 / q) := by
  classical
  let a : ℝ := 1 / (p * q)
  let A : LatticeConfiguration h → ℝ := fun x =>
    1 + ‖siteToPlane (x m - x n)‖ ^ (2 * a)
  let B : LatticeConfiguration h → ℝ := fun y =>
    1 + ‖siteToPlane (y k - y l)‖ ^ (2 * a)
  let S : ℝ := 4 ^ ((h : ℝ) - 1) * (9 : ℝ) ^ (h - 3) * 1188 * (p * q)
  have hp : 0 < p := hpq.pos
  have hq : 0 < q := hpq.symm.pos
  have hinvsum : 1 / p + 1 / q = 1 := by
    simpa [one_div] using hpq.inv_add_inv_eq_one
  have ha : 0 < a := by dsimp [a]; positivity
  have hap : a * p < 1 := by
    have hrecip : 1 / q < 1 := by
      have hpos : 0 < 1 / p := one_div_pos.mpr hp
      linarith [hinvsum]
    have hqone : 1 < q := by
      exact (one_div_lt_one_div hq (by norm_num : (0 : ℝ) < 1)).mp (by simpa using hrecip)
    have haeq : a * p = 1 / q := by
      dsimp [a]
      field_simp [hp.ne', hq.ne']
    rw [haeq]
    simpa using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hqone
  have haq : a * q < 1 := by
    have hrecip : 1 / p < 1 := by
      have hpos : 0 < 1 / q := one_div_pos.mpr hq
      linarith [hinvsum]
    have hpone : 1 < p := by
      exact (one_div_lt_one_div hp (by norm_num : (0 : ℝ) < 1)).mp (by simpa using hrecip)
    have haeq : a * q = 1 / p := by
      dsimp [a]
      field_simp [hp.ne', hq.ne']
    rw [haeq]
    simpa using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hpone
  have hden : a * p * (1 - a * p) = 1 / (p * q) := by
    have hAp : a * p = 1 / q := by
      dsimp [a]
      field_simp [hp.ne', hq.ne']
    rw [hAp]
    have hminus : 1 - 1 / q = 1 / p := by linarith [hinvsum]
    rw [hminus]
    field_simp [hp.ne', hq.ne']
  have hinvden : 1 / (a * p * (1 - a * p)) = p * q := by
    rw [hden]
    field_simp [hp.ne', hq.ne']
  have hS : 0 < S := by
    dsimp [S]
    positivity
  obtain ⟨Ks, hboxs⟩ := exists_configurations_in_box s
  obtain ⟨Kt, hboxt⟩ := exists_configurations_in_box t
  have hApos (x : LatticeConfiguration h) : 0 < A x := by
    dsimp [A]
    positivity
  have hBpos (y : LatticeConfiguration h) : 0 < B y := by
    dsimp [B]
    positivity
  have hKpos (x y : LatticeConfiguration h) : 0 < replicaGreenKernel x y :=
    replicaGreenKernel_pos x y
  have hrow (x : LatticeConfiguration h) (hx : x ∈ s) :
      (∑ y ∈ t, replicaGreenKernel x y * (A x / B y) ^ p) ≤ S * 2 ^ p := by
    have hmodel := sum_pairStratum_weightedKernel_le m n k l hmn hmk hml hkl e₁
      ha hp (by simpa [a] using hap) x (hs x hx) t Kt ht hboxt
    have hsum :
        (∑ y ∈ t, replicaGreenKernel x y * (A x / B y) ^ p) =
          ∑ y ∈ t, pairStratumWeightedKernel a p m n k l x y := by
      apply Finset.sum_congr rfl
      intro y hy
      have hr := collisionWeightRatio_rpow (r := p) (hApos x) (hBpos y)
      simp [A, B, replicaGreenKernel, pairStratumWeightedKernel, hr]
      ring
    rw [hsum]
    calc
      _ ≤ 4 ^ ((h : ℝ) - 1) * 2 ^ p *
          ((9 : ℝ) ^ (h - 3) * 1188 / (a * p * (1 - a * p))) := hmodel
      _ = S * 2 ^ p := by
        have hdenInv : (a * p * (1 - a * p))⁻¹ = p * q := by
          simpa [one_div] using hinvden
        have hfactor : (9 : ℝ) ^ (h - 3) * 1188 / (a * p * (1 - a * p)) =
            (9 : ℝ) ^ (h - 3) * 1188 * (p * q) := by
          rw [div_eq_mul_inv, hdenInv]
        dsimp [S]
        rw [hfactor]
        ring
  have hcol (y : LatticeConfiguration h) (hy : y ∈ t) :
      (∑ x ∈ s, replicaGreenKernel x y * (B y / A x) ^ q) ≤ S * 2 ^ q := by
    have hmodel := sum_pairStratum_weightedKernel_le k l m n hkl hkm hkn hmn e₂
      ha hq haq y (ht y hy) s Ks (fun x hx => hs x hx) hboxs
    have hsum :
        (∑ x ∈ s, replicaGreenKernel x y * (B y / A x) ^ q) =
          ∑ x ∈ s, pairStratumWeightedKernel a q k l m n y x := by
      apply Finset.sum_congr rfl
      intro x hx
      have hr := collisionWeightRatio_rpow (r := q) (hBpos y) (hApos x)
      rw [replicaGreenKernel_symm]
      simp [A, B, replicaGreenKernel, pairStratumWeightedKernel, hr]
      ring
    rw [hsum]
    calc
      _ ≤ 4 ^ ((h : ℝ) - 1) * 2 ^ q *
          ((9 : ℝ) ^ (h - 3) * 1188 / (a * q * (1 - a * q))) := hmodel
      _ = S * 2 ^ q := by
        have hdenq : 1 / (a * q * (1 - a * q)) = p * q := by
          have hAq : a * q = 1 / p := by
            dsimp [a]
            field_simp [hp.ne', hq.ne']
          rw [hAq]
          have hminus : 1 - 1 / p = 1 / q := by linarith [hinvsum]
          rw [hminus]
          field_simp [hp.ne', hq.ne']
        have hdenInv : (a * q * (1 - a * q))⁻¹ = p * q := by
          simpa [one_div] using hdenq
        have hfactor : (9 : ℝ) ^ (h - 3) * 1188 / (a * q * (1 - a * q)) =
            (9 : ℝ) ^ (h - 3) * 1188 * (p * q) := by
          rw [div_eq_mul_inv, hdenInv]
        dsimp [S]
        rw [hfactor]
        ring
  have hfinal := finite_weighted_schur s t replicaGreenKernel A B f g hpq
    (by positivity) (by positivity) hKpos hApos hBpos hrow hcol
  calc
    (∑ x ∈ s, ∑ y ∈ t, |f x| * replicaGreenKernel x y * |g y|) ≤
        (S * 2 ^ p) ^ (1 / p) * (S * 2 ^ q) ^ (1 / q) *
          (∑ x ∈ s, |f x| ^ p) ^ (1 / p) *
          (∑ y ∈ t, |g y| ^ q) ^ (1 / q) := hfinal
    _ = 4 * S * (∑ x ∈ s, |f x| ^ p) ^ (1 / p) *
          (∑ y ∈ t, |g y| ^ q) ^ (1 / q) := by rw [schur_row_root_product hpq hS]
    _ = _ := by dsimp [S]; ring

end

end Critical2DKPZ.MomentBounds
