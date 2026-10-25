/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.PairStratumProfileSum
import Critical2DKPZ.RandomWalk.GaussianBridge
import Mathlib.Tactic

/-! # Energy bookkeeping on intersecting pair-collision strata -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- The squared distance contributed by one replica coordinate. -/
def replicaCoordinateEnergy {h : ℕ} (x y : LatticeConfiguration h) (i : Fin h) : ℝ :=
  ‖siteToPlane (y i - x i)‖ ^ 2

/-- The full h-coordinate squared distance between two replica configurations. -/
def replicaDistanceEnergy {h : ℕ} (x y : LatticeConfiguration h) : ℝ :=
  ∑ i : Fin h, replicaCoordinateEnergy x y i

/-- Squared site distance is symmetric in its arguments. -/
theorem siteDistance_sq_symm (x y : Site) :
    ‖siteToPlane (x - y)‖ ^ 2 = ‖siteToPlane (y - x)‖ ^ 2 := by
  rw [Critical2DKPZ.norm_siteToPlane_sq, Critical2DKPZ.norm_siteToPlane_sq]
  simp only [Pi.sub_apply, Int.cast_sub]
  ring

/-- The artificial collision weight cancels against the displacement scale. -/
theorem collision_numerator_cancel {u a p : ℝ} (hu : 0 ≤ u) (ha : 0 < a) (hp : 0 < p) :
    (1 + u ^ (2 * a)) ^ p * (1 + u ^ 2) ^ (-(a * p)) ≤ 2 ^ p := by
  have hbase : 0 < 1 + u ^ 2 := by positivity
  have hu2 : u ^ (2 : ℝ) = u ^ 2 := Real.rpow_natCast u 2
  have hpowid : u ^ (2 * a) = (u ^ (2 : ℝ)) ^ a :=
    Real.rpow_mul hu (2 : ℝ) a
  have hpow : u ^ (2 * a) ≤ (1 + u ^ 2) ^ a := by
    rw [hpowid]
    apply Real.rpow_le_rpow (Real.rpow_nonneg hu _) _ ha.le
    rw [hu2]
    nlinarith [sq_nonneg u]
  have hone : 1 ≤ (1 + u ^ 2) ^ a := by
    have hh : (1 : ℝ) ^ a ≤ (1 + u ^ 2) ^ a :=
      Real.rpow_le_rpow (by norm_num) (by nlinarith [sq_nonneg u]) ha.le
    simpa using hh
  have hsum : 1 + u ^ (2 * a) ≤ 2 * (1 + u ^ 2) ^ a := by
    linarith
  have hnum : (1 + u ^ (2 * a)) ^ p ≤ 2 ^ p * (1 + u ^ 2) ^ (a * p) := by
    calc
      (1 + u ^ (2 * a)) ^ p ≤ (2 * (1 + u ^ 2) ^ a) ^ p :=
        Real.rpow_le_rpow (by positivity) hsum hp.le
      _ = 2 ^ p * (1 + u ^ 2) ^ (a * p) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hbase.le a p]
  have hcancel : (1 + u ^ 2) ^ (a * p) * (1 + u ^ 2) ^ (-(a * p)) = 1 := by
    rw [← Real.rpow_add hbase]
    simp
  calc
    (1 + u ^ (2 * a)) ^ p * (1 + u ^ 2) ^ (-(a * p)) ≤
        (2 ^ p * (1 + u ^ 2) ^ (a * p)) * (1 + u ^ 2) ^ (-(a * p)) :=
      mul_le_mul_of_nonneg_right hnum (Real.rpow_nonneg hbase.le _)
    _ = 2 ^ p := by rw [mul_assoc, hcancel, mul_one]

/-- Removing the omitted collision label and retaining every other coordinate is
exactly the sum over the selected pair and its spectators. -/
theorem sum_except_pair_eq {h : ℕ} (m k l : Fin h)
    (hmk : m ≠ k) (hml : m ≠ l) (hkl : k ≠ l) (f : Fin h → ℝ) :
    (∑ i ∈ Finset.univ.erase m, f i) = f k + f l +
      ∑ i : PairSpectatorLabels h m k l, f i.val := by
  classical
  let S : Finset (Fin h) := Finset.univ.filter (fun i => i ≠ m ∧ i ≠ k ∧ i ≠ l)
  have hS : S = ((Finset.univ.erase m).erase k).erase l := by
    ext i
    simp [S, and_assoc, and_comm]
  have hk : k ∈ Finset.univ.erase m :=
    Finset.mem_erase.mpr ⟨hmk.symm, Finset.mem_univ _⟩
  have hl : l ∈ (Finset.univ.erase m).erase k := by
    apply Finset.mem_erase.mpr
    exact ⟨hkl.symm, Finset.mem_erase.mpr ⟨hml.symm, Finset.mem_univ _⟩⟩
  have hsub : (∑ i : PairSpectatorLabels h m k l, f i.val) =
      ∑ i ∈ S, f i := by
    rw [← Finset.sum_subtype_eq_sum_filter]
    simp [PairSpectatorLabels]
  have h1 := Finset.add_sum_erase (Finset.univ.erase m) f hk
  have h2 := Finset.add_sum_erase ((Finset.univ.erase m).erase k) f hl
  rw [hS] at hsub
  calc
    (∑ i ∈ Finset.univ.erase m, f i) =
        f k + ∑ i ∈ (Finset.univ.erase m).erase k, f i := h1.symm
    _ = f k + (f l + ∑ i ∈ ((Finset.univ.erase m).erase k).erase l, f i) := by
      rw [h2.symm]
    _ = f k + f l + ∑ i : PairSpectatorLabels h m k l, f i.val := by
      rw [← hsub]
      ring

/-- The reduced profile energy is exactly the distance sum over every label
except the omitted representative of the second collision pair. -/
theorem pairProfileEnergy_eq {h : ℕ} (m k l : Fin h)
    (hmk : m ≠ k) (hml : m ≠ l) (hkl : k ≠ l)
    (e : PairSpectatorLabels h m k l ≃ Fin (h - 3))
    (x y : LatticeConfiguration h) :
    replicaEnergy (fun j => x (e.symm j).val)
        (fun j => y (e.symm j).val) +
      ‖siteToPlane (y k - x k)‖ ^ 2 + ‖siteToPlane (y l - x l)‖ ^ 2 =
      ∑ i ∈ Finset.univ.erase m, replicaCoordinateEnergy x y i := by
  let f := replicaCoordinateEnergy x y
  have hspec : replicaEnergy (fun j => x (e.symm j).val)
        (fun j => y (e.symm j).val) =
      ∑ i : PairSpectatorLabels h m k l, f i.val := by
    unfold replicaEnergy
    change (∑ j : Fin (h - 3), f (e.symm j).val) =
      ∑ i : PairSpectatorLabels h m k l, f i.val
    exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  have hdecomp := sum_except_pair_eq m k l hmk hml hkl f
  have hk : f k = ‖siteToPlane (y k - x k)‖ ^ 2 := by
    rfl
  have hl : f l = ‖siteToPlane (y l - x l)‖ ^ 2 := by
    rfl
  calc
    _ = f k + f l + ∑ i : PairSpectatorLabels h m k l, f i.val := by
      rw [hspec, ← hk, ← hl]
      ring
    _ = ∑ i ∈ Finset.univ.erase m, f i := hdecomp.symm

/-- The full distance sum splits into the omitted coordinate and its complement. -/
theorem replicaDistanceEnergy_add_erase {h : ℕ} (m : Fin h)
    (x y : LatticeConfiguration h) :
    replicaCoordinateEnergy x y m +
      ∑ i ∈ Finset.univ.erase m, replicaCoordinateEnergy x y i =
      replicaDistanceEnergy x y := by
  exact Finset.add_sum_erase Finset.univ (replicaCoordinateEnergy x y)
    (Finset.mem_univ m)

/-- The pair-collision substitution loses at most the factor four in the
full h-replica denominator, even when the selected pairs share a label. -/
theorem pairProfileDenominator_le_four {h : ℕ} (m n k l : Fin h)
    (hmn : m ≠ n) (hmk : m ≠ k) (hml : m ≠ l) (hkl : k ≠ l)
    (e : PairSpectatorLabels h m k l ≃ Fin (h - 3))
    {x y : LatticeConfiguration h} (hy : y m = y n) :
    1 + ‖siteToPlane (x m - x n)‖ ^ 2 +
        replicaEnergy (fun j => x (e.symm j).val) (fun j => y (e.symm j).val) +
        ‖siteToPlane (y k - x k)‖ ^ 2 + ‖siteToPlane (y l - x l)‖ ^ 2 ≤
      4 * (1 + replicaDistanceEnergy x y) := by
  let d : Fin h → ℝ := replicaCoordinateEnergy x y
  let R : ℝ := ∑ i ∈ Finset.univ.erase m, d i
  have hprofile :
      replicaEnergy (fun j => x (e.symm j).val) (fun j => y (e.symm j).val) +
        ‖siteToPlane (y k - x k)‖ ^ 2 + ‖siteToPlane (y l - x l)‖ ^ 2 = R := by
    simpa [R, d] using pairProfileEnergy_eq m k l hmk hml hkl e x y
  have htotal : d m + R = replicaDistanceEnergy x y := by
    simpa [R, d] using replicaDistanceEnergy_add_erase m x y
  have hR : 0 ≤ R := by
    dsimp [R]
    apply Finset.sum_nonneg
    intro i hi
    exact sq_nonneg _
  have hDm : 0 ≤ d m := sq_nonneg _
  have hDn : 0 ≤ d n := sq_nonneg _
  have hnmem : n ∈ Finset.univ.erase m :=
    Finset.mem_erase.mpr ⟨hmn.symm, Finset.mem_univ _⟩
  have hDnR : d n ≤ R := by
    dsimp [R]
    apply Finset.single_le_sum
    · intro i hi
      exact sq_nonneg _
    · exact hnmem
  have hgeom := pair_anchor_distance_sq_le (x m) (x n) (y n)
  have hgeom' : ‖siteToPlane (x m - x n)‖ ^ 2 ≤ 2 * (d m + d n) := by
    have hterm : replicaCoordinateEnergy x y m =
        ‖siteToPlane (x m - y n)‖ ^ 2 := by
      dsimp [replicaCoordinateEnergy]
      rw [hy]
      exact (siteDistance_sq_symm (x m) (y n)).symm
    have hterm' : replicaCoordinateEnergy x y n =
        ‖siteToPlane (x n - y n)‖ ^ 2 := by
      dsimp [replicaCoordinateEnergy]
      exact (siteDistance_sq_symm (x n) (y n)).symm
    simpa [d, hterm, hterm'] using hgeom
  calc
    _ = 1 + ‖siteToPlane (x m - x n)‖ ^ 2 + R := by
      rw [← hprofile]
      ring
    _ ≤ 4 * (1 + replicaDistanceEnergy x y) := by
      rw [← htotal]
      nlinarith [hgeom', hDnR, hDm, hDn, hR]

end

end Critical2DKPZ.MomentBounds
