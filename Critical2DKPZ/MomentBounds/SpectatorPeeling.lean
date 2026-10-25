/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CoordinateSum
public import Critical2DKPZ.MomentBounds.FinitePiSums
import Mathlib.Tactic

/-! # Finite spectator-coordinate peeling for the LZ21 lattice kernel -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- The sum of squared distances between two finite families of replica sites. -/
def replicaEnergy {m : ℕ} (anchor z : Fin m → Site) : ℝ :=
  ∑ i : Fin m, ‖siteToPlane (z i - anchor i)‖ ^ 2

/-- The denominator kernel on a finite family of independent lattice sites. -/
def replicaPowerKernel {m : ℕ} (L r : ℝ) (anchor z : Fin m → Site) : ℝ :=
  (L + replicaEnergy anchor z) ^ (-r)

/-- Adding one reference site and one replica site adds their squared distance to the replica energy. -/
theorem replicaEnergy_cons {m : ℕ} (a b : Site) (anchor z : Fin m → Site) :
    replicaEnergy (Fin.cons a anchor) (Fin.cons b z) =
      ‖siteToPlane (b - a)‖ ^ 2 + replicaEnergy anchor z := by
  simp [replicaEnergy, Fin.sum_univ_succ]

/-- Repeatedly summing one independent planar site lowers the denominator power by one.
For a cutoff box this is the finite-sum version needed before taking lattice limits. -/
theorem sum_replicaPowerKernel_finPiBox_le : ∀ m : ℕ,
    ∀ {L r : ℝ}, 1 ≤ L → (m : ℝ) + 2 ≤ r →
      ∀ anchor : Fin m → Site, ∀ k : ℕ,
        (∑ z ∈ finPiBox m k, replicaPowerKernel L r anchor z) ≤
          (9 : ℝ) ^ m * L ^ ((m : ℝ) - r) := by
  intro m
  induction m with
  | zero =>
      intro L r hL hr anchor k
      simp [finPiBox, replicaPowerKernel, replicaEnergy]
  | succ m ih =>
      intro L r hL hr anchor k
      rw [sum_finPiBox_succ]
      rw [Finset.sum_comm]
      let anchorTail : Fin m → Site := fun i => anchor i.succ
      have hr' : (m : ℝ) + 2 ≤ r - 1 := by
        have h := hr
        push_cast at h
        nlinarith
      have hr2 : 2 ≤ r := by
        have h := hr
        push_cast at h
        linarith
      have hhead (z : Fin m → Site) :
          (∑ a ∈ latticeBox k, replicaPowerKernel L r anchor (Fin.cons a z)) ≤
            9 * (L + replicaEnergy anchorTail z) ^ (1 - r) := by
        have ha : Fin.cons (anchor 0) anchorTail = anchor := by
          exact Fin.cons_self_tail anchor
        have hE (a : Site) :
            replicaEnergy anchor (Fin.cons a z) =
              ‖siteToPlane (a - anchor 0)‖ ^ 2 + replicaEnergy anchorTail z := by
          conv_lhs => rw [← ha]
          rw [replicaEnergy_cons]
        have hM : 1 ≤ L + replicaEnergy anchorTail z := by
          have he : 0 ≤ replicaEnergy anchorTail z :=
            Finset.sum_nonneg fun i _ => sq_nonneg (‖siteToPlane (z i - anchorTail i)‖)
          linarith
        have hsum := sum_shifted_lattice_rpow_le hM hr2 (anchor 0) (latticeBox k)
        calc
          (∑ a ∈ latticeBox k, replicaPowerKernel L r anchor (Fin.cons a z)) =
              ∑ a ∈ latticeBox k,
                (L + replicaEnergy anchorTail z + ‖siteToPlane (a - anchor 0)‖ ^ 2) ^ (-r) := by
                  apply Finset.sum_congr rfl
                  intro a ha'
                  simp only [replicaPowerKernel]
                  rw [hE]
                  congr 1
                  ring
          _ ≤ 9 * (L + replicaEnergy anchorTail z) ^ (1 - r) := by
            simpa [replicaEnergy] using hsum
      calc
        (∑ z ∈ finPiBox m k, ∑ a ∈ latticeBox k,
            replicaPowerKernel L r anchor (Fin.cons a z)) ≤
            ∑ z ∈ finPiBox m k, 9 * (L + replicaEnergy anchorTail z) ^ (1 - r) :=
          Finset.sum_le_sum fun z _ => hhead z
        _ = 9 * ∑ z ∈ finPiBox m k, replicaPowerKernel L (r - 1) anchorTail z := by
          rw [← Finset.mul_sum]
          apply congrArg (fun x : ℝ => 9 * x)
          apply Finset.sum_congr rfl
          intro z hz
          simp only [replicaPowerKernel]
          rw [show (1 : ℝ) - r = -(r - 1) by ring]
        _ ≤ 9 * ((9 : ℝ) ^ m * L ^ ((m : ℝ) - (r - 1))) :=
          mul_le_mul_of_nonneg_left (ih hL hr' anchorTail k) (by norm_num)
        _ = (9 : ℝ) ^ (m + 1) * L ^ (((m + 1 : ℕ) : ℝ) - r) := by
          rw [show (m : ℝ) - (r - 1) = ((m + 1 : ℕ) : ℝ) - r by push_cast; ring,
            pow_succ]
          ring

end

end Critical2DKPZ.MomentBounds
