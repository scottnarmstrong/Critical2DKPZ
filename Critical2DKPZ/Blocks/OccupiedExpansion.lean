/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.StringSum
public import Critical2DKPZ.Blocks.CollisionIntegration
public import Critical2DKPZ.Blocks.ChaosPropagation
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Tactic

/-! # Expansion over the occupied intermediate blocks -/

@[expose] public noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.Blocks

/-- One occupied block acts by its absolute first-last collision cell. -/
theorem stringTail_cons_eq_cell (σ2 : ℝ) (t : ℕ → ℕ) (i : ℕ) (is : List ℕ)
    (b : ℕ) (y : Site) :
    stringTail σ2 t (i :: is) b y =
      collisionCellSum σ2 (t (i - 1)) (t i)
        (fun a x => discrepancyHeatKernel b a y x ^ 2)
        (fun c z => stringTail σ2 t is c z) := by
  rfl

/-- Sum over all choices of occupied intermediate blocks, with the last block prescribed. -/
def occupiedTailSum (σ2 : ℝ) (t : ℕ → ℕ) (u v : ℕ) (b : ℕ) (y : Site) : ℝ :=
  ∑ S ∈ (Finset.Ico u v).powerset, stringTail σ2 t (S.sort (· ≤ ·) ++ [v]) b y

/-- With no intermediate blocks, only the terminal occupied block remains. -/
theorem occupiedTailSum_self (σ2 : ℝ) (t : ℕ → ℕ) (v b : ℕ) (y : Site) :
    occupiedTailSum σ2 t v v b y =
      collisionCellSum σ2 (t (v - 1)) (t v)
        (fun a x => discrepancyHeatKernel b a y x ^ 2) (fun _ _ => 1) := by
  simp only [occupiedTailSum, Finset.Ico_self, Finset.powerset_empty, Finset.sum_singleton,
    Finset.sort_empty, List.nil_append, stringTail_cons_eq_cell]
  rfl

/-- The closed collision-string sum ranges over occupied intermediate blocks with fixed first and last blocks. -/
theorem closedStringSum_eq_sum_firstCell (σ2 : ℝ) (t : ℕ → ℕ) (u v : ℕ) :
    closedStringSum σ2 t u v =
      ∑ S ∈ (Finset.Ioo u v).powerset,
        collisionCellSum σ2 (t (u - 1)) (t u) (fun a x => srwKernel a x ^ 2)
          (fun c z => stringTail σ2 t (S.sort (· ≤ ·) ++ [v]) c z) := by
  rfl

/-- Partition the occupied subsets according to whether their first available block is occupied. -/
theorem occupiedTailSum_recursion (β : ℝ) (t : ℕ → ℕ) {u v : ℕ}
    (huv : u < v) (b : ℕ) (y : Site) :
    occupiedTailSum (Polymer.sigmaSq β) t u v b y =
      occupiedTailSum (Polymer.sigmaSq β) t (u + 1) v b y +
        collisionCellSum (Polymer.sigmaSq β) (t (u - 1)) (t u)
          (fun a x => discrepancyHeatKernel b a y x ^ 2)
          (fun c z => occupiedTailSum (Polymer.sigmaSq β) t (u + 1) v c z) := by
  classical
  have hI : Finset.Ico u v = insert u (Finset.Ico (u + 1) v) := by
    ext i
    simp only [Finset.mem_Ico, Finset.mem_insert]
    omega
  have hnot : u ∉ Finset.Ico (u + 1) v := by simp only [Finset.mem_Ico]; omega
  unfold occupiedTailSum
  rw [hI, Finset.sum_powerset_insert hnot]
  apply congrArg (fun q : ℝ =>
    (∑ S ∈ (Finset.Ico (u + 1) v).powerset,
      stringTail (Polymer.sigmaSq β) t (S.sort (· ≤ ·) ++ [v]) b y) + q)
  have hterm (S : Finset ℕ) (hS : S ∈ (Finset.Ico (u + 1) v).powerset) :
      stringTail (Polymer.sigmaSq β) t ((insert u S).sort (· ≤ ·) ++ [v]) b y =
      collisionCellSum (Polymer.sigmaSq β) (t (u - 1)) (t u)
        (fun a x => discrepancyHeatKernel b a y x ^ 2)
        (fun c z => stringTail (Polymer.sigmaSq β) t (S.sort (· ≤ ·) ++ [v]) c z) := by
    have hsub := Finset.mem_powerset.1 hS
    have hmin (j : ℕ) (hj : j ∈ S) : u ≤ j := by
      have := Finset.mem_Ico.1 (hsub hj)
      omega
    have hnotS : u ∉ S := fun hu => hnot (hsub hu)
    rw [Finset.sort_insert (· ≤ ·) hmin hnotS, List.cons_append, stringTail_cons_eq_cell]
  rw [Finset.sum_congr rfl hterm]
  let S : ℕ → Finset Site := fun a => Polymer.endpoints y (a - b) ∪ Polymer.endpoints 0 a
  have hW (a : ℕ) (x : Site) (hx : x ∉ S a) : discrepancyHeatKernel b a y x ^ 2 = 0 := by
    rw [discrepancyHeatKernel_eq_zero_of_not_mem_support b a y x hx]
    norm_num
  exact (collisionCellSum_finsetSum β (t (u - 1)) (t u)
    (fun a x => discrepancyHeatKernel b a y x ^ 2) S hW
    (Finset.Ico (u + 1) v).powerset
    (fun S c z => stringTail (Polymer.sigmaSq β) t (S.sort (· ≤ ·) ++ [v]) c z)).symm

end Critical2DKPZ.Blocks
