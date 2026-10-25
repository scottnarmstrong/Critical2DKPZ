/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.SrwKernel
public import Critical2DKPZ.RandomWalk.Port.Walk.SRW
import Mathlib

/-!
# Identifying the path sum with the recursive simple walk kernel

The four step labels enumerate the two signed coordinate directions. Splitting a
word at its final letter gives the same recursion as `LatticeProb.srwHeat`.
-/

@[expose] public section

namespace Critical2DKPZ

/-- At its endpoint, a word contributes the sum of all its steps. -/
theorem walkPosition_endpoint {n : ℕ} (s : Fin n → Fin 4) :
    walkPosition 0 s n = ∑ i, srwStep (s i) := by
  simp [walkPosition]

/-- Appending one letter adds its step to the endpoint. -/
theorem walkPosition_snoc {n : ℕ} (s : Fin n → Fin 4) (a : Fin 4) :
    walkPosition 0 (Fin.snoc s a) (n + 1) = walkPosition 0 s n + srwStep a := by
  simp only [walkPosition_endpoint, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

/-- The transition probability at time zero is the point mass at the origin. -/
@[simp] theorem srwKernel_zero (z : Site) :
    srwKernel 0 z = if z = 0 then 1 else 0 := by
  simp [srwKernel, walkPosition, eq_comm]

/-- Splitting a word at its last letter gives the forward recursion. -/
theorem srwKernel_succ (n : ℕ) (z : Site) :
    srwKernel (n + 1) z = (∑ a : Fin 4, srwKernel n (z - srwStep a)) / 4 := by
  classical
  let e : ((Fin n → Fin 4) × Fin 4) ≃ (Fin (n + 1) → Fin 4) :=
    { toFun := fun p => Fin.snoc p.1 p.2
      invFun := fun s => (fun i => s i.castSucc, s (Fin.last n))
      left_inv := by intro p; simp
      right_inv := by intro s; exact Fin.snoc_init_self s }
  rw [srwKernel, ← e.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [srwKernel]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun s _ => ?_
  change (4 : ℝ)⁻¹ ^ (n + 1) * (if walkPosition 0 (Fin.snoc s a) (n + 1) = z then 1 else 0) =
    ((4 : ℝ)⁻¹ ^ n * if walkPosition 0 s n = z - srwStep a then 1 else 0) / 4
  rw [walkPosition_snoc]
  simp only [show walkPosition 0 s n + srwStep a = z ↔
    walkPosition 0 s n = z - srwStep a from eq_sub_iff_add_eq.symm]
  split_ifs <;> simp [pow_succ]
  ring

/-- Averaging the four labelled steps is the recursive lattice walk operator. -/
theorem sum_srwStep_sub (f : Site → ℝ) (z : Site) :
    ∑ a : Fin 4, f (z - srwStep a) =
      ∑ a : LatticeProb.Dir 2, f (z + LatticeProb.dirVec a) := by
  rw [Fin.sum_univ_four, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Fintype.sum_bool]
  have h0 : z - srwStep 0 = z + LatticeProb.dirVec ((0, false) : LatticeProb.Dir 2) := by
    ext i; fin_cases i <;> simp [srwStep, LatticeProb.dirVec, sub_eq_add_neg]
  have h1 : z - srwStep 1 = z + LatticeProb.dirVec ((0, true) : LatticeProb.Dir 2) := by
    ext i; fin_cases i <;> simp [srwStep, LatticeProb.dirVec, sub_eq_add_neg]
  have h2 : z - srwStep 2 = z + LatticeProb.dirVec ((1, false) : LatticeProb.Dir 2) := by
    ext i; fin_cases i <;> simp [srwStep, LatticeProb.dirVec, sub_eq_add_neg]
  have h3 : z - srwStep 3 = z + LatticeProb.dirVec ((1, true) : LatticeProb.Dir 2) := by
    ext i; fin_cases i <;> simp [srwStep, LatticeProb.dirVec, sub_eq_add_neg]
  rw [h0, h1, h2, h3]
  ring

/-- The path-sum kernel equals the recursive simple walk kernel. -/
theorem srwKernel_eq_srwHeat (n : ℕ) (z : Site) :
    srwKernel n z = LatticeProb.srwHeat 2 n z := by
  induction n generalizing z with
  | zero => exact srwKernel_zero z
  | succ n ih =>
    rw [srwKernel_succ, LatticeProb.srwHeat_succ_eq_sum_dir, sum_srwStep_sub]
    simp only [ih]
    norm_num

end Critical2DKPZ
