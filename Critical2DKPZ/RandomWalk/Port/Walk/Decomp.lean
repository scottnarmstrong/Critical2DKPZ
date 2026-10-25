/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module

public import Mathlib
public import Mathlib
public import Critical2DKPZ.RandomWalk.Port.Walk.Basic
public import Critical2DKPZ.RandomWalk.Port.Walk.OneDim

/-! # Coordinate schedules and signed coordinate updates

The count of a coordinate records how many times a finite schedule selects it; appending
a choice increases exactly that count. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset

variable {d : ℕ}

/-! ### Coordinate updates -/



/-- Adding a positive unit step changes exactly its chosen coordinate by one. -/
lemma add_dirVec_true_apply (x : Site d) (i j : Fin d) :
    (x + dirVec ((i, true) : Dir d)) j = if j = i then x j + 1 else x j := by
  have h : dirVec ((i, true) : Dir d) j = if j = i then 1 else 0 := by unfold dirVec; simp
  show x j + dirVec ((i, true) : Dir d) j = _
  rw [h]
  split <;> ring

/-- Adding a negative unit step changes exactly its chosen coordinate by minus one. -/
lemma add_dirVec_false_apply (x : Site d) (i j : Fin d) :
    (x + dirVec ((i, false) : Dir d)) j = if j = i then x j - 1 else x j := by
  have h : dirVec ((i, false) : Dir d) j = if j = i then -1 else 0 := by unfold dirVec; simp
  show x j + dirVec ((i, false) : Dir d) j = _
  rw [h]
  split <;> ring





/-! ### Coordinate schedules -/

/-- How often the schedule `c` selects coordinate `i`. -/
def cnt {r : ℕ} (c : Fin r → Fin d) (i : Fin d) : ℕ := ∑ t : Fin r, if c t = i then 1 else 0

/-- The empty coordinate schedule selects every coordinate zero times. -/
lemma cnt_zero (c : Fin 0 → Fin d) : cnt c = fun _ => 0 := by
  funext i; simp [cnt]

/-- Appending a coordinate choice increases its count by one and leaves the other counts unchanged. -/
lemma cnt_snoc {r : ℕ} (c : Fin r → Fin d) (i : Fin d) :
    cnt (Fin.snoc c i : Fin (r + 1) → Fin d) = Function.update (cnt c) i (cnt c i + 1) := by
  funext j
  unfold cnt
  rw [Fin.sum_univ_castSucc]
  have h1 : ∀ t : Fin r,
      (if (Fin.snoc c i : Fin (r + 1) → Fin d) t.castSucc = j then 1 else 0)
        = (if c t = j then 1 else 0) := by
    intro t; rw [Fin.snoc_castSucc]
  rw [Finset.sum_congr rfl fun t _ => h1 t, Fin.snoc_last]
  by_cases hij : j = i
  · subst hij
    rw [Function.update_self, ite_eq_left rfl]
  · rw [Function.update_of_ne hij, ite_eq_right (fun h => hij h.symm), add_zero]

/-- Appending one letter to a schedule. -/
def snocEquiv (r : ℕ) (d : ℕ) : ((Fin r → Fin d) × Fin d) ≃ (Fin (r + 1) → Fin d) where
  toFun p := Fin.snoc p.1 p.2
  invFun c := (fun t => c t.castSucc, c (Fin.last r))
  left_inv := by
    rintro ⟨c, i⟩
    simp [Fin.snoc_castSucc, Fin.snoc_last]
  right_inv := by
    intro c
    exact Fin.snoc_init_self c




end LatticeProb

end
