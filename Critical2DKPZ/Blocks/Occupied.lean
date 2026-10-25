/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-! # Ordered occupied blocks in a discrepancy string -/

@[expose] public noncomputable section

namespace Critical2DKPZ.Blocks

/-- The occupied blocks, including the two prescribed endpoints. -/
def occupiedIndex (u v : ℕ) (S : Finset ℕ) (j : Fin (S.card + 2)) : ℕ :=
  (u :: (S.sort (· ≤ ·) ++ [v])).getD j 0

/-- The left time endpoint of an occupied block. -/
def occupiedLo (t : ℕ → ℕ) (u v : ℕ) (S : Finset ℕ) (j : Fin (S.card + 2)) : ℕ :=
  t (occupiedIndex u v S j - 1)

/-- The right time endpoint of an occupied block. -/
def occupiedHi (t : ℕ → ℕ) (u v : ℕ) (S : Finset ℕ) (j : Fin (S.card + 2)) : ℕ :=
  t (occupiedIndex u v S j)

/-- The occupied index enumeration starts at the left endpoint. -/
theorem occupiedIndex_zero (u v : ℕ) (S : Finset ℕ) :
    occupiedIndex u v S 0 = u := by
  simp [occupiedIndex]

/-- The occupied index enumeration ends at the right endpoint. -/
theorem occupiedIndex_last (u v : ℕ) (S : Finset ℕ) :
    occupiedIndex u v S (Fin.last (S.card + 1)) = v := by
  unfold occupiedIndex
  rw [List.getD_eq_getElem]
  · simp
  · simp

/-- The occupied index enumeration is strictly increasing when occupied times lie strictly between the endpoints. -/
theorem occupiedIndex_strictMono {u v : ℕ} {S : Finset ℕ}
    (huv : u < v) (hS : S ⊆ Finset.Ioo u v) :
    StrictMono (occupiedIndex u v S) := by
  have hsorted : (u :: (S.sort (· ≤ ·) ++ [v])).SortedLT := by
    apply List.Pairwise.sortedLT
    rw [List.pairwise_cons, List.pairwise_append]
    refine ⟨?_, S.sortedLT_sort.pairwise, by simp, ?_⟩
    · intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · exact (Finset.mem_Ioo.1 (hS (Finset.mem_sort _ |>.1 ha))).1
      · have haeq : a = v := List.mem_singleton.1 ha
        exact haeq ▸ huv
    · intro a ha b hb
      have hab := (Finset.mem_Ioo.1 (hS (Finset.mem_sort _ |>.1 ha))).2
      simp only [List.mem_singleton] at hb
      simpa only [hb] using hab
  intro i j hij
  have hi : (i : ℕ) < (u :: (S.sort (· ≤ ·) ++ [v])).length := by
    simpa only [List.length_cons, List.length_append, List.length_singleton,
      Finset.length_sort, List.length_nil, Nat.add_assoc] using i.isLt
  have hj : (j : ℕ) < (u :: (S.sort (· ≤ ·) ++ [v])).length := by
    simpa only [List.length_cons, List.length_append, List.length_singleton,
      Finset.length_sort, List.length_nil, Nat.add_assoc] using j.isLt
  simpa only [occupiedIndex, List.getD_eq_getElem _ _ hi,
    List.getD_eq_getElem _ _ hj, List.get_eq_getElem] using
    hsorted.strictMono_get (show (⟨i, hi⟩ : Fin _) < ⟨j, hj⟩ from hij)

/-- The unoccupied gaps telescope between the prescribed endpoints. -/
theorem sum_occupiedIndex_gap {u v : ℕ} {S : Finset ℕ}
    (huv : u < v) (hS : S ⊆ Finset.Ioo u v) :
    ∑ j : Fin (S.card + 1),
      (occupiedIndex u v S j.succ - occupiedIndex u v S j.castSucc - 1)
      = v - u - 1 - S.card := by
  let f := occupiedIndex u v S
  have hmono := occupiedIndex_strictMono huv hS
  have hstep (j : Fin (S.card + 1)) : f j.castSucc < f j.succ :=
    hmono (by exact Nat.lt_succ_self j.val)
  change (∑ j : Fin (S.card + 1), (f j.succ - f j.castSucc - 1)) = _
  rw [Finset.sum_tsub_distrib (Finset.univ : Finset (Fin (S.card + 1)))
    (f := fun j => f j.succ - f j.castSucc)
    (g := fun _ => 1) (by intro j _; have := hstep j; omega)]
  rw [Finset.sum_tsub_distrib (Finset.univ : Finset (Fin (S.card + 1)))
    (f := fun j => f j.succ) (g := fun j => f j.castSucc) (fun j _ => (hstep j).le)]
  have hleft := Fin.sum_univ_succ f
  have hright := Fin.sum_univ_castSucc f
  have hzero : f 0 = u := occupiedIndex_zero u v S
  have hlast : f (Fin.last (S.card + 1)) = v := occupiedIndex_last u v S
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one]
  omega

end Critical2DKPZ.Blocks
