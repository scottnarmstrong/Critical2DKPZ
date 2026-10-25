/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-! # Partitions with endpoints in a dense time set

Choose one dense-time point in each open cell of a uniform grid. Adjoining
the two fixed endpoints gives positive increments of size at most twice
the grid spacing, which is the maximum-mesh condition used in uniqueness.
-/

@[expose] public noncomputable section

open Set

namespace Critical2DKPZ.SHF.Tsai

/-- Density on a closed interval supplies a point in each nontrivial subinterval. -/
theorem exists_mem_Ioo_of_subset_closure {D : Set ℝ} {s t a b : ℝ}
    (hD : Icc s t ⊆ closure D) (hsa : s ≤ a) (hab : a < b) (hbt : b ≤ t) :
    ∃ x ∈ D, a < x ∧ x < b := by
  have hm : (a + b) / 2 ∈ Icc s t := ⟨by linarith, by linarith⟩
  obtain ⟨x, hx, hxD⟩ := mem_closure_iff.1 (hD hm) (Ioo a b) isOpen_Ioo
    (show (a + b) / 2 ∈ Ioo a b from ⟨by linarith, by linarith⟩)
  exact ⟨x, hxD, hx⟩

/-- A positive uniform grid admits a dense-time partition with maximum gap at most twice its spacing. -/
theorem exists_dense_partition {D : Set ℝ} {s t : ℝ}
    (hD : Icc s t ⊆ closure D) (hs : s ∈ D) (ht : t ∈ D) (hst : s < t)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ r : ℕ → ℝ, r 0 = s ∧ r (n + 1) = t ∧
      (∀ i ≤ n + 1, r i ∈ D) ∧
      ∀ i < n + 1, 0 < r (i + 1) - r i ∧ r (i + 1) - r i ≤ 2 * ((t - s) / n) := by
  classical
  let d : ℝ := (t - s) / n
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hd : 0 < d := div_pos (sub_pos.mpr hst) hn0
  have hnd : (n : ℝ) * d = t - s := by dsimp only [d]; field_simp
  have hCell (i : Fin n) : ∃ x ∈ D, s + (i : ℝ) * d < x ∧ x < s + ((i : ℝ) + 1) * d := by
    apply exists_mem_Ioo_of_subset_closure hD
    · nlinarith [show (0 : ℝ) ≤ (i : ℕ) from Nat.cast_nonneg _]
    · linarith
    · have hi : (i : ℝ) + 1 ≤ n := by exact_mod_cast i.is_lt
      nlinarith
  choose x hxD hx using hCell
  let r (k : ℕ) : ℝ := if hk0 : k = 0 then s else
    if hk : k ≤ n then x ⟨k - 1, by omega⟩ else t
  have hr0 : r 0 = s := by simp only [r, dite_true]
  have hrend : r (n + 1) = t := by simp only [r, Nat.add_one_ne_zero, dite_false, Nat.not_succ_le_self]
  have hrmid (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
      r k = x ⟨k - 1, by omega⟩ := by
    simp only [r, dite_eq_right (by omega : k ≠ 0), dite_eq_left hkn]
  refine ⟨r, hr0, hrend, ?_, ?_⟩
  · intro i hi
    by_cases hi0 : i = 0
    · subst i
      rwa [hr0]
    by_cases hin : i ≤ n
    · rw [hrmid i (by omega) hin]
      exact hxD _
    · have hie : i = n + 1 := by omega
      subst i
      rwa [hrend]
  · intro i hi
    by_cases hi0 : i = 0
    · subst i
      rw [hr0, hrmid 1 le_rfl hn]
      have h := hx (⟨0, by omega⟩ : Fin n)
      simp only [Nat.cast_zero, zero_mul, zero_add] at h
      constructor <;> dsimp only [d] at * <;> linarith
    by_cases hin : i = n
    · subst i
      rw [hrend, hrmid n hn le_rfl]
      have h := hx (⟨n - 1, by omega⟩ : Fin n)
      simp only [Nat.cast_sub hn, Nat.cast_one] at h
      constructor <;> nlinarith
    · have hi1 : 1 ≤ i := by omega
      have hin' : i + 1 ≤ n := by omega
      rw [hrmid i hi1 (by omega), hrmid (i + 1) (by omega) hin']
      have hleft := hx (⟨i - 1, by omega⟩ : Fin n)
      have hright := hx (⟨i, by omega⟩ : Fin n)
      simp only [Nat.cast_sub hi1, Nat.cast_one] at hleft
      simp only [Nat.add_sub_cancel] at *
      constructor <;> nlinarith

end Critical2DKPZ.SHF.Tsai

end
