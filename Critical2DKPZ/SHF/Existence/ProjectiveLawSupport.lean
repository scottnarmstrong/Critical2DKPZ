/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Existence.SubsequenceLawTransfer
import Mathlib.Topology.Bases

/-! # Dense countable time windows -/

@[expose] public section

open Set

namespace Critical2DKPZ.SHF.Existence

/-- A bounded countable dense time set can be chosen to contain any finite list
of endpoints in the nonnegative half-line. -/
theorem exists_countable_dense_interval_with_finite_times {k : ℕ}
    (s t : Fin k → ℝ) (hTimes : ∀ i, 0 ≤ s i ∧ s i < t i) :
    ∃ B : ℝ, 0 < B ∧ ∃ D : Set ℝ, D.Countable ∧ D ⊆ Set.Icc 0 B ∧
      Set.Icc 0 B ⊆ closure D ∧ ∀ i, s i ∈ D ∧ t i ∈ D := by
  let B : ℝ := 1 + ∑ i : Fin k, (|s i| + |t i|)
  have hsum : 0 ≤ ∑ i : Fin k, (|s i| + |t i|) :=
    Finset.sum_nonneg fun i hi => add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hB : 0 < B := by dsimp [B]; linarith
  have hsB : ∀ i, s i ≤ B := by
    intro i
    have hterm : |s i| + |t i| ≤ ∑ j : Fin k, (|s j| + |t j|) :=
      Finset.single_le_sum (f := fun j : Fin k => |s j| + |t j|)
        (fun j hj => add_nonneg (abs_nonneg _) (abs_nonneg _))
        (Finset.mem_univ i)
    change s i ≤ 1 + ∑ j : Fin k, (|s j| + |t j|)
    calc
      s i ≤ |s i| := le_abs_self _
      _ ≤ |s i| + |t i| := le_add_of_nonneg_right (abs_nonneg _)
      _ ≤ ∑ j : Fin k, (|s j| + |t j|) := hterm
      _ ≤ 1 + ∑ j : Fin k, (|s j| + |t j|) :=
        le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
  have htB : ∀ i, t i ≤ B := by
    intro i
    have hterm : |s i| + |t i| ≤ ∑ j : Fin k, (|s j| + |t j|) :=
      Finset.single_le_sum (f := fun j : Fin k => |s j| + |t j|)
        (fun j hj => add_nonneg (abs_nonneg _) (abs_nonneg _))
        (Finset.mem_univ i)
    change t i ≤ 1 + ∑ j : Fin k, (|s j| + |t j|)
    calc
      t i ≤ |t i| := le_abs_self _
      _ ≤ |s i| + |t i| := le_add_of_nonneg_left (abs_nonneg _)
      _ ≤ ∑ j : Fin k, (|s j| + |t j|) := hterm
      _ ≤ 1 + ∑ j : Fin k, (|s j| + |t j|) :=
        le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨Q, hQcount, hQsub, hQdense⟩ :=
    TopologicalSpace.exists_countable_dense_subset (Set.Icc (0 : ℝ) B)
  let D : Set ℝ := Q ∪ (Set.range s ∪ Set.range t)
  have hDcount : D.Countable := by
    dsimp [D]
    exact hQcount.union ((Set.countable_range s).union (Set.countable_range t))
  have hDsub : D ⊆ Set.Icc 0 B := by
    intro x hx
    rcases hx with hx | hx
    · exact hQsub hx
    · rcases hx with hx | hx
      · obtain ⟨i, rfl⟩ := hx
        exact ⟨(hTimes i).1, hsB i⟩
      · obtain ⟨i, rfl⟩ := hx
        exact ⟨by linarith [(hTimes i).1, (hTimes i).2], htB i⟩
  have hDdense : Set.Icc 0 B ⊆ closure D := by
    exact hQdense.trans (closure_mono (subset_union_left : Q ⊆ D))
  refine ⟨B, hB, D, hDcount, hDsub, hDdense, ?_⟩
  intro i
  exact ⟨Or.inr (Or.inl ⟨i, rfl⟩), Or.inr (Or.inr ⟨i, rfl⟩)⟩

end Critical2DKPZ.SHF.Existence

end
