/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.LatticeShells
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-! # Finite radial reductions for planar lattice sums -/

public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

/-- The radius-zero lattice box consists only of the origin. -/
theorem latticeBox_zero : latticeBox 0 = {0} := by
  ext z
  rw [mem_latticeBox, Nat.le_zero, latticeRadius_eq_zero_iff, Finset.mem_singleton]

/-- A sum over the next lattice box splits into the previous box and the new shell. -/
theorem sum_latticeBox_succ (f : Site → ℝ) (k : ℕ) :
    (∑ z ∈ latticeBox (k + 1), f z) =
      (∑ z ∈ latticeBox k, f z) + ∑ z ∈ latticeShell k, f z := by
  have h := Finset.sum_sdiff (f := f) (latticeBox_mono (Nat.le_succ k))
  change (∑ z ∈ latticeShell k, f z) + (∑ z ∈ latticeBox k, f z) = _ at h
  rw [← h, add_comm]

/-- A sum over a lattice box equals its value at the origin plus its shell sums. -/
theorem sum_latticeBox_eq_shells (f : Site → ℝ) (k : ℕ) :
    (∑ z ∈ latticeBox k, f z) = f 0 +
      ∑ j ∈ Finset.range k, ∑ z ∈ latticeShell j, f z := by
  induction k with
  | zero => rw [latticeBox_zero, Finset.sum_singleton, Finset.sum_range_zero, add_zero]
  | succ k ih => rw [sum_latticeBox_succ, ih, Finset.sum_range_succ, add_assoc]

/-- A radial majorant is summed with the exact shell multiplicity. -/
theorem sum_latticeBox_le_radial (f : Site → ℝ) (F : ℕ → ℝ) (k : ℕ)
    (hF : ∀ j, ∀ z ∈ latticeShell j, f z ≤ F (j + 1)) :
    (∑ z ∈ latticeBox k, f z) ≤ f 0 +
      ∑ j ∈ Finset.range k, (8 * ((j : ℝ) + 1)) * F (j + 1) := by
  rw [sum_latticeBox_eq_shells]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro j _
  calc
    _ ≤ ∑ _z ∈ latticeShell j, F (j + 1) := Finset.sum_le_sum (hF j)
    _ = _ := by rw [Finset.sum_const, card_latticeShell, nsmul_eq_mul]; push_cast; rfl

/-- Every finite set of lattice sites lies in one of the squares. -/
theorem exists_subset_latticeBox (s : Finset Site) : ∃ k : ℕ, s ⊆ latticeBox k := by
  classical
  refine ⟨∑ z ∈ s, latticeRadius z, fun z hz => ?_⟩
  rw [mem_latticeBox]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hz

/-- Bounds on the square cutoffs imply summability and the same bound on the full sum. -/
theorem summable_and_tsum_le_of_latticeBox_bound {f : Site → ℝ} (hf : ∀ z, 0 ≤ f z)
    {C : ℝ} (hC : ∀ k, (∑ z ∈ latticeBox k, f z) ≤ C) :
    Summable f ∧ (∑' z, f z) ≤ C := by
  have hbound (s : Finset Site) : (∑ z ∈ s, f z) ≤ C := by
    obtain ⟨k, hk⟩ := exists_subset_latticeBox s
    exact (Finset.sum_le_sum_of_subset_of_nonneg hk (fun z _ _ => hf z)).trans (hC k)
  exact ⟨summable_of_sum_le hf hbound, Real.tsum_le_of_sum_le hf hbound⟩

end Critical2DKPZ.MomentBounds
