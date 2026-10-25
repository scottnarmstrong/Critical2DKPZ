/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-! # A common finite grid for finitely many strict time intervals

Sorting the finite union of all left and right endpoints gives a strictly
increasing grid containing every requested interval and staying in the
original time set.
-/

@[expose] public noncomputable section

namespace Critical2DKPZ.SHF.Tsai

/-- A nonempty finite family of strict intervals admits a common increasing grid of its endpoints. -/
theorem exists_common_time_grid (D : Set ℝ) {k : ℕ} (hk : 0 < k) (s t : Fin k → ℝ)
    (hst : ∀ i, s i ∈ D ∧ t i ∈ D ∧ s i < t i) :
    ∃ m : ℕ, ∃ q : Fin (m + 1) → ℝ, StrictMono q ∧ (∀ j, q j ∈ D) ∧
      ∃ a b : Fin k → Fin (m + 1), (∀ i, a i < b i) ∧ (∀ i, q (a i) = s i) ∧ ∀ i, q (b i) = t i := by
  classical
  let S : Finset ℝ := Finset.univ.image s ∪ Finset.univ.image t
  have hs (i : Fin k) : s i ∈ S :=
    Finset.mem_union_left _ (Finset.mem_image_of_mem s (Finset.mem_univ i))
  have ht (i : Fin k) : t i ∈ S :=
    Finset.mem_union_right _ (Finset.mem_image_of_mem t (Finset.mem_univ i))
  have hScard : 0 < S.card := Finset.card_pos.mpr ⟨s ⟨0, hk⟩, hs _⟩
  let m := S.card - 1
  have hcard : S.card = m + 1 := (Nat.sub_add_cancel (Nat.one_le_of_lt hScard)).symm
  let q := S.orderEmbOfFin hcard
  let a (i : Fin k) := (S.orderIsoOfFin hcard).symm ⟨s i, hs i⟩
  let b (i : Fin k) := (S.orderIsoOfFin hcard).symm ⟨t i, ht i⟩
  have hsa (i : Fin k) : q (a i) = s i := by
    change ((S.orderIsoOfFin hcard) ((S.orderIsoOfFin hcard).symm ⟨s i, hs i⟩) : ℝ) = s i
    rw [OrderIso.apply_symm_apply]
  have htb (i : Fin k) : q (b i) = t i := by
    change ((S.orderIsoOfFin hcard) ((S.orderIsoOfFin hcard).symm ⟨t i, ht i⟩) : ℝ) = t i
    rw [OrderIso.apply_symm_apply]
  have hqD (j : Fin (m + 1)) : q j ∈ D := by
    have hj : q j ∈ S := S.orderEmbOfFin_mem hcard j
    rcases Finset.mem_union.mp hj with hj | hj
    · obtain ⟨i, _hi, hi⟩ := Finset.mem_image.mp hj
      rw [← hi]
      exact (hst i).1
    · obtain ⟨i, _hi, hi⟩ := Finset.mem_image.mp hj
      rw [← hi]
      exact (hst i).2.1
  have hab (i : Fin k) : a i < b i := by
    apply q.strictMono.lt_iff_lt.mp
    rw [hsa, htb]
    exact (hst i).2.2
  exact ⟨m, q, q.strictMono, hqD, a, b, hab, hsa, htb⟩

end Critical2DKPZ.SHF.Tsai

end
