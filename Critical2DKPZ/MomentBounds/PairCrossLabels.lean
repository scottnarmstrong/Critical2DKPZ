/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.PairStratumEncoding
import Mathlib.Tactic

/-! # Select outside labels for two distinct collision pairs -/

@[expose] public section

namespace Critical2DKPZ.MomentBounds

/-- The two replica labels belonging to a collision pair. -/
def collisionPairLabels {h : ℕ} (α : DeltaBose.CollisionPair h) : Finset (Fin h) :=
  {α.val.1, α.val.2}

private theorem collisionPairLabels_card {h : ℕ} (α : DeltaBose.CollisionPair h) :
    (collisionPairLabels α).card = 2 := by
  simp [collisionPairLabels, ne_of_lt α.property]

private theorem collisionPairLabels_injective {h : ℕ} {α β : DeltaBose.CollisionPair h}
    (he : collisionPairLabels α = collisionPairLabels β) : α = β := by
  rcases α with ⟨⟨a, b⟩, hab⟩
  rcases β with ⟨⟨c, d⟩, hcd⟩
  have habN : a.val < b.val := (Fin.lt_def).mp hab
  have hcdN : c.val < d.val := (Fin.lt_def).mp hcd
  have haN : a.val = c.val ∨ a.val = d.val := by
    have ha : a = c ∨ a = d := by
      have hmem : a ∈ collisionPairLabels ⟨(a, b), hab⟩ := by simp [collisionPairLabels]
      rw [he] at hmem
      simpa [collisionPairLabels] using hmem
    rcases ha with ha | ha
    · exact Or.inl (congrArg Fin.val ha)
    · exact Or.inr (congrArg Fin.val ha)
  have hbN : b.val = c.val ∨ b.val = d.val := by
    have hb : b = c ∨ b = d := by
      have hmem : b ∈ collisionPairLabels ⟨(a, b), hab⟩ := by simp [collisionPairLabels]
      rw [he] at hmem
      simpa [collisionPairLabels] using hmem
    rcases hb with hb | hb
    · exact Or.inl (congrArg Fin.val hb)
    · exact Or.inr (congrArg Fin.val hb)
  apply Subtype.ext
  apply Prod.ext
  · rcases haN with hac | had <;> rcases hbN with hbc | hbd
    · apply Fin.ext
      omega
    · apply Fin.ext
      exact hac
    · apply Fin.ext
      omega
    · apply Fin.ext
      omega
  · rcases haN with hac | had <;> rcases hbN with hbc | hbd
    · apply Fin.ext
      omega
    · apply Fin.ext
      omega
    · apply Fin.ext
      omega
    · apply Fin.ext
      exact hbd

/-- Two different pair strata admit a label from each pair outside the other.
The complementary endpoints then provide the two collision coordinates needed
for the row and transposed-column estimates. -/
theorem exists_pairCrossLabels {h : ℕ} (α β : DeltaBose.CollisionPair h) (hne : α ≠ β) :
    ∃ k l m n : Fin h,
      ((k = α.val.1 ∧ l = α.val.2) ∨ (k = α.val.2 ∧ l = α.val.1)) ∧
      ((m = β.val.1 ∧ n = β.val.2) ∨ (m = β.val.2 ∧ n = β.val.1)) ∧
      k ∉ collisionPairLabels β ∧ m ∉ collisionPairLabels α := by
  classical
  have hnotA : ¬ collisionPairLabels α ⊆ collisionPairLabels β := by
    intro hsub
    have heq : collisionPairLabels α = collisionPairLabels β :=
      Finset.eq_of_subset_of_card_le hsub (by rw [collisionPairLabels_card, collisionPairLabels_card])
    exact hne (collisionPairLabels_injective heq)
  have hnotB : ¬ collisionPairLabels β ⊆ collisionPairLabels α := by
    intro hsub
    have heq : collisionPairLabels β = collisionPairLabels α :=
      Finset.eq_of_subset_of_card_le hsub (by rw [collisionPairLabels_card, collisionPairLabels_card])
    exact hne (collisionPairLabels_injective heq.symm)
  obtain ⟨k, hkA, hknotB⟩ := Finset.not_subset.mp hnotA
  obtain ⟨m, hmB, hmnotA⟩ := Finset.not_subset.mp hnotB
  have hkCases : k = α.val.1 ∨ k = α.val.2 := by
    simpa [collisionPairLabels] using hkA
  have hmCases : m = β.val.1 ∨ m = β.val.2 := by
    simpa [collisionPairLabels] using hmB
  let l : Fin h := if k = α.val.1 then α.val.2 else α.val.1
  let n : Fin h := if m = β.val.1 then β.val.2 else β.val.1
  have hlCases : (k = α.val.1 ∧ l = α.val.2) ∨ (k = α.val.2 ∧ l = α.val.1) := by
    rcases hkCases with hk | hk
    · exact Or.inl ⟨hk, by simp [l, hk]⟩
    · have hka : k ≠ α.val.1 := by
        intro hka
        exact (ne_of_lt α.property) (hka.symm.trans hk)
      exact Or.inr ⟨hk, by simp [l, hk]⟩
  have hnCases : (m = β.val.1 ∧ n = β.val.2) ∨ (m = β.val.2 ∧ n = β.val.1) := by
    rcases hmCases with hm | hm
    · exact Or.inl ⟨hm, by simp [n, hm]⟩
    · have hma : m ≠ β.val.1 := by
        intro hma
        exact (ne_of_lt β.property) (hma.symm.trans hm)
      exact Or.inr ⟨hm, by simp [n, hm]⟩
  exact ⟨k, l, m, n, hlCases, hnCases, hknotB, hmnotA⟩

/-- The outside-endpoint selection supplies exactly the distinct labels and
spectator equivalences required by the two weighted row bounds. -/
theorem exists_pairCrossSpectators {h : ℕ} (α β : DeltaBose.CollisionPair h) (hne : α ≠ β) :
    ∃ m n k l : Fin h,
      m ≠ n ∧ m ≠ k ∧ m ≠ l ∧ k ≠ l ∧ k ≠ m ∧ k ≠ n ∧
      ((k = α.val.1 ∧ l = α.val.2) ∨ (k = α.val.2 ∧ l = α.val.1)) ∧
      ((m = β.val.1 ∧ n = β.val.2) ∨ (m = β.val.2 ∧ n = β.val.1)) ∧
      Nonempty (PairSpectatorLabels h m k l ≃ Fin (h - 3)) ∧
      Nonempty (PairSpectatorLabels h k m n ≃ Fin (h - 3)) := by
  classical
  obtain ⟨k, l, m, n, hklPair, hmnPair, hkout, hmout⟩ := exists_pairCrossLabels α β hne
  have hkA : k ∈ collisionPairLabels α := by
    rcases hklPair with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [collisionPairLabels]
  have hlA : l ∈ collisionPairLabels α := by
    rcases hklPair with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [collisionPairLabels]
  have hmB : m ∈ collisionPairLabels β := by
    rcases hmnPair with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp [collisionPairLabels]
  have hnB : n ∈ collisionPairLabels β := by
    rcases hmnPair with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [collisionPairLabels]
  have hmk : m ≠ k := by
    intro he
    exact hmout (he ▸ hkA)
  have hml : m ≠ l := by
    intro he
    exact hmout (he ▸ hlA)
  have hkl : k ≠ l := by
    rcases hklPair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ne_of_lt α.property
    · exact (ne_of_lt α.property).symm
  have hmn : m ≠ n := by
    rcases hmnPair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ne_of_lt β.property
    · exact (ne_of_lt β.property).symm
  have hkm : k ≠ m := hmk.symm
  have hkn : k ≠ n := by
    intro he
    exact hkout (he ▸ hnB)
  exact ⟨m, n, k, l, hmn, hmk, hml, hkl, hkm, hkn, hklPair, hmnPair,
    ⟨pairSpectatorEquivFin m k l hmk hml hkl⟩,
    ⟨pairSpectatorEquivFin k m n hkm hkn hmn⟩⟩

end Critical2DKPZ.MomentBounds
