/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordExpansion
import Mathlib.Tactic

/-! # Pair-simple edge sets as optional chronological pair choices -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open DeltaBose

attribute [local instance] Classical.propDecidable

private def collisionWordSelectionFiber {n h : ℕ} (j : Fin n)
    (o : Option (CollisionPair h)) : Finset (ℕ × CollisionPair h) :=
  o.elim ∅ (fun α => {(j.val + 1, α)})

private def collisionWordPairSelectionEdges {n h : ℕ}
    (u : Fin n → Option (CollisionPair h)) : Finset (ℕ × CollisionPair h) :=
  Finset.univ.biUnion fun j => collisionWordSelectionFiber j (u j)

private theorem collisionWord_mem_selectionFiber {n h : ℕ} (j : Fin n)
    (o : Option (CollisionPair h)) (e : ℕ × CollisionPair h) :
    e ∈ collisionWordSelectionFiber j o ↔ ∃ α, o = some α ∧ e = (j.val + 1, α) := by
  cases o <;> simp [collisionWordSelectionFiber]

private theorem collisionWord_mem_selectionEdges {n h : ℕ}
    (u : Fin n → Option (CollisionPair h)) (e : ℕ × CollisionPair h) :
    e ∈ collisionWordPairSelectionEdges u ↔ ∃ j : Fin n, u j = some e.2 ∧ e.1 = j.val + 1 := by
  simp only [collisionWordPairSelectionEdges, Finset.mem_biUnion, Finset.mem_univ, true_and,
    collisionWord_mem_selectionFiber]
  constructor
  · rintro ⟨j, α, hu, he⟩
    subst e
    exact ⟨j, hu, rfl⟩
  · rintro ⟨j, hu, ht⟩
    exact ⟨j, e.2, hu, Prod.ext ht rfl⟩

private theorem collisionWord_mem_selectionEdges_at {n h : ℕ}
    (u : Fin n → Option (CollisionPair h)) (j : Fin n) (α : CollisionPair h) :
    (j.val + 1, α) ∈ collisionWordPairSelectionEdges u ↔ u j = some α := by
  rw [collisionWord_mem_selectionEdges]
  constructor
  · rintro ⟨k, hk, htime⟩
    have hkj : k = j := Fin.ext (by omega)
    simpa [hkj] using hk
  · intro hu
    exact ⟨j, hu, rfl⟩

private theorem collisionWord_selectionEdges_subset {n h : ℕ}
    (u : Fin n → Option (CollisionPair h)) :
    collisionWordPairSelectionEdges u ⊆ collisionEdges n h := by
  intro e he
  obtain ⟨j, hj, ht⟩ := (collisionWord_mem_selectionEdges u e).mp he
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, Finset.mem_univ _⟩

private theorem collisionWord_selectionEdges_simple {n h : ℕ}
    (u : Fin n → Option (CollisionPair h)) : IsPairSimple (collisionWordPairSelectionEdges u) := by
  intro e he e' he' ht
  obtain ⟨j, hj, htime⟩ := (collisionWord_mem_selectionEdges u e).mp he
  obtain ⟨k, hk, htime'⟩ := (collisionWord_mem_selectionEdges u e').mp he'
  have hjk : j = k := Fin.ext (by omega)
  subst k
  have hpair : e.2 = e'.2 := Option.some.inj (hj.symm.trans hk)
  exact Prod.ext ht hpair

private theorem collisionWord_selectionEdges_injective {n h : ℕ} :
    Function.Injective (collisionWordPairSelectionEdges :
      (Fin n → Option (CollisionPair h)) → Finset (ℕ × CollisionPair h)) := by
  intro u v he
  funext j
  have hsome (α : CollisionPair h) : u j = some α ↔ v j = some α := by
    rw [← collisionWord_mem_selectionEdges_at, he, collisionWord_mem_selectionEdges_at]
  cases hu : u j with
  | none =>
      cases hv : v j with
      | none => rfl
      | some α =>
          have h := (hsome α).mpr hv
          rw [hu] at h
          cases h
  | some α =>
      have h := (hsome α).mp hu
      exact h.symm

private theorem collisionWord_selectionEdges_surjective {n h : ℕ}
    (A : Finset (ℕ × CollisionPair h)) (hA : A ⊆ collisionEdges n h)
    (hsimple : IsPairSimple A) :
    ∃ u : Fin n → Option (CollisionPair h), collisionWordPairSelectionEdges u = A := by
  classical
  let u : Fin n → Option (CollisionPair h) := fun j =>
    if he : ∃ α, (j.val + 1, α) ∈ A then some he.choose else none
  have hchoice (j : Fin n) (α : CollisionPair h) :
      u j = some α ↔ (j.val + 1, α) ∈ A := by
    dsimp [u]
    split_ifs with he
    · constructor
      · intro h
        have heq := Option.some.inj h
        simpa [heq] using he.choose_spec
      · intro hα
        apply congrArg some
        exact congrArg Prod.snd (hsimple _ he.choose_spec _ hα rfl)
    · constructor
      · intro h
        cases h
      · intro hα
        exact (he ⟨α, hα⟩).elim
  refine ⟨u, ?_⟩
  ext e
  constructor
  · intro he
    obtain ⟨j, hu, ht⟩ := (collisionWord_mem_selectionEdges u e).mp he
    have hmem := (hchoice j e.2).mp hu
    have heq : e = (j.val + 1, e.2) := Prod.ext ht rfl
    exact heq.symm ▸ hmem
  · intro he
    have htime := (Finset.mem_product.mp (hA he)).1
    have ht := Finset.mem_Icc.mp htime
    let j : Fin n := ⟨e.1 - 1, by omega⟩
    have hj : e.1 = j.val + 1 := by dsimp [j]; omega
    apply (collisionWord_mem_selectionEdges u e).mpr
    have heq : e = (j.val + 1, e.2) := Prod.ext hj rfl
    exact ⟨j, (hchoice j e.2).mpr (heq ▸ he), hj⟩

private theorem collisionWord_selectionEdges_product {n h : ℕ}
    (u : Fin n → Option (CollisionPair h)) (f : (ℕ × CollisionPair h) → ℝ) :
    (∏ e ∈ collisionWordPairSelectionEdges u, f e) =
      ∏ j : Fin n, (u j).elim 1 (fun α => f (j.val + 1, α)) := by
  classical
  have hd : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin n)))
      (fun j => collisionWordSelectionFiber j (u j)) := by
    intro j hj k hk hjk
    apply Finset.disjoint_left.mpr
    intro e he he'
    obtain ⟨α, hα, hea⟩ := (collisionWord_mem_selectionFiber j (u j) e).mp he
    obtain ⟨β, hβ, heb⟩ := (collisionWord_mem_selectionFiber k (u k) e).mp he'
    apply hjk
    apply Fin.ext
    have ht := congrArg Prod.fst (hea.symm.trans heb)
    omega
  rw [collisionWordPairSelectionEdges, Finset.prod_biUnion hd]
  apply Finset.prod_congr rfl
  intro j hj
  cases hu : u j <;> simp [collisionWordSelectionFiber]

/-- Pair-simple edge selections are exactly independent optional pair
choices at the positive microscopic times. This identity is algebraic and
retains every time and pair convention of `collisionEdges`. -/
theorem sum_pairSimple_edge_products_eq_prod_one_add_sum (n h : ℕ)
    (f : (ℕ × CollisionPair h) → ℝ) :
    (∑ A ∈ (collisionEdges n h).powerset.filter IsPairSimple, ∏ e ∈ A, f e) =
      ∏ j : Fin n, (1 + ∑ α : CollisionPair h, f (j.val + 1, α)) := by
  classical
  have hsum :
      (∑ A ∈ (collisionEdges n h).powerset.filter IsPairSimple, ∏ e ∈ A, f e) =
        ∑ u : Fin n → Option (CollisionPair h),
          ∏ j : Fin n, (u j).elim 1 (fun α => f (j.val + 1, α)) := by
    symm
    apply Finset.sum_bij (fun u _ => collisionWordPairSelectionEdges u)
    · intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
        (collisionWord_selectionEdges_subset u), collisionWord_selectionEdges_simple u⟩
    · intro u hu v hv he
      exact collisionWord_selectionEdges_injective he
    · intro A hA
      obtain ⟨hsub, hs⟩ := Finset.mem_filter.mp hA
      obtain ⟨u, hu⟩ := collisionWord_selectionEdges_surjective A (Finset.mem_powerset.mp hsub) hs
      exact ⟨u, Finset.mem_univ _, hu⟩
    · intro u hu
      exact (collisionWord_selectionEdges_product u f).symm
  rw [hsum]
  let g : Fin n → Option (CollisionPair h) → ℝ :=
    fun j o => o.elim 1 (fun α => f (j.val + 1, α))
  change (∑ u : Fin n → Option (CollisionPair h), ∏ j : Fin n, g j (u j)) = _
  calc
    _ = ∏ j : Fin n, ∑ o : Option (CollisionPair h), g j o := (Fintype.prod_sum g).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j hj
      simp only [g, Fintype.sum_option, Option.elim_none, Option.elim_some]

end Critical2DKPZ.SHF.Moments

end
