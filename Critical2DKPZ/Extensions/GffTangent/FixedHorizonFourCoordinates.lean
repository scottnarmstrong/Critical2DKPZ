/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonFourthPartitions
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! # Product coordinates for two disjoint collision pairs -/

@[expose] public noncomputable section

open Critical2DKPZ.MomentBounds Critical2DKPZ.DeltaBose
open scoped BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- Endpoints from disjoint collision pairs are distinct across the pairs. -/
theorem disjoint_pair_cross_ne (α δ : CollisionPair 4)
    (hd : Disjoint (collisionPairLabels α) (collisionPairLabels δ)) :
    α.1.1 ≠ δ.1.1 ∧ α.1.1 ≠ δ.1.2 ∧ α.1.2 ≠ δ.1.1 ∧ α.1.2 ≠ δ.1.2 := by
  have hn (i : Fin 4) (hi : i ∈ collisionPairLabels α) : i ∉ collisionPairLabels δ :=
    fun hm => Finset.disjoint_left.mp hd hi hm
  have ha := hn α.1.1 (by simp [collisionPairLabels])
  have hb := hn α.1.2 (by simp [collisionPairLabels])
  simpa only [collisionPairLabels, Finset.mem_insert, Finset.mem_singleton,
    not_or, and_assoc] using And.intro ha hb

/-- The four labels of two disjoint pairs enumerate all four replicas. -/
def disjointPairLabelEquiv (α δ : CollisionPair 4)
    (hd : Disjoint (collisionPairLabels α) (collisionPairLabels δ)) : Fin 4 ≃ Fin 4 := by
  let e : Fin 4 → Fin 4 := ![α.1.1, α.1.2, δ.1.1, δ.1.2]
  obtain ⟨hac, had, hbc, hbd⟩ := disjoint_pair_cross_ne α δ hd
  have hab : α.1.1 ≠ α.1.2 := ne_of_lt α.2
  have hcd : δ.1.1 ≠ δ.1.2 := ne_of_lt δ.2
  have he : Function.Injective e := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      dsimp only [e] at hij ⊢
      <;> first | rfl | exact (hab hij).elim | exact (hab hij.symm).elim |
        exact (hac hij).elim | exact (hac hij.symm).elim |
        exact (had hij).elim | exact (had hij.symm).elim |
        exact (hbc hij).elim | exact (hbc hij.symm).elim |
        exact (hbd hij).elim | exact (hbd hij.symm).elim |
        exact (hcd hij).elim | exact (hcd hij.symm).elim
  exact Equiv.ofBijective e ⟨he, Finite.surjective_of_injective he⟩

/-- A four-replica configuration written as the two selected site pairs. -/
def disjointPairConfigurationEquiv (α δ : CollisionPair 4)
    (hd : Disjoint (collisionPairLabels α) (collisionPairLabels δ)) :
    LatticeConfiguration 4 ≃ (Site × Site) × (Site × Site) where
  toFun x := ((x α.1.1, x α.1.2), (x δ.1.1, x δ.1.2))
  invFun p := fun i => ![p.1.1, p.1.2, p.2.1, p.2.2]
    ((disjointPairLabelEquiv α δ hd).symm i)
  left_inv x := by
    funext i
    let e := disjointPairLabelEquiv α δ hd
    have heval (j : Fin 4) : ![x α.1.1, x α.1.2, x δ.1.1, x δ.1.2] j = x (e j) := by
      fin_cases j <;> rfl
    change ![x α.1.1, x α.1.2, x δ.1.1, x δ.1.2] (e.symm i) = x i
    rw [heval, e.apply_symm_apply]
  right_inv p := by
    have he (j : Fin 4) : (disjointPairLabelEquiv α δ hd).symm
        ((disjointPairLabelEquiv α δ hd) j) = j := Equiv.symm_apply_apply _ j
    have h0 := he 0
    have h1 := he 1
    have h2 := he 2
    have h3 := he 3
    change ((![p.1.1, p.1.2, p.2.1, p.2.2] ((disjointPairLabelEquiv α δ hd).symm α.1.1),
      ![p.1.1, p.1.2, p.2.1, p.2.2] ((disjointPairLabelEquiv α δ hd).symm α.1.2)),
      (![p.1.1, p.1.2, p.2.1, p.2.2] ((disjointPairLabelEquiv α δ hd).symm δ.1.1),
      ![p.1.1, p.1.2, p.2.1, p.2.2] ((disjointPairLabelEquiv α δ hd).symm δ.1.2))) = p
    change (disjointPairLabelEquiv α δ hd).symm α.1.1 = 0 at h0
    change (disjointPairLabelEquiv α δ hd).symm α.1.2 = 1 at h1
    change (disjointPairLabelEquiv α δ hd).symm δ.1.1 = 2 at h2
    change (disjointPairLabelEquiv α δ hd).symm δ.1.2 = 3 at h3
    simp only [h0, h1, h2, h3]
    rfl

/-- Products over the four replicas factor into the two disjoint pairs. -/
theorem prod_disjointPair_labels (α δ : CollisionPair 4)
    (hd : Disjoint (collisionPairLabels α) (collisionPairLabels δ)) (F : Fin 4 → ℝ) :
    (∏ i : Fin 4, F i) = (F α.1.1 * F α.1.2) * (F δ.1.1 * F δ.1.2) := by
  have he := Fintype.prod_equiv (disjointPairLabelEquiv α δ hd)
    (fun j => F (disjointPairLabelEquiv α δ hd j)) F (fun _ => rfl)
  rw [← he]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change F α.1.1 * (F α.1.2 * (F δ.1.1 * (F δ.1.2 * 1))) = _
  ring

end Critical2DKPZ.Extensions.GffTangent
