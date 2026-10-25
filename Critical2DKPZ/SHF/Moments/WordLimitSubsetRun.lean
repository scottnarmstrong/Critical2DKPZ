/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationTerminalRecursion
public import Mathlib.Tactic
public import Critical2DKPZ.SHF.Tsai.DiagramSpectatorFactorization
import Mathlib.Tactic

/-! # Subset factorization of a lattice collision run -/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- If a pair is contained in a selected label set, its run factor separates
into the run on those labels and free transitions on the complementary labels. -/
theorem pairRunFactor_subset_factor {n : ℕ} (S : Finset (Fin n)) (β : ℝ)
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S)
    (r : ℕ) (u v : LatticeConfiguration n) :
    collisionWordUndampedPairRunFactor β α r u v =
      collisionWordUndampedPairRunFactor β (Tsai.collisionPairWithin S α h₁ h₂) r
        (fun j => u (S.orderEmbOfFin rfl j))
        (fun j => v (S.orderEmbOfFin rfl j)) *
      ∏ j : Fin Sᶜ.card, srwKernel r
        (v (Sᶜ.orderEmbOfFin rfl j) - u (Sᶜ.orderEmbOfFin rfl j)) := by
  classical
  let a := S.orderEmbOfFin rfl
  let c := Sᶜ.orderEmbOfFin rfl
  let γ := Tsai.collisionPairWithin S α h₁ h₂
  have hfst : a γ.1.1 = α.1.1 := Tsai.orderEmb_collisionPairWithin_fst S α h₁ h₂
  have hsnd : a γ.1.2 = α.1.2 := Tsai.orderEmb_collisionPairWithin_snd S α h₁ h₂
  have hfirst (j : Fin S.card) : a j = α.1.1 ↔ j = γ.1.1 := by
    constructor
    · intro hj
      exact a.injective (hj.trans hfst.symm)
    · intro hj
      rw [hj, hfst]
  have hsecond (j : Fin S.card) : a j = α.1.2 ↔ j = γ.1.2 := by
    constructor
    · intro hj
      exact a.injective (hj.trans hsnd.symm)
    · intro hj
      rw [hj, hsnd]
  have hcfirst (j : Fin Sᶜ.card) : c j ≠ α.1.1 := by
    intro heq
    have hnot : c j ∉ S := Finset.mem_compl.mp (Sᶜ.orderEmbOfFin_mem rfl j)
    exact hnot (heq.symm ▸ h₁)
  have hcsecond (j : Fin Sᶜ.card) : c j ≠ α.1.2 := by
    intro heq
    have hnot : c j ∉ S := Finset.mem_compl.mp (Sᶜ.orderEmbOfFin_mem rfl j)
    exact hnot (heq.symm ▸ h₂)
  have hprod :
      (∏ i : Fin n, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ)
        else srwKernel r (v i - u i)) =
      (∏ j : Fin S.card, if j = γ.1.1 ∨ j = γ.1.2 then (1 : ℝ)
        else srwKernel r (v (a j) - u (a j))) *
        ∏ j : Fin Sᶜ.card, srwKernel r (v (c j) - u (c j)) := by
    calc
      _ = (∏ j : Fin S.card, if a j = α.1.1 ∨ a j = α.1.2 then (1 : ℝ)
          else srwKernel r (v (a j) - u (a j))) *
          ∏ j : Fin Sᶜ.card, if c j = α.1.1 ∨ c j = α.1.2 then (1 : ℝ)
            else srwKernel r (v (c j) - u (c j)) :=
        Tsai.prod_subset_mul_compl S _
      _ = _ := by
        congr 1
        · apply Finset.prod_congr rfl
          intro j hj
          simp only [hfirst, hsecond]
        · apply Finset.prod_congr rfl
          intro j hj
          simp only [hcfirst, hcsecond, false_or, ite_false]
  change collisionWordUndampedPairRunFactor β α r u v =
    collisionWordUndampedPairRunFactor β γ r (fun j => u (a j)) (fun j => v (a j)) *
      ∏ j : Fin Sᶜ.card, srwKernel r (v (c j) - u (c j))
  simp only [collisionWordUndampedPairRunFactor, hfst, hsnd]
  rw [hprod]
  ring

end Critical2DKPZ.SHF.Moments
