/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitSpectators
public import Critical2DKPZ.SHF.Tsai.DiagramSpectatorFactorization
public import Critical2DKPZ.SHF.DeltaBose.EndpointSymmetry
import Critical2DKPZ.Collision.RenewalStringCells
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic

/-! # One-letter diagram factorization -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

private theorem diagramKernel_onePair_card_cast {n k : ℕ} (S : Finset (Fin n))
    (hcard : S.card = k) (β : CollisionPair k) (θ t : ℝ) (x y : Configuration n) :
    diagramKernel θ [hcard.symm ▸ β] t
      (fun i => x (S.orderEmbOfFin rfl i))
      (fun i => y (S.orderEmbOfFin rfl i)) =
    diagramKernel θ [β] t
      (fun i => x (S.orderEmbOfFin hcard i))
      (fun i => y (S.orderEmbOfFin hcard i)) := by
  cases hcard
  rfl

/-- A single collision diagram factors into its pair diagram and free spectator strands. -/
theorem diagramKernel_single_eq (θ : ℝ) {h : ℕ} (α : CollisionPair h) (t : ℝ)
    (x y : Configuration h) :
    diagramKernel θ [α] t x y =
      diagramKernel θ [pairTwo] t (pairRestrict α x) (pairRestrict α y) *
        ∏ i : Spectator α, ENNReal.ofReal (heatKernel t (y i.1 - x i.1)) := by
  classical
  let S : Finset (Fin h) := {α.1.1, α.1.2}
  have hfst : α.1.1 ∈ S := by simp [S]
  have hsnd : α.1.2 ∈ S := by simp [S]
  have hcard : S.card = 2 := by simp [S, ne_of_lt α.2]
  let γ : CollisionPair S.card := hcard.symm ▸ pairTwo
  have hγ : γ = Critical2DKPZ.SHF.Tsai.collisionPairWithin S α hfst hsnd := by
    have hsub : Subsingleton (CollisionPair S.card) := by
      rw [hcard]
      infer_instance
    exact hsub.elim _ _
  have hRel : List.Forall₂
      (fun β γ' => ∃ h₁ : β.1.1 ∈ S, ∃ h₂ : β.1.2 ∈ S,
        γ' = Critical2DKPZ.SHF.Tsai.collisionPairWithin S β h₁ h₂)
      [α] [γ] :=
    List.Forall₂.cons ⟨hfst, hsnd, hγ⟩ List.Forall₂.nil
  have hmap : (fun j : Fin 2 => if j = 0 then α.1.1 else α.1.2) =
      S.orderEmbOfFin hcard := by
    apply Finset.orderEmbOfFin_unique hcard
    · intro j
      fin_cases j <;> simp [S]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [α.2]
  have hspectOut (i : Spectator α) : i.1 ∉ S := by
    simp [S, i.2.1, i.2.2]
  let e₁ : Spectator α ≃ {i : Spectator α // i.1 ∉ S} :=
    { toFun := fun i => ⟨i, hspectOut i⟩
      invFun := fun i => i.1
      left_inv := fun _ => rfl
      right_inv := fun i => by apply Subtype.ext; rfl }
  let e := e₁.trans (Critical2DKPZ.SHF.Tsai.spectatorOutsideEquiv S α hfst hsnd)
  by_cases ht : 0 < t
  · have hf := Critical2DKPZ.SHF.Tsai.diagramKernel_subset_factor_of_forall₂
      S θ [α] [γ] hRel ht x y
    have hred : diagramKernel θ [γ] t
        (fun i => x (S.orderEmbOfFin rfl i))
        (fun i => y (S.orderEmbOfFin rfl i)) =
        diagramKernel θ [pairTwo] t (pairRestrict α x) (pairRestrict α y) := by
      calc
        _ = diagramKernel θ [pairTwo] t
            (fun i => x (S.orderEmbOfFin hcard i))
            (fun i => y (S.orderEmbOfFin hcard i)) := by
              exact diagramKernel_onePair_card_cast S hcard pairTwo θ t x y
        _ = _ := by
          rw [← hmap]
          have hx :
              (fun i : Fin 2 => x (if i = 0 then α.1.1 else α.1.2)) =
                pairRestrict α x := by
            funext i
            fin_cases i <;> simp [pairRestrict]
          have hy :
              (fun i : Fin 2 => y (if i = 0 then α.1.1 else α.1.2)) =
                pairRestrict α y := by
            funext i
            fin_cases i <;> simp [pairRestrict]
          rw [hx, hy]
    have hprod :
        (∏ j : Fin Sᶜ.card,
          ENNReal.ofReal (heatKernel t
            (y (Sᶜ.orderEmbOfFin rfl j) - x (Sᶜ.orderEmbOfFin rfl j)))) =
          ∏ i : Spectator α,
            ENNReal.ofReal (heatKernel t (y i.1 - x i.1)) := by
      let f : Fin Sᶜ.card → ℝ≥0∞ := fun j =>
        ENNReal.ofReal (heatKernel t
          (y (Sᶜ.orderEmbOfFin rfl j) - x (Sᶜ.orderEmbOfFin rfl j)))
      have heval (i : Spectator α) : Sᶜ.orderEmbOfFin rfl (e i) = i.1 := by
        dsimp [e, e₁, Critical2DKPZ.SHF.Tsai.spectatorOutsideEquiv]
        change ((Sᶜ.orderIsoOfFin rfl)
          ((Sᶜ.orderIsoOfFin rfl).symm
            ⟨i.1, Finset.mem_compl.mpr (hspectOut i)⟩)).1 = i.1
        exact congrArg Subtype.val ((Sᶜ.orderIsoOfFin rfl).apply_symm_apply
          ⟨i.1, Finset.mem_compl.mpr (hspectOut i)⟩)
      calc
        _ = ∏ i : Spectator α, f (e i) :=
          (Equiv.prod_comp e f).symm
        _ = _ := by
          apply Finset.prod_congr rfl
          intro i hi
          simp [f, heval i]
    rw [hf, hred, hprod]
  · have htn : t ≤ 0 := le_of_not_gt ht
    rw [diagramKernel_of_nonpos θ (by simp) htn x y,
      diagramKernel_of_nonpos θ (by simp) htn (pairRestrict α x) (pairRestrict α y)]
    simp

end Critical2DKPZ.SHF.Moments
