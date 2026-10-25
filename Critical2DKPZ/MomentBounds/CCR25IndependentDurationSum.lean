/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25FiniteOperators
import Mathlib.Tactic

/-! # Bounding constrained sums of independent duration factors -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

universe u v

/-- The sum of a product over the full finite product of coordinate supports
is exactly the product of the coordinate sums. -/
theorem finite_sum_product_over_piFinset_eq_product_sums
    {α : Type u} {β : Type v} [Fintype α] [DecidableEq α]
    [DecidableEq β] (D : α → Finset β) (f : α → β → ℝ) :
    (∑ w ∈ Fintype.piFinset D, ∏ i, f i (w i)) =
      ∏ i, ∑ b ∈ D i, f i b := by
  classical
  let Sub : α → Type v := fun i => {b : β // b ∈ D i}
  let encode : (∀ i, Sub i) → α → β := fun w i => (w i).1
  have himage : Finset.image encode Finset.univ = Fintype.piFinset D := by
    ext w
    simp only [Finset.mem_image, Finset.mem_univ, true_and,
      Fintype.mem_piFinset]
    constructor
    · rintro ⟨v, rfl⟩ i
      exact (v i).2
    · intro hw
      exact ⟨fun i => ⟨w i, hw i⟩, by funext i; rfl⟩
  have hencode : Function.Injective encode := by
    intro u v huv
    funext i
    apply Subtype.ext
    exact congrFun huv i
  calc
    (∑ w ∈ Fintype.piFinset D, ∏ i, f i (w i)) =
        ∑ w ∈ Finset.image encode Finset.univ, ∏ i, f i (w i) := by
      rw [← himage]
    _ = ∑ w : (∀ i, Sub i), ∏ i, f i (w i).1 := by
      rw [Finset.sum_image (fun u hu v hv huv => hencode huv)]
    _ = ∏ i, ∑ b : Sub i, f i b.1 := by
      symm
      exact Fintype.prod_sum (f := fun (i : α) (b : Sub i) => f i b.1)
    _ = ∏ i, ∑ b ∈ D i, f i b := by
      apply Finset.prod_congr rfl
      intro i hi
      exact Finset.sum_coe_sort (D i) (fun b => f i b)


end Critical2DKPZ.MomentBounds
