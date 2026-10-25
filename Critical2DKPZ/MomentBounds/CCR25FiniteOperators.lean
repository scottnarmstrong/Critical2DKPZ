/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CollisionStrata
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-! # Finite weighted operator factorization for CCR25 Theorem 4.11 -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- The counting `ℓᵖ` seminorm on a finite state set. -/
def finiteLpNorm {α : Type*} (s : Finset α) (p : ℝ) (f : α → ℝ) : ℝ :=
  (∑ x ∈ s, |f x| ^ p) ^ (1 / p)

/-- A finite kernel acts on a column vector by summing its second coordinate. -/
def finiteKernelApply {α : Type*} (s : Finset α) (K : α → α → ℝ) (f : α → ℝ) : α → ℝ :=
  fun x => ∑ y ∈ s, K x y * f y

/-- Conjugation by a strictly positive weight, in the source's row/column convention. -/
def weightedKernel {α : Type*} (W : α → ℝ) (K : α → α → ℝ) : α → α → ℝ :=
  fun x y => W x * K x y / W y

/-- Apply an ordered word of kernels, with the first kernel acting outermost. -/
def finiteKernelWordApply {α : Type*} (s : Finset α) :
    List (α → α → ℝ) → (α → ℝ) → α → ℝ
  | [], f, x => f x
  | K :: Ks, f, x => ∑ y ∈ s, K x y * finiteKernelWordApply s Ks f y

/-- The finite Lᵖ norm is nonnegative. -/
theorem finiteLpNorm_nonneg {α : Type*} (s : Finset α) (p : ℝ) (f : α → ℝ) :
    0 ≤ finiteLpNorm s p f := by
  unfold finiteLpNorm
  apply Real.rpow_nonneg
  apply Finset.sum_nonneg
  intro x hx
  exact Real.rpow_nonneg (abs_nonneg _) _

/-- Conjugating every kernel in a word moves the endpoint weight through the
entire finite composition. -/
theorem finiteKernelWordApply_weighted {α : Type*} [DecidableEq α]
    (s : Finset α) (W : α → ℝ) (hW : ∀ x ∈ s, 0 < W x)
    (Ks : List (α → α → ℝ)) (f : α → ℝ) :
    ∀ x ∈ s,
      finiteKernelWordApply s (Ks.map (weightedKernel W)) (fun y => W y * f y) x =
        W x * finiteKernelWordApply s Ks f x := by
  induction Ks generalizing f with
  | nil =>
      intro x hx
      simp [finiteKernelWordApply]
  | cons K Ks ih =>
      intro x hx
      simp only [List.map_cons, finiteKernelWordApply]
      calc
        (∑ y ∈ s, weightedKernel W K x y *
            finiteKernelWordApply s (Ks.map (weightedKernel W)) (fun y => W y * f y) y) =
            ∑ y ∈ s, weightedKernel W K x y *
              (W y * finiteKernelWordApply s Ks f y) := by
                apply Finset.sum_congr rfl
                intro y hy
                rw [ih f y hy]
        _ = W x * ∑ y ∈ s, K x y * finiteKernelWordApply s Ks f y := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro y hy
              simp only [weightedKernel]
              field_simp [ne_of_gt (hW y hy)]



end

end Critical2DKPZ.MomentBounds
