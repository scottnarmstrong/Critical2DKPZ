/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationFinitePath
import Mathlib.Tactic

/-! # Linearity of the full-lattice hatted path -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

/-- A finite linear combination of terminal profiles can be moved outside an
unrestricted hatted operator word. The row support hypothesis makes every
exchange of a finite sum and a lattice `tsum` exact. -/
theorem collisionKernelWordAction_finsetSum {α ι : Type*}
    (Ks : List (α → α → ℝ)) (S : Finset ι) (c : ι → ℝ)
    (f : ι → α → ℝ)
    (hrow : ∀ K ∈ Ks, ∀ x, ∃ U : Finset α, ∀ y ∉ U, K x y = 0) :
    ∀ x, collisionKernelWordAction Ks (fun y => ∑ z ∈ S, c z * f z y) x =
      ∑ z ∈ S, c z * collisionKernelWordAction Ks (f z) x := by
  induction Ks with
  | nil =>
      intro x
      rfl
  | cons K Ks ih =>
      intro x
      have hKrow : ∃ U : Finset α, ∀ y ∉ U, K x y = 0 := hrow K (by simp) x
      obtain ⟨U, hU⟩ := hKrow
      have htail : ∀ K' ∈ Ks, ∀ x, ∃ U : Finset α, ∀ y ∉ U, K' x y = 0 := by
        intro K' hK' y
        exact hrow K' (by simp [hK']) y
      have htermSummable (z : ι) (hz : z ∈ S) :
          Summable (fun y : α => c z * (K x y * collisionKernelWordAction Ks (f z) y)) := by
        apply summable_of_ne_finset_zero (s := U)
        intro y hy
        rw [hU y hy]
        simp
      calc
        _ = ∑' y : α, ∑ z ∈ S,
              c z * (K x y * collisionKernelWordAction Ks (f z) y) := by
              rw [collisionKernelWordAction]
              apply tsum_congr
              intro y
              rw [ih htail y]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro z hz
              ring
        _ = ∑ z ∈ S, ∑' y : α,
              c z * (K x y * collisionKernelWordAction Ks (f z) y) :=
              Summable.tsum_finsetSum fun z hz => htermSummable z hz
        _ = ∑ z ∈ S, c z *
              collisionKernelWordAction (K :: Ks) (f z) x := by
              apply Finset.sum_congr rfl
              intro z hz
              rw [collisionKernelWordAction]
              rw [← tsum_mul_left]

end Critical2DKPZ.SHF.Moments

end
