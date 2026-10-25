/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25HattedInteractionSupport
public import Critical2DKPZ.MomentBounds.CCR25RunBoxSupport
import Mathlib.Tactic

/-! # Finite spatial truncation of hatted operator paths -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.MomentBounds

attribute [local instance] Classical.propDecidable

/-- The unrestricted row convention for a word of hatted operators. -/
def collisionKernelWordAction {α : Type*} : List (α → α → ℝ) →
    (α → ℝ) → α → ℝ
  | [], f, x => f x
  | K :: Ks, f, x => ∑' y, K x y * collisionKernelWordAction Ks f y

/-- A word whose kernels expand a configuration box by at most `L` per
operator can be restricted to the final reachable box. The intermediate
box shrinks by one step at each induction, so the finite truncation is exact. -/
theorem collisionKernelWordAction_eq_finiteKernelWordApply
    {h L : ℕ} (A : Finset Critical2DKPZ.Site)
    (Ks : List (LatticeConfiguration h → LatticeConfiguration h → ℝ))
    (hstep : ∀ K ∈ Ks, ∀ r : ℕ, ∀ x,
      x ∈ configBox h A r → ∀ y, K x y ≠ 0 → y ∈ configBox h A (r + L))
    (f : LatticeConfiguration h → ℝ) :
    ∀ r x, x ∈ configBox h A r →
      collisionKernelWordAction Ks f x =
        finiteKernelWordApply (configBox h A (r + Ks.length * L)) Ks f x := by
  induction Ks with
  | nil =>
      intro r x hx
      rfl
  | cons K Ks ih =>
      intro r x hx
      have hKstep : ∀ y,
          K x y ≠ 0 → y ∈ configBox h A (r + L) := by
        intro y hy
        exact hstep K (by simp) r x hx y hy
      let Ssmall : Finset (LatticeConfiguration h) :=
        configBox h A (r + L)
      let Slarge : Finset (LatticeConfiguration h) :=
        configBox h A (r + (Ks.length + 1) * L)
      have hlargeEq : Slarge =
          configBox h A (r + (K :: Ks).length * L) := by
        apply congrArg (configBox h A)
        simp only [List.length_cons]
      have hsmallSub : Ssmall ⊆ Slarge := by
        apply ccr25ConfigBox_mono
        have hmul : (Ks.length + 1) * L = Ks.length * L + L := by
          simp [Nat.add_mul]
        omega
      have htailStep : ∀ K' ∈ Ks, ∀ r' : ℕ, ∀ z,
          z ∈ configBox h A r' → ∀ y, K' z y ≠ 0 →
            y ∈ configBox h A (r' + L) := by
        intro K' hK' r' z hz y hy
        exact hstep K' (by simp [hK']) r' z hz y hy
      have hfull :
          (∑' y, K x y * collisionKernelWordAction Ks f y) =
            ∑ y ∈ Ssmall, K x y * collisionKernelWordAction Ks f y := by
        apply tsum_eq_sum
        intro y hy
        have hzero : K x y = 0 := by
          by_contra hn
          exact hy (hKstep y hn)
        simp [hzero]
      have hfinite :
          (∑ y ∈ Slarge, K x y *
              finiteKernelWordApply Slarge Ks f y) =
            ∑ y ∈ Ssmall, K x y *
              finiteKernelWordApply Slarge Ks f y := by
        have hsum :
            (∑ y ∈ Ssmall, K x y *
              finiteKernelWordApply Slarge Ks f y) =
              ∑ y ∈ Slarge, K x y *
                finiteKernelWordApply Slarge Ks f y :=
          Finset.sum_subset hsmallSub (by
            intro y hyLarge hySmall
            have hzero : K x y = 0 := by
              by_contra hn
              exact hySmall (hKstep y hn)
            simp [hzero])
        exact hsum.symm
      calc
        collisionKernelWordAction (K :: Ks) f x =
            ∑ y ∈ Ssmall, K x y * collisionKernelWordAction Ks f y := by
              exact hfull
        _ = ∑ y ∈ Ssmall, K x y *
              finiteKernelWordApply Slarge Ks f y := by
              apply Finset.sum_congr rfl
              intro y hy
              have hyBox : y ∈ configBox h A (r + L) := by
                change y ∈ configBox h A (r + L) at hy
                exact hy
              have hIH := ih htailStep (r + L) y hyBox
              have hrad : (r + L) + Ks.length * L =
                  r + (Ks.length + 1) * L := by
                have hmul : (Ks.length + 1) * L = Ks.length * L + L := by
                  simp [Nat.add_mul]
                omega
              rw [hrad] at hIH
              exact congrArg (fun z : ℝ => K x y * z) hIH
        _ = ∑ y ∈ Slarge, K x y *
              finiteKernelWordApply Slarge Ks f y := hfinite.symm
        _ = finiteKernelWordApply
              (configBox h A (r + (K :: Ks).length * L)) (K :: Ks) f x := by
              rw [← hlargeEq]
              rw [finiteKernelWordApply]

end Critical2DKPZ.SHF.Moments

end
