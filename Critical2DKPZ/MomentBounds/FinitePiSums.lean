/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.LatticeShells
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Tactic

/-! # Finite coordinate boxes and their head-tail decomposition -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

/-- Product of `m` planar lattice boxes, indexed by a finite replica coordinate. -/
def finPiBox (m k : ℕ) : Finset (Fin m → Site) :=
  Fintype.piFinset (fun _ : Fin m => latticeBox k)

/-- Splitting the first coordinate identifies a finite product box with a product. -/
def finPiConsEquiv (m : ℕ) : (Fin (m + 1) → Site) ≃ Site × (Fin m → Site) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j
      simp
  right_inv p := by
    rcases p with ⟨a, f⟩
    apply Prod.ext
    · simp
    · funext i
      simp

/-- Finite summation over a product box splits into its first coordinate and its tail. -/
theorem sum_finPiBox_succ {m k : ℕ} (F : (Fin (m + 1) → Site) → ℝ) :
    (∑ z ∈ finPiBox (m + 1) k, F z) =
      ∑ a ∈ latticeBox k, ∑ z ∈ finPiBox m k, F (Fin.cons a z) := by
  have hmem (z : Fin (m + 1) → Site) :
      z ∈ finPiBox (m + 1) k ↔ finPiConsEquiv m z ∈ latticeBox k ×ˢ finPiBox m k := by
    simp [finPiBox, finPiConsEquiv, Finset.mem_product, Fin.forall_fin_succ]
  have hsum : (∑ z ∈ finPiBox (m + 1) k, F z) =
      ∑ p ∈ latticeBox k ×ˢ finPiBox m k, F (Fin.cons p.1 p.2) :=
    Finset.sum_equiv (finPiConsEquiv m) hmem (fun z hz => by
      have hz' : z = Fin.cons (z 0) (fun i => z i.succ) := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp
        · intro j
          simp
      exact congrArg F hz')
  exact hsum.trans
    (Finset.sum_product' (latticeBox k) (finPiBox m k) fun a z => F (Fin.cons a z))

end Critical2DKPZ.MomentBounds
