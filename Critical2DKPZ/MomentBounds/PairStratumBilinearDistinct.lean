/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.PairCrossLabels
public import Critical2DKPZ.MomentBounds.PairStratumBilinear
import Mathlib.Tactic

/-! # Bilinear bound on any two distinct pair strata -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

/-- The finite LZ21 bilinear estimate on any two different pair strata. The
endpoint choice is allowed to depend on the two pairs, so overlapping pairs
are included. -/
theorem finite_distinct_pair_stratum_bilinear_le {h : ℕ}
    (α β : DeltaBose.CollisionPair h) (hne : α ≠ β)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (s t : Finset (LatticeConfiguration h))
    (hs : ∀ x ∈ s, x α.val.1 = x α.val.2)
    (ht : ∀ y ∈ t, y β.val.1 = y β.val.2)
    (f g : LatticeConfiguration h → ℝ) :
    (∑ x ∈ s, ∑ y ∈ t, |f x| * replicaGreenKernel x y * |g y|) ≤
      4 ^ ((h : ℝ) - 1) * 4 * (9 : ℝ) ^ (h - 3) * 1188 * (p * q) *
        (∑ x ∈ s, |f x| ^ p) ^ (1 / p) *
        (∑ y ∈ t, |g y| ^ q) ^ (1 / q) := by
  classical
  obtain ⟨m, n, k, l, hmn, hmk, hml, hkl, hkm, hkn, hklPair, hmnPair,
      he₁, he₂⟩ := exists_pairCrossSpectators α β hne
  let e₁ : PairSpectatorLabels h m k l ≃ Fin (h - 3) := Classical.choice he₁
  let e₂ : PairSpectatorLabels h k m n ≃ Fin (h - 3) := Classical.choice he₂
  have hs' : ∀ x ∈ s, x k = x l := by
    intro x hx
    rcases hklPair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hs x hx
    · exact (hs x hx).symm
  have ht' : ∀ y ∈ t, y m = y n := by
    intro y hy
    rcases hmnPair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ht y hy
    · exact (ht y hy).symm
  exact finite_pair_stratum_bilinear_le m n k l hmn hmk hml hkl hkm hkn
    e₁ e₂ hpq s t hs' ht' f g

end Critical2DKPZ.MomentBounds
