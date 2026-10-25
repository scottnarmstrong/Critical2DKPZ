/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25ChaosExpansion
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! # Centered point-to-plane chaos expansion for CCR25 -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- Nonempty subsets of the positive time coordinates in an `n`-step walk. -/
def ccr25NonemptyChaosSubsets (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.powerset (Finset.Icc 1 n)).erase ∅

/-- Finite choices of a walk and a nonempty chaos subset for one replica. -/
def ccr25CenteredChaosIndices (n : ℕ) :
    Finset (Finset ℕ × (Fin n → Fin 4)) :=
  ccr25NonemptyChaosSubsets n ×ˢ Finset.univ

/-- One centered chaos summand of the `n`-step point-to-plane partition
function. -/
def ccr25CenteredChaosTerm (β : ℝ) (a n : ℕ) (w : Site)
    (i : Finset ℕ × (Fin n → Fin 4)) (ω : Disorder) : ℝ :=
  (4 : ℝ)⁻¹ ^ n *
    ∏ j ∈ i.1, Critical2DKPZ.Polymer.xi β
      (a + j, Critical2DKPZ.walkPosition w i.2 j) ω

/-- The finite sum of centered chaos summands. -/
def ccr25CenteredChaosExpansion (β : ℝ) (a n : ℕ) (w : Site)
    (ω : Disorder) : ℝ :=
  ∑ i ∈ ccr25CenteredChaosIndices n, ccr25CenteredChaosTerm β a n w i ω

/-- The empty chaos term is equal to one. -/
theorem ccr25_emptyChaosTerm_eq_one (n : ℕ) :
    ∑ _s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n = 1 := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← mul_pow, mul_inv_cancel₀ (by norm_num : (4 : ℝ) ≠ 0), one_pow]

/-- The centered point-to-plane polymer is exactly the sum over nonempty
square-free chaos subsets. -/
theorem pointToPlane_sub_one_eq_ccr25CenteredChaosExpansion
    (β : ℝ) (a n : ℕ) (w : Site) (ω : Disorder) :
    Critical2DKPZ.pointToPlane β a n w ω - 1 =
      ccr25CenteredChaosExpansion β a n w ω := by
  classical
  let S := Finset.powerset (Finset.Icc 1 n)
  let F : Finset ℕ → ℝ := fun A =>
    ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n *
      ∏ j ∈ A, Critical2DKPZ.Polymer.xi β
        (a + j, Critical2DKPZ.walkPosition w s j) ω
  have hempty : ∅ ∈ S := by simp [S]
  have hsplit :
      (∑ A ∈ S, F A) = F ∅ + ∑ A ∈ S.erase ∅, F A :=
    (Finset.add_sum_erase S F hempty).symm
  have hterm : F ∅ = 1 := by
    dsimp [F]
    simp only [mul_one]
    exact ccr25_emptyChaosTerm_eq_one n
  rw [Critical2DKPZ.Polymer.pointToPlane_chaos]
  change (∑ A ∈ S, F A) - 1 = _
  rw [hsplit, hterm, add_sub_cancel_left]
  change (∑ A ∈ ccr25NonemptyChaosSubsets n,
      ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n *
        ∏ j ∈ A, Critical2DKPZ.Polymer.xi β
          (a + j, Critical2DKPZ.walkPosition w s j) ω) = _
  rw [ccr25CenteredChaosExpansion, ccr25CenteredChaosIndices, Finset.sum_product]
  rfl


end

end Critical2DKPZ.MomentBounds
