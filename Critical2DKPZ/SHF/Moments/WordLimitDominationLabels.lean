/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.HeadCoordinateSplit
public import Critical2DKPZ.Definitions.Site
public import Critical2DKPZ.SHF.Tsai.FinsetCoordinateSplit
import Mathlib.Tactic

/-! # Label geometry for the shared potential-domination induction -/

@[expose] public noncomputable section

open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

/-- For at most four replicas, a pair distinct from the current collision has a label outside the colliding pair. -/
theorem collisionPair_free_endpoint_of_le_four {h : ℕ} (hh : h ≤ 4)
    (α β : CollisionPair h) (hαβ : α ≠ β) :
    ∃ i : Fin h, (i = β.1.1 ∨ i = β.1.2) ∧ i ≠ α.1.1 ∧ i ≠ α.1.2 := by
  interval_cases h
  · exact False.elim (collisionPair_impossible (by omega) α)
  · exact False.elim (collisionPair_impossible (by omega) α)
  · exact False.elim (hαβ (Subsingleton.elim α β))
  · have hthree : ∀ a b : CollisionPair 3, a ≠ b →
        ∃ i : Fin 3, (i = b.1.1 ∨ i = b.1.2) ∧ i ≠ a.1.1 ∧ i ≠ a.1.2 := by decide
    exact hthree α β hαβ
  · exact Tsai.exists_beta_endpoint_outside_alpha α β hαβ

/-- Reconstructing a split configuration recovers each selected coordinate. -/
theorem splitSubsetConfig_symm_selected {h : ℕ} (S : Finset (Fin h))
    (p : Fin S.card → Site) (q : Fin Sᶜ.card → Site) (j : Fin S.card) :
    (Tsai.splitFinsetCoordinates S Site).symm (p, q) (S.orderEmbOfFin rfl j) = p j := by
  exact congrArg (fun z => z.1 j) ((Tsai.splitFinsetCoordinates S Site).apply_symm_apply (p, q))

/-- Reconstructing a split configuration recovers each complementary coordinate. -/
theorem splitSubsetConfig_symm_complement {h : ℕ} (S : Finset (Fin h))
    (p : Fin S.card → Site) (q : Fin Sᶜ.card → Site) (j : Fin Sᶜ.card) :
    (Tsai.splitFinsetCoordinates S Site).symm (p, q) (Sᶜ.orderEmbOfFin rfl j) = q j := by
  exact congrArg (fun z => z.2 j) ((Tsai.splitFinsetCoordinates S Site).apply_symm_apply (p, q))

end Critical2DKPZ.SHF.Moments
