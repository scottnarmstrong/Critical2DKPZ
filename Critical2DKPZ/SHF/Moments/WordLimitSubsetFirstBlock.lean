/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitSubsetTransitions

/-! # Spectators across a fixed entrance and collision run -/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- Before summing the entrance and run durations, all labels outside the
colliding subset already form a single free transition at time `s+r`. -/
theorem sum_free_run_subset_factor {h : ℕ} (S : Finset (Fin h))
    (β : ℝ) (α : CollisionPair h) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S)
    (s r : ℕ) (x v : LatticeConfiguration h) :
    (∑ u ∈ collisionWordConfigurationEndpointSet s x,
      (∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) =
    (∑ p ∈ collisionWordConfigurationEndpointSet s (fun j => x (S.orderEmbOfFin rfl j)),
      (∏ j, srwKernel s (p j - x (S.orderEmbOfFin rfl j))) *
        collisionWordUndampedPairRunFactor β (Tsai.collisionPairWithin S α h₁ h₂) r p
          (fun j => v (S.orderEmbOfFin rfl j))) *
      ∏ j : Fin Sᶜ.card, srwKernel (s + r)
        (v (Sᶜ.orderEmbOfFin rfl j) - x (Sᶜ.orderEmbOfFin rfl j)) := by
  simp_rw [pairRunFactor_subset_factor S β α h₁ h₂]
  exact sum_freeReplica_subset_factor S s r x
    (fun j => v (Sᶜ.orderEmbOfFin rfl j))
    (fun p => collisionWordUndampedPairRunFactor β (Tsai.collisionPairWithin S α h₁ h₂) r p
      (fun j => v (S.orderEmbOfFin rfl j)))

end Critical2DKPZ.SHF.Moments
