/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitFirstBlock

/-! # Conditioning a first block on its active labels -/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- A uniform bound on the free-spectator average of an endpoint profile
bounds its first-block test by that constant times the scalar block mass. -/
theorem wordFirstBlockKernel_test_le_of_free_average {h : ℕ}
    (S : Finset (Fin h)) (β : ℝ) (α : CollisionPair h)
    (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S)
    (s r : ℕ) (x : LatticeConfiguration h) (H : LatticeConfiguration h → ℝ) (B : ℝ)
    (hH : ∀ p ∈ collisionWordConfigurationEndpointSet (s + r)
        (fun j => x (S.orderEmbOfFin rfl j)),
      (∑ q ∈ collisionWordConfigurationEndpointSet (s + r)
          (fun j => x (Sᶜ.orderEmbOfFin rfl j)),
        (∏ j, srwKernel (s + r) (q j - x (Sᶜ.orderEmbOfFin rfl j))) *
          H ((Tsai.splitFinsetCoordinates S Site).symm (p, q))) ≤ B) :
    (∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
      wordFirstBlockKernel β α s r x v * H v) ≤
      B * (srwKernel (2 * s) (x α.1.2 - x α.1.1) *
        (sigmaSq β * Renewal.renewalMass
          (fun k => sigmaSq β * Renewal.returnWeight k) r)) := by
  classical
  let a := S.orderEmbOfFin rfl
  let c := Sᶜ.orderEmbOfFin rfl
  let e := Tsai.splitFinsetCoordinates S Site
  let γ := Tsai.collisionPairWithin S α h₁ h₂
  let xS : LatticeConfiguration S.card := fun j => x (a j)
  let A : LatticeConfiguration S.card → ℝ := wordFirstBlockKernel β γ s r xS
  let G : LatticeConfiguration Sᶜ.card → ℝ := fun q =>
    ∏ j, srwKernel (s + r) (q j - x (c j))
  let P := collisionWordConfigurationEndpointSet (s + r) xS
  let Q := collisionWordConfigurationEndpointSet (s + r) (fun j => x (c j))
  have hrepr (v : LatticeConfiguration h) :
      e.symm ((fun j => v (a j)), (fun j => v (c j))) = v := by
    have he : e v = ((fun j => v (a j)), (fun j => v (c j))) := by
      apply Prod.ext <;> rfl
    rw [← he]
    exact e.symm_apply_apply v
  have hpoint (v : LatticeConfiguration h) :
      wordFirstBlockKernel β α s r x v * H v =
        A (fun j => v (a j)) *
          (G (fun j => v (c j)) * H (e.symm ((fun j => v (a j)), (fun j => v (c j))))) := by
    rw [wordFirstBlockKernel_subset_factor S β α h₁ h₂]
    change (A (fun j => v (a j)) * G (fun j => v (c j))) * H v = _
    rw [hrepr]
    exact mul_assoc _ _ _
  calc
    _ = ∑ v ∈ Fintype.piFinset (fun i => endpoints (x i) (s + r)),
        A (fun j => v (a j)) *
          (G (fun j => v (c j)) * H (e.symm ((fun j => v (a j)), (fun j => v (c j))))) :=
      Finset.sum_congr rfl (fun v _ => hpoint v)
    _ = ∑ p ∈ P, ∑ q ∈ Q, A p * (G q * H (e.symm (p, q))) :=
      sum_piFinset_split_subset S (fun i => endpoints (x i) (s + r))
        (fun p q => A p * (G q * H (e.symm (p, q))))
    _ ≤ ∑ p ∈ P, A p * B := by
      apply Finset.sum_le_sum
      intro p hp
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hH p hp) (wordFirstBlockKernel_nonneg β γ s r xS p)
    _ = B * ∑ p ∈ P, A p := by
      rw [← Finset.sum_mul]
      exact mul_comm _ _
    _ = _ := by
      change B * (∑ p ∈ collisionWordConfigurationEndpointSet (s + r) xS,
        wordFirstBlockKernel β γ s r xS p) = _
      rw [sum_wordFirstBlockKernel]
      dsimp only [xS, γ, a]
      rw [Tsai.orderEmb_collisionPairWithin_snd, Tsai.orderEmb_collisionPairWithin_fst]

end Critical2DKPZ.SHF.Moments
