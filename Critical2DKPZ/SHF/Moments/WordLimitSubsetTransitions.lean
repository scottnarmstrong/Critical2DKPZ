/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitSubsetSums
public import Critical2DKPZ.SHF.Moments.WordLimitSubsetRun
public import Critical2DKPZ.SHF.Moments.WordDominationFreeTail
import Mathlib.Tactic

/-! # Contracting free complementary strands in finite lattice sums -/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- The finite endpoint version of the free configuration semigroup identity. -/
theorem sum_freeReplicaConfigurationKernel_convolution {h s k : ℕ}
    (x y : LatticeConfiguration h) :
    (∑ u ∈ collisionWordConfigurationEndpointSet s x,
      (∏ i, srwKernel s (u i - x i)) * ∏ i, srwKernel k (y i - u i)) =
      ∏ i, srwKernel (s + k) (y i - x i) := by
  classical
  calc
    _ = ∑' u : LatticeConfiguration h,
        (∏ i, srwKernel s (u i - x i)) * ∏ i, srwKernel k (y i - u i) := by
      symm
      apply tsum_eq_sum
      intro u hu
      rw [collisionWord_freeProduct_zero_of_not_endpoints s x u hu, zero_mul]
    _ = _ := freeReplicaConfigurationKernel_convolution x y

/-- A free entrance contracts the complementary free strands while leaving
an arbitrary function of the selected coordinates. -/
theorem sum_freeReplica_subset_factor {n : ℕ} (S : Finset (Fin n)) (s k : ℕ)
    (x : LatticeConfiguration n) (y : LatticeConfiguration Sᶜ.card)
    (H : LatticeConfiguration S.card → ℝ) :
    (∑ u ∈ collisionWordConfigurationEndpointSet s x,
      (∏ i, srwKernel s (u i - x i)) *
        (H (fun j => u (S.orderEmbOfFin rfl j)) *
          ∏ j : Fin Sᶜ.card, srwKernel k (y j - u (Sᶜ.orderEmbOfFin rfl j)))) =
      (∑ p ∈ collisionWordConfigurationEndpointSet s (fun j => x (S.orderEmbOfFin rfl j)),
        (∏ j, srwKernel s (p j - x (S.orderEmbOfFin rfl j))) * H p) *
        ∏ j : Fin Sᶜ.card, srwKernel (s + k) (y j - x (Sᶜ.orderEmbOfFin rfl j)) := by
  classical
  let a := S.orderEmbOfFin rfl
  let c := Sᶜ.orderEmbOfFin rfl
  let F : LatticeConfiguration S.card → ℝ := fun p =>
    (∏ j, srwKernel s (p j - x (a j))) * H p
  let G : LatticeConfiguration Sᶜ.card → ℝ := fun q =>
    (∏ j, srwKernel s (q j - x (c j))) * ∏ j, srwKernel k (y j - q j)
  have hpoint (u : LatticeConfiguration n) :
      (∏ i, srwKernel s (u i - x i)) *
          (H (fun j => u (a j)) * ∏ j, srwKernel k (y j - u (c j))) =
        F (fun j => u (a j)) * G (fun j => u (c j)) := by
    rw [Tsai.prod_subset_mul_compl S (fun i => srwKernel s (u i - x i))]
    dsimp only [F, G]
    ring
  have hG :
      (∑ q ∈ collisionWordConfigurationEndpointSet s (fun j => x (c j)), G q) =
        ∏ j, srwKernel (s + k) (y j - x (c j)) :=
    sum_freeReplicaConfigurationKernel_convolution (fun j => x (c j)) y
  calc
    _ = ∑ u ∈ Fintype.piFinset (fun i => endpoints (x i) s),
        F (fun j => u (a j)) * G (fun j => u (c j)) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact hpoint u
    _ = (∑ p ∈ collisionWordConfigurationEndpointSet s (fun j => x (a j)), F p) *
        ∑ q ∈ collisionWordConfigurationEndpointSet s (fun j => x (c j)), G q :=
      sum_piFinset_subset_mul_compl S (fun i => endpoints (x i) s) F G
    _ = _ := by rw [hG]


end Critical2DKPZ.SHF.Moments
