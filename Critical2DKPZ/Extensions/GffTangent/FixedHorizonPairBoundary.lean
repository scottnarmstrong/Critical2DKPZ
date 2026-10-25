/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonProfileEnergy
import Critical2DKPZ.MomentBounds.CCR25AbsolutePositivity
import Mathlib.Tactic

/-! # The disjoint-pair boundary bound in the sharp fourth moment -/

@[expose] public noncomputable section

open Critical2DKPZ.MomentBounds Critical2DKPZ.DeltaBose
open scoped BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- The disjoint-pair spatial form is a product of two bounded quadratic
energies. The estimate is uniform in the collision time. -/
theorem summable_tsum_disjoint_pair_boundary_energy_le
    (α δ : CollisionPair 4) (hd : Disjoint (collisionPairLabels α) (collisionPairLabels δ))
    (k : ℕ) (F : Site → ℝ) (hF : ∀ x, 0 ≤ F x) (hs : Summable F)
    {B : ℝ} (hB : 0 ≤ B) (hFB : ∀ x, F x ≤ B) :
    let G : LatticeConfiguration 4 → ℝ := fun x =>
      (if x α.1.1 = x α.1.2 then
        F (x α.1.1) ^ 2 * (F (x δ.1.1) * F (x δ.1.2)) else 0) *
        srwKernel (2 * k) (x δ.1.2 - x δ.1.1)
    Summable G ∧ (∑' x, G x) ≤ (B * ∑' y : Site, F y) ^ 2 := by
  let A : Site × Site → ℝ := fun p => F p.1 * F p.2 * srwKernel 0 (p.2 - p.1)
  let D : Site × Site → ℝ := fun p => F p.1 * F p.2 * srwKernel (2 * k) (p.2 - p.1)
  have hA := tsum_profile_even_energy_le 0 F hF hs hFB
  have hD := tsum_profile_even_energy_le k F hF hs hFB
  have hA0 (p : Site × Site) : 0 ≤ A p :=
    mul_nonneg (mul_nonneg (hF _) (hF _)) (Polymer.kernel_nonneg _ _)
  have hD0 (p : Site × Site) : 0 ≤ D p :=
    mul_nonneg (mul_nonneg (hF _) (hF _)) (Polymer.kernel_nonneg _ _)
  have hprod : Summable (fun p : (Site × Site) × (Site × Site) => A p.1 * D p.2) :=
    hA.1.mul_of_nonneg hD.1 hA0 hD0
  let e := disjointPairConfigurationEquiv α δ hd
  have hcfg : Summable ((fun p : (Site × Site) × (Site × Site) => A p.1 * D p.2) ∘ e) :=
    hprod.comp_injective (i := (e : LatticeConfiguration 4 → (Site × Site) × (Site × Site))) e.injective
  change Summable (fun x : LatticeConfiguration 4 =>
    A (x α.1.1, x α.1.2) * D (x δ.1.1, x δ.1.2)) at hcfg
  have he (x : LatticeConfiguration 4) :
      (if x α.1.1 = x α.1.2 then
        F (x α.1.1) ^ 2 * (F (x δ.1.1) * F (x δ.1.2)) else 0) *
        srwKernel (2 * k) (x δ.1.2 - x δ.1.1) =
      A (x α.1.1, x α.1.2) * D (x δ.1.1, x δ.1.2) := by
    dsimp only [A, D]
    rw [Polymer.srwKernel_zero]
    by_cases hx : x α.1.1 = x α.1.2
    · simp only [hx, sub_self, ite_true, mul_one]
      ring
    · have hsub : x α.1.2 - x α.1.1 ≠ 0 := fun h => hx (sub_eq_zero.mp h).symm
      simp only [hx, hsub, ite_false, mul_zero, zero_mul]
  refine ⟨hcfg.congr (fun x => (he x).symm), ?_⟩
  calc
    _ = (∑' p : Site × Site, A p) * (∑' q : Site × Site, D q) :=
      (tsum_congr he).trans (tsum_disjointPair_product α δ hd A D hcfg)
    _ ≤ (B * ∑' y : Site, F y) * (B * ∑' y : Site, F y) :=
      mul_le_mul hA.2 hD.2 (tsum_nonneg hD0) (mul_nonneg hB (tsum_nonneg hF))
    _ = _ := by ring

/-- The finite first-collision boundary paired with any even spectator kernel
is bounded by the square of the initial supremum times initial mass. This
bound is uniform in both walk times and in the configuration cutoff. -/
theorem sum_replicaBoundaryVector_mul_pair_kernel_le
    (α δ : CollisionPair 4) (hd : Disjoint (collisionPairLabels α) (collisionPairLabels δ))
    (n k : ℕ) (S : Finset Site) (φ : Site → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hφ : ∀ y ∈ S, 0 ≤ φ y) (hφB : ∀ y ∈ S, φ y ≤ B)
    (s : Finset (LatticeConfiguration 4)) :
    (∑ x ∈ s, replicaBoundaryVector n (pairPartition α) S φ x *
      srwKernel (2 * k) (x δ.1.2 - x δ.1.1)) ≤ (B * ∑ y ∈ S, φ y) ^ 2 := by
  let F := finiteBoundaryConvolution n S φ
  have hF (x : Site) : 0 ≤ F x := (finiteBoundaryConvolution_nonneg_le n S φ hB hφ hφB x).1
  have hFB (x : Site) : F x ≤ B := (finiteBoundaryConvolution_nonneg_le n S φ hB hφ hφB x).2
  have hmass := summable_tsum_finiteBoundaryConvolution n S φ
  have hbound := summable_tsum_disjoint_pair_boundary_energy_le α δ hd k F hF hmass.1 hB hFB
  have he (x : LatticeConfiguration 4) :
      (if x α.1.1 = x α.1.2 then F (x α.1.1) ^ 2 * (F (x δ.1.1) * F (x δ.1.2)) else 0) *
        srwKernel (2 * k) (x δ.1.2 - x δ.1.1) =
      replicaBoundaryVector n (pairPartition α) S φ x * srwKernel (2 * k) (x δ.1.2 - x δ.1.1) := by
    rw [replicaBoundaryVector_disjoint_pairs_eq α δ hd]
  have hs := hbound.1.congr he
  have hle := hs.sum_le_tsum s (fun x _ => mul_nonneg
    (replicaBoundaryVector_nonneg n (pairPartition α) S φ hφ x) (Polymer.kernel_nonneg _ _))
  have htotal := (tsum_congr he).symm.trans_le hbound.2
  exact hle.trans (by simpa only [F, hmass.2] using htotal)

end Critical2DKPZ.Extensions.GffTangent
