/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.PairStratumRenewalIdentity
import Mathlib.Tactic

/-! # CCR identification of one resummed pair run -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds Polymer

attribute [local instance] Classical.propDecidable

/-- A pair-word run, including its first selected disorder edge, is exactly
the pair-partition CCR interaction kernel multiplied by the first variance.
The equality is valid off the pair stratum as well, where both sides vanish. -/
theorem pairRunFactor_eq_sigmaSq_mul_interactingReplicaKernelAbs
    {h : ℕ} (β : ℝ) (α : CollisionPair h) (r : ℕ)
    (u v : LatticeConfiguration h) :
    (if u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
        sigmaSq β * Collision.spatialRenewal (sigmaSq β) r
          (v α.1.1 - u α.1.1) *
        (∏ i : Fin h, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
          Critical2DKPZ.srwKernel r (v i - u i)) =
      sigmaSq β * interactingReplicaKernelAbs β (pairPartition α) r u v := by
  by_cases hu : u α.1.1 = u α.1.2
  · by_cases hv : v α.1.1 = v α.1.2
    · rw [interactingReplicaKernelAbs_pairPartition_eq_on_strata β α r u v
        hu hv]
      rw [otherBlocksFreeKernel_pairPartition_eq]
      simp [hu, hv]
      ring
    · have hzero : interactingReplicaKernelAbs β (pairPartition α) r u v = 0 :=
        interactingReplicaKernelAbs_pairPartition_zero_of_endpoint_offStratum
          β α r u v (Or.inr hv)
      rw [hzero]
      simp [hu, hv]
  · have hzero : interactingReplicaKernelAbs β (pairPartition α) r u v = 0 :=
      interactingReplicaKernelAbs_pairPartition_zero_of_endpoint_offStratum
        β α r u v (Or.inl hu)
    rw [hzero]
    simp [hu]

private theorem sum_range_succ_eq_zero_add_shift (L : ℕ) (f : ℕ → ℝ) :
    (∑ r ∈ Finset.range (L + 1), f r) =
      f 0 + ∑ r ∈ Finset.range L, f (r + 1) := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring

/-- Laplace summing the resummed run, including its distinguished first
collision, is the pair-partition hatted CCR interaction multiplied by its
first disorder variance. -/
theorem pairRunFactor_laplace_sum_eq_hattedInteracting
    {h : ℕ} (β lam : ℝ) (L : ℕ)
    (α : CollisionPair h) (z x : LatticeConfiguration h) :
    (∑ r ∈ Finset.range (L + 1),
      Real.exp (-((lam / (L : ℝ)) * (r : ℝ))) *
        ((if z α.1.1 = z α.1.2 ∧ x α.1.1 = x α.1.2 then (1 : ℝ) else 0) *
          sigmaSq β * Collision.spatialRenewal (sigmaSq β) r
            (x α.1.1 - z α.1.1) *
          (∏ i : Fin h, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
            Critical2DKPZ.srwKernel r (x i - z i)))) =
      sigmaSq β * hattedInteractingReplicaKernelAbs L (lam / (L : ℝ)) β
        (pairPartition α) z x := by
  let κ : ℝ := lam / (L : ℝ)
  have hterm (r : ℕ) :
      (if z α.1.1 = z α.1.2 ∧ x α.1.1 = x α.1.2 then (1 : ℝ) else 0) *
          sigmaSq β * Collision.spatialRenewal (sigmaSq β) r
            (x α.1.1 - z α.1.1) *
          (∏ i : Fin h, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
            Critical2DKPZ.srwKernel r (x i - z i)) =
        sigmaSq β * interactingReplicaKernelAbs β (pairPartition α) r z x :=
    pairRunFactor_eq_sigmaSq_mul_interactingReplicaKernelAbs β α r z x
  have hzero :
      interactingReplicaKernelAbs β (pairPartition α) 0 z x =
        (if z = x ∧ IsCollisionConfiguration (pairPartition α) x then
          (1 : ℝ) else 0) := by
    simp [interactingReplicaKernelAbs]
  calc
    _ = sigmaSq β *
        (interactingReplicaKernelAbs β (pairPartition α) 0 z x +
          ∑ r ∈ Finset.range L,
            Real.exp (-(κ * ((r + 1 : ℕ) : ℝ))) *
              interactingReplicaKernelAbs β (pairPartition α) (r + 1) z x) := by
      rw [sum_range_succ_eq_zero_add_shift]
      calc
        _ = sigmaSq β * interactingReplicaKernelAbs β (pairPartition α) 0 z x +
            ∑ r ∈ Finset.range L,
              Real.exp (-(κ * ((r + 1 : ℕ) : ℝ))) *
                (sigmaSq β * interactingReplicaKernelAbs β
                  (pairPartition α) (r + 1) z x) := by
          simp_rw [hterm]
          simp [κ]
        _ = _ := by
          rw [mul_add, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro r hr
          ring
    _ = sigmaSq β *
        hattedInteractingReplicaKernelAbs L κ β (pairPartition α) z x := by
      simp only [hattedInteractingReplicaKernelAbs]
      rw [hzero]
      apply congrArg (fun q : ℝ => sigmaSq β *
        ((if z = x ∧ IsCollisionConfiguration (pairPartition α) x then
          (1 : ℝ) else 0) + q))
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      apply congrArg Real.exp
      simp only [κ]
      ring

end Critical2DKPZ.SHF.Moments

end
