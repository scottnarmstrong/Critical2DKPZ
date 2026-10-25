/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationPairWordCCR
public import Critical2DKPZ.SHF.Moments.WordDominationVariancePathFactor
import Mathlib.Tactic

/-! # Operator costs for compact hatted pair paths -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds Polymer

private theorem collisionWord_lastPartition_ne_bot {h : ℕ}
    (α : CollisionPair h) (rest : List (CollisionPair h)) :
    pairWordLastPartition (α :: rest) ≠ (⊥ : ReplicaPartition h) := by
  induction rest generalizing α with
  | nil => simpa [pairWordLastPartition] using pairPartition_ne_bot α
  | cons γ tail ih =>
      simpa [pairWordLastPartition] using ih γ

/-- Uniform boundary and operator estimates bound a variance-weighted pair
path. The finite configuration box may depend on the word; all costs are
uniform in that box. -/
theorem finite_sum_varianceWeightedHattedPairWordPath_le_operatorCosts
    {h n : ℕ} (L : ℕ) (lam β : ℝ) (A : Finset Site)
    (w : CollisionWord h (n + 1)) (cU cQ d : ℝ)
    (hcU : 0 ≤ cU) (hcQ : 0 ≤ cQ) (hd : 0 ≤ d)
    (hboundary : ∀ (s : Finset (LatticeConfiguration h))
      (I : ReplicaPartition h), I ≠ ⊥ →
      finiteLpNorm s 2 (hattedReplicaBoundaryVector L I A
        (collisionWordSiteIndicator A)) ≤ d)
    (hU : ∀ (s : Finset (LatticeConfiguration h))
      (I : ReplicaPartition h), I ≠ ⊥ → ∀ f,
      finiteLpNorm s 2 (finiteKernelApply s
        (weightedKernel (replicaExponentialWeight 0)
          (hattedInteractingReplicaKernelAbs L lam β I)) f) ≤
        cU * finiteLpNorm s 2 f)
    (hQ : ∀ (s : Finset (LatticeConfiguration h))
      (I J : ReplicaPartition h), I ≠ ⊥ → J ≠ ⊥ → I ≠ J → ∀ f,
      finiteLpNorm s 2 (finiteKernelApply s
        (weightedKernel (replicaExponentialWeight 0)
          (hattedFreeReplicaKernel L I J)) f) ≤ cQ * finiteLpNorm s 2 f) :
    (∑ x ∈ Fintype.piFinset (fun _ : Fin h => A),
      ∑ z ∈ Fintype.piFinset (fun _ : Fin h => A),
        varianceWeightedHattedPairWordPath L lam β ⊥ (List.ofFn w.1) x z) ≤
      d ^ 2 * (cU * sigmaSq β) ^ (n + 1) * cQ ^ n := by
  classical
  let s : Finset (LatticeConfiguration h) := configBox h A
    (L + (pairWordInteriorKernels L lam β (List.ofFn w.1)).length * L)
  let u : ReplicaPartition h → LatticeConfiguration h → ℝ :=
    fun _ => hattedReplicaBoundaryVector L (pairPartition (w.1 0)) A
      (collisionWordSiteIndicator A)
  let v : ReplicaPartition h → LatticeConfiguration h → ℝ :=
    fun _ => hattedReplicaBoundaryVector L
      (pairWordLastPartition (List.ofFn w.1)) A (collisionWordSiteIndicator A)
  have hlast : pairWordLastPartition (List.ofFn w.1) ≠
      (⊥ : ReplicaPartition h) := by
    rw [List.ofFn_succ]
    exact collisionWord_lastPartition_ne_bot _ _
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    ⟨by norm_num, by norm_num, by norm_num⟩
  have hpairBound := ccr25FinitePairCollisionWordPairing_le w s L lam β
    (replicaExponentialWeight 0)
    (by intro x hx; simp [replicaExponentialWeight]) hpq u v cU cQ d d
    hcU hcQ hd
    (by
      intro I hI
      simpa [u, replicaExponentialWeight] using
        hboundary s (pairPartition (w.1 0)) (pairPartition_ne_bot _))
    (by
      intro I hI
      simpa [v, replicaExponentialWeight] using
        hboundary s (pairWordLastPartition (List.ofFn w.1)) hlast)
    (by intro I hI f; simpa [ccr25LabelKernel] using hU s I hI f)
    (by intro I J hI hJ hIJ f; simpa [ccr25LabelKernel] using hQ s I J hI hJ hIJ f)
  have hpairEq := finite_sum_hattedPairWordPath_eq_ccr25FiniteWordPairing
    L lam β A w
  have hfactor :
      (∑ x ∈ Fintype.piFinset (fun _ : Fin h => A),
        ∑ z ∈ Fintype.piFinset (fun _ : Fin h => A),
          varianceWeightedHattedPairWordPath L lam β ⊥ (List.ofFn w.1) x z) =
      sigmaSq β ^ (n + 1) *
        (∑ x ∈ Fintype.piFinset (fun _ : Fin h => A),
          ∑ z ∈ Fintype.piFinset (fun _ : Fin h => A),
            hattedPairWordPath L lam β ⊥ (List.ofFn w.1) x z) := by
    simp only [varianceWeightedHattedPairWordPath_eq_sigmaSq_pow_mul,
      List.length_ofFn, Finset.mul_sum]
  rw [hfactor, hpairEq]
  calc
    _ ≤ sigmaSq β ^ (n + 1) * (d * d * cU ^ (n + 1) * cQ ^ n) :=
      mul_le_mul_of_nonneg_left hpairBound (pow_nonneg (sigmaSq_nonneg β) _)
    _ = _ := by rw [mul_pow]; ring

end Critical2DKPZ.SHF.Moments

end
