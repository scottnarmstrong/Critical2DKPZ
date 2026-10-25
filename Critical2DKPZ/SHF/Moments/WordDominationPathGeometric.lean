/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationPathOperatorBound
import Mathlib.Tactic

/-! # Geometric summation of compact hatted pair paths -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds Polymer

/-- A quarter-contraction controls all variance-weighted hatted paths of a
given nonzero length at rate `1/2`, uniformly in their finite support set. -/
theorem sum_varianceWeightedHattedPairWordPath_le_half_pow
    {h n : ℕ} (L : ℕ) (lam β : ℝ) (A : Finset Site)
    (cU cQ d : ℝ) (hcU : 0 ≤ cU) (hcQ : 1 ≤ cQ) (hd : 0 ≤ d)
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
          (hattedFreeReplicaKernel L I J)) f) ≤ cQ * finiteLpNorm s 2 f)
    (hsmall : cU * sigmaSq β * (Fintype.card (CollisionPair h) : ℝ) * cQ < 1 / 4) :
    (∑ w : CollisionWord h (n + 1),
      ∑ x ∈ Fintype.piFinset (fun _ : Fin h => A),
        ∑ z ∈ Fintype.piFinset (fun _ : Fin h => A),
          varianceWeightedHattedPairWordPath L lam β ⊥ (List.ofFn w.1) x z) ≤
      d ^ 2 * (1 / 2 : ℝ) ^ n := by
  classical
  let P : ℝ := Fintype.card (CollisionPair h)
  let a : ℝ := cU * sigmaSq β * P
  let b : ℝ := d ^ 2 * (cU * sigmaSq β) ^ (n + 1) * cQ ^ n
  have hσ : 0 ≤ sigmaSq β := sigmaSq_nonneg β
  have hQ0 : 0 ≤ cQ := le_trans (by norm_num) hcQ
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hcard : (Fintype.card (CollisionWord h (n + 1)) : ℝ) ≤ P ^ (n + 1) := by
    dsimp [P]
    exact_mod_cast collisionWord_card_le_pow h (n + 1)
  have hsum :
      (∑ w : CollisionWord h (n + 1),
        ∑ x ∈ Fintype.piFinset (fun _ : Fin h => A),
          ∑ z ∈ Fintype.piFinset (fun _ : Fin h => A),
            varianceWeightedHattedPairWordPath L lam β ⊥ (List.ofFn w.1) x z) ≤
        d ^ 2 * a ^ (n + 1) * cQ ^ n := by
    calc
      _ ≤ ∑ _w : CollisionWord h (n + 1), b := by
          apply Finset.sum_le_sum
          intro w hw
          exact finite_sum_varianceWeightedHattedPairWordPath_le_operatorCosts
            L lam β A w cU cQ d hcU hQ0 hd hboundary hU hQ
      _ = (Fintype.card (CollisionWord h (n + 1)) : ℝ) * b := by simp
      _ ≤ P ^ (n + 1) * b := mul_le_mul_of_nonneg_right hcard hb
      _ = _ := by dsimp [a, b]; rw [mul_pow, mul_pow]; ring
  have harate : a * cQ < 1 / 4 := by simpa [a, P] using hsmall
  have haone : a ≤ 1 := by
    have hle : a ≤ a * cQ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hcQ ha
    linarith
  have hrate0 : 0 ≤ a * cQ := mul_nonneg ha hQ0
  have hrate : a * cQ ≤ (1 / 2 : ℝ) := by linarith
  have hpow : (a * cQ) ^ n ≤ (1 / 2 : ℝ) ^ n :=
    pow_le_pow_left₀ hrate0 hrate n
  have hprod : a * (a * cQ) ^ n ≤ (1 / 2 : ℝ) ^ n := by
    calc
      _ ≤ 1 * (a * cQ) ^ n :=
        mul_le_mul_of_nonneg_right haone (pow_nonneg hrate0 n)
      _ ≤ _ := by simpa only [one_mul] using hpow
  calc
    _ ≤ d ^ 2 * a ^ (n + 1) * cQ ^ n := hsum
    _ = d ^ 2 * (a * (a * cQ) ^ n) := by rw [pow_succ, mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (sq_nonneg d)

end Critical2DKPZ.SHF.Moments

end
