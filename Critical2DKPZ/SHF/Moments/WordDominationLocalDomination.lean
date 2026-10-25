/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationPathDefect
public import Critical2DKPZ.SHF.Moments.WordDominationLocalNonpair
import Mathlib.Tactic

/-! # Positive local domination for the marked non-pair expansion -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Polymer DeltaBose Critical2DKPZ.MomentBounds

attribute [local instance] Classical.propDecidable

private theorem collisionWord_one_add_sum_le_prod {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) :
    1 + ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 + f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      have hsum : 0 ≤ ∑ j ∈ s, f j := Finset.sum_nonneg fun j hj => hf j
      have hfi := hf i
      calc
        _ ≤ (1 + f i) * (1 + ∑ j ∈ s, f j) := by
          nlinarith only [mul_nonneg hfi hsum]
        _ ≤ _ := mul_le_mul_of_nonneg_left ih (by linarith only [hfi])


/-- Omitting simultaneous selected pairs decreases the local Gaussian
potential. -/
theorem collisionWordLocalPairPotential_le_exp (β : ℝ) {h : ℕ} (x : Fin h → Site) :
    collisionWordLocalPairPotential β x ≤ Real.exp (β ^ 2 * replicaPotential x) := by
  classical
  rw [collisionWordLocalPairPotential, exp_potential_eq_prod_pairs, Finset.mul_sum]
  apply collisionWord_one_add_sum_le_prod
  intro α
  apply mul_nonneg (sigmaSq_nonneg β)
  split_ifs <;> norm_num

/-- The sum of local active moments involving at least three labels is
nonnegative, as it is the full potential minus its pair-simple part. -/
theorem localNonpair_sum_nonneg (β : ℝ) {h : ℕ} (x : Fin h → Site) :
    0 ≤ ∑ A ∈ (Finset.univ : Finset (Fin h)).powerset.filter (fun A => 3 ≤ A.card),
      collisionWordLocalVertexMoment β x A := by
  have he := exp_replicaPotential_eq_pair_add_nonpair β x
  have hle := collisionWordLocalPairPotential_le_exp β x
  change 1 + sigmaSq β * (∑ α : CollisionPair h,
    if x α.1.1 = x α.1.2 then (1 : ℝ) else 0) ≤ _ at hle
  linarith only [he, hle]

/-- The full local potential is dominated by its free and pair part plus
the absolute non-pair CCR partition moments. -/
theorem exp_replicaPotential_le_pair_add_nonpairMoments (β : ℝ) {h : ℕ}
    (x : Fin h → Site) :
    Real.exp (β ^ 2 * replicaPotential x) ≤ collisionWordLocalPairPotential β x +
      ∑ I ∈ (Finset.univ : Finset (ReplicaPartition h)).filter
        (fun I => I ≠ ⊥ ∧ (∀ α : CollisionPair h, I ≠ pairPartition α) ∧
          IsCollisionConfiguration I x), |replicaPartitionDisorderMoment β I| := by
  have hbound := abs_localNonpair_sum_le_partitionMoments β x
  have hnonneg := localNonpair_sum_nonneg β x
  rw [abs_of_nonneg hnonneg] at hbound
  rw [exp_replicaPotential_eq_pair_add_nonpair]
  exact add_le_add (le_refl (collisionWordLocalPairPotential β x)) hbound

end Critical2DKPZ.SHF.Moments

end
