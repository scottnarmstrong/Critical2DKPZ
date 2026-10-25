/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationValidWords
public import Critical2DKPZ.MomentBounds.CollisionStrata
public import Critical2DKPZ.SHF.DeltaBose.CollisionWords
import Mathlib.Tactic

/-! # Pair-partition encodings of collision words -/

@[expose] public section

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

/-- The partition attached to one collision pair is nontrivial. -/
theorem pairPartition_ne_bot {h : ℕ} (α : CollisionPair h) :
    pairPartition α ≠ (⊥ : ReplicaPartition h) := by
  intro he
  have hrel := pairPartition_related α
  rw [he] at hrel
  have hEq : α.val.1 = α.val.2 := by simpa using hrel
  exact (ne_of_lt α.property) hEq

/-- The pair-partition map remembers the collision pair. -/
theorem pairPartition_injective {h : ℕ} :
    Function.Injective (pairPartition : CollisionPair h → ReplicaPartition h) := by
  intro α β hαβ
  have hrel : (pairPartition β).r α.val.1 α.val.2 := by
    rw [← hαβ]
    exact pairPartition_related α
  have hchoices := (pairPartition_rel β α.val.1 α.val.2).mp hrel
  have hendpoints : α.val.1 = β.val.1 ∧ α.val.2 = β.val.2 := by
    rcases hchoices with heq | ⟨hleft, hright⟩
    · omega
    · rcases hleft with hleft | hleft <;>
        rcases hright with hright | hright <;> omega
  apply Subtype.ext
  exact Prod.ext hendpoints.1 hendpoints.2

/-- Replace each letter of a collision word by its pair partition. -/
@[instance_reducible] def collisionWordPairPartition {h n : ℕ}
    (w : CollisionWord h (n + 1)) :
    Fin (n + 1) → ReplicaPartition h :=
  fun j => pairPartition (w.1 j)

/-- Every label in the partition word is nontrivial. -/
theorem collisionWordPairPartition_ne_bot {h n : ℕ}
    (w : CollisionWord h (n + 1)) (j : Fin (n + 1)) :
    collisionWordPairPartition w j ≠ (⊥ : ReplicaPartition h) :=
  pairPartition_ne_bot (w.1 j)

/-- Adjacent letters remain distinct pair partitions. -/
theorem collisionWordPairPartition_adjacent_ne {h n : ℕ}
    (w : CollisionWord h (n + 1)) (j : Fin n) :
    collisionWordPairPartition w j.castSucc ≠
      collisionWordPairPartition w j.succ := by
  intro he
  have hword := w.2 j.castSucc j.succ (by simp)
  exact hword (pairPartition_injective he)


/-- A finite CCR operator word attached to a collision word is bounded by the
product of its interacting and free operator costs. This statement does not
assume full support, which is needed for h=4 words using only three labels. -/
theorem ccr25FinitePairCollisionWordPairing_le {h n : ℕ}
    (w : CollisionWord h (n + 1))
    (s : Finset (LatticeConfiguration h)) (L : ℕ) (lam β : ℝ)
    (W : LatticeConfiguration h → ℝ) (hW : ∀ x ∈ s, 0 < W x)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (u v : ReplicaPartition h → LatticeConfiguration h → ℝ)
    (cU cQ left right : ℝ) (hCU : 0 ≤ cU) (hCQ : 0 ≤ cQ)
    (hleft : 0 ≤ left)
    (hleft_bound : ∀ I, I ≠ ⊥ →
      finiteLpNorm s p (fun x => u I x / W x) ≤ left)
    (hright_bound : ∀ I, I ≠ ⊥ →
      finiteLpNorm s q (fun x => W x * v I x) ≤ right)
    (hU_bound : ∀ I, I ≠ ⊥ → ∀ f : LatticeConfiguration h → ℝ,
      finiteLpNorm s q (finiteKernelApply s
        (weightedKernel W
          (ccr25LabelKernel L lam β (.interacting I))) f) ≤
        cU * finiteLpNorm s q f)
    (hQ_bound : ∀ I J, I ≠ ⊥ → J ≠ ⊥ → I ≠ J →
      ∀ f : LatticeConfiguration h → ℝ,
        finiteLpNorm s q (finiteKernelApply s
          (weightedKernel W (ccr25LabelKernel L lam β (.free I J))) f) ≤
          cQ * finiteLpNorm s q f) :
    ccr25FiniteWordPairing s L lam β (collisionWordPairPartition w) u v ≤
      left * right * cU ^ (n + 1) * cQ ^ n := by
  exact collisionWord_finite_valid_partition_word_pairing_le
    (collisionWordPairPartition w) (collisionWordPairPartition_ne_bot w)
    (collisionWordPairPartition_adjacent_ne w) s L lam β W hW hpq u v
    cU cQ left right hCU hCQ hleft hleft_bound hright_bound hU_bound hQ_bound

end Critical2DKPZ.SHF.Moments

end
