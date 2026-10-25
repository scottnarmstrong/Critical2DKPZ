/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25WordCounting
import Mathlib.Tactic

/-! # CCR operator words without a full-support requirement -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.MomentBounds

/-- Nontrivial, adjacent-distinct partition words. Labels need not cover
every replica: untouched replicas remain free spectators. -/
def collisionWordValidPartitionWords (h n : ℕ) : Finset (Fin (n + 1) → ReplicaPartition h) := by
  classical
  exact Finset.univ.filter (fun I => (∀ j, I j ≠ ⊥) ∧
    ∀ j : Fin n, I j.castSucc ≠ I j.succ)

/-- The CCR word estimate only requires nontriviality and adjacent distinct
letters. No full-support hypothesis is needed for its operator factorization. -/
theorem collisionWord_finite_valid_partition_word_pairing_le {h n : ℕ}
    (I : Fin (n + 1) → ReplicaPartition h)
    (hpart : ∀ j, I j ≠ ⊥) (hadj : ∀ j : Fin n, I j.castSucc ≠ I j.succ)
    (s : Finset (LatticeConfiguration h)) (L : ℕ) (lam β : ℝ)
    (W : LatticeConfiguration h → ℝ) (hW : ∀ x ∈ s, 0 < W x)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (u v : ReplicaPartition h → LatticeConfiguration h → ℝ)
    (cU cQ left right : ℝ) (hcU : 0 ≤ cU) (hcQ : 0 ≤ cQ) (hleft : 0 ≤ left)
    (hleft_bound : ∀ J, J ≠ ⊥ → finiteLpNorm s p (fun x => u J x / W x) ≤ left)
    (hright_bound : ∀ J, J ≠ ⊥ → finiteLpNorm s q (fun x => W x * v J x) ≤ right)
    (hU_bound : ∀ J, J ≠ ⊥ → ∀ f : LatticeConfiguration h → ℝ,
      finiteLpNorm s q (finiteKernelApply s
        (weightedKernel W (ccr25LabelKernel L lam β (.interacting J))) f) ≤
          cU * finiteLpNorm s q f)
    (hQ_bound : ∀ J K, J ≠ ⊥ → K ≠ ⊥ → J ≠ K → ∀ f : LatticeConfiguration h → ℝ,
      finiteLpNorm s q (finiteKernelApply s
        (weightedKernel W (ccr25LabelKernel L lam β (.free J K))) f) ≤
          cQ * finiteLpNorm s q f) :
    ccr25FiniteWordPairing s L lam β I u v ≤ left * right * cU ^ (n + 1) * cQ ^ n := by
  let labels := ccr25PartitionWordLabels n I
  let K : CCR25OperatorLabel h → LatticeConfiguration h →
      LatticeConfiguration h → ℝ := ccr25LabelKernel L lam β
  let c : CCR25OperatorLabel h → ℝ := ccr25LabelCost cU cQ
  have hvalid : ∀ a ∈ labels, ccr25LabelValid a :=
    ccr25PartitionWordLabels_valid I hpart hadj
  have hcost : ∀ a, 0 ≤ c a := by
    intro a
    cases a with
    | interacting J => exact hcU
    | free J K => exact hcQ
  have hop : ∀ a ∈ labels, ∀ f,
      finiteLpNorm s q (finiteKernelApply s (weightedKernel W (K a)) f) ≤
        c a * finiteLpNorm s q f := by
    intro a ha f
    cases a with
    | interacting J =>
        simpa [K, c, ccr25LabelCost] using hU_bound J (hvalid _ ha) f
    | free J K' =>
        obtain ⟨hJ, hK, hJK⟩ := hvalid _ ha
        simpa [K, c, ccr25LabelCost] using hQ_bound J K' hJ hK hJK f
  have hpair := finite_weighted_taggedKernelWord_pairing_le s hpq W hW
    labels K c hcost hop (u (I 0)) (v (I (Fin.last n)))
  have hprod : (labels.map c).prod = cU ^ (n + 1) * cQ ^ n :=
    ccr25PartitionWordLabels_cost_prod cU cQ I
  have hprod0 : 0 ≤ (labels.map c).prod :=
    List.prod_nonneg (by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact hcost b)
  have hleftI := hleft_bound (I 0) (hpart 0)
  have hrightI := hright_bound (I (Fin.last n)) (hpart _)
  calc
    _ ≤ finiteLpNorm s p (fun x => u (I 0) x / W x) *
        (labels.map c).prod * finiteLpNorm s q (fun x => W x * v (I (Fin.last n)) x) := by
      simpa [ccr25FiniteWordPairing, finiteTaggedKernelWordApply, labels, K] using hpair
    _ ≤ left * (labels.map c).prod * right := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right hleftI hprod0) hrightI
        (finiteLpNorm_nonneg _ _ _) (mul_nonneg hleft hprod0)
    _ = _ := by rw [hprod]; ring

/-- A uniform letter weight and the elementary partition-alphabet count
bound all valid CCR words, including words with free spectators. -/
theorem collisionWord_valid_word_constantMoment_operator_bound {h n : ℕ}
    (s : Finset (LatticeConfiguration h)) (L : ℕ) (lam β : ℝ)
    (W : LatticeConfiguration h → ℝ) (hW : ∀ x ∈ s, 0 < W x)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (u v : ReplicaPartition h → LatticeConfiguration h → ℝ)
    (σ cU cQ left right : ℝ) (hσ : 0 ≤ σ)
    (hcU : 0 ≤ cU) (hcQ : 0 ≤ cQ) (hleft : 0 ≤ left) (hright : 0 ≤ right)
    (hleft_bound : ∀ J, J ≠ ⊥ → finiteLpNorm s p (fun x => u J x / W x) ≤ left)
    (hright_bound : ∀ J, J ≠ ⊥ → finiteLpNorm s q (fun x => W x * v J x) ≤ right)
    (hU_bound : ∀ J, J ≠ ⊥ → ∀ f : LatticeConfiguration h → ℝ,
      finiteLpNorm s q (finiteKernelApply s
        (weightedKernel W (ccr25LabelKernel L lam β (.interacting J))) f) ≤
          cU * finiteLpNorm s q f)
    (hQ_bound : ∀ J K, J ≠ ⊥ → K ≠ ⊥ → J ≠ K → ∀ f : LatticeConfiguration h → ℝ,
      finiteLpNorm s q (finiteKernelApply s
        (weightedKernel W (ccr25LabelKernel L lam β (.free J K))) f) ≤
          cQ * finiteLpNorm s q f) :
    (∑ I ∈ collisionWordValidPartitionWords h n, σ ^ (n + 1) *
      ccr25FiniteWordPairing s L lam β I u v) ≤
      left * right * (cU * σ * (2 ^ (h * h) : ℝ)) ^ (n + 1) * cQ ^ n := by
  classical
  let b := σ ^ (n + 1) * (left * right * cU ^ (n + 1) * cQ ^ n)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hcard : ((collisionWordValidPartitionWords h n).card : ℝ) ≤
      (2 ^ (h * h) : ℝ) ^ (n + 1) := by
    have hc : (collisionWordValidPartitionWords h n).card ≤
        Fintype.card (ReplicaPartition h) ^ (n + 1) := by
      simpa using Finset.card_le_univ (collisionWordValidPartitionWords h n)
    have hc' := hc.trans (pow_le_pow_left' (replicaPartition_card_le_two_pow_sq h) (n + 1))
    exact_mod_cast hc'
  calc
    _ ≤ ∑ _I ∈ collisionWordValidPartitionWords h n, b := by
      apply Finset.sum_le_sum
      intro I hI
      obtain ⟨hpart, hadj⟩ := (Finset.mem_filter.mp hI).2
      exact mul_le_mul_of_nonneg_left
        (collisionWord_finite_valid_partition_word_pairing_le I hpart hadj s L lam β W hW hpq
          u v cU cQ left right hcU hcQ hleft hleft_bound hright_bound hU_bound hQ_bound)
        (pow_nonneg hσ _)
    _ = ((collisionWordValidPartitionWords h n).card : ℝ) * b := by simp
    _ ≤ (2 ^ (h * h) : ℝ) ^ (n + 1) * b := mul_le_mul_of_nonneg_right hcard hb
    _ = _ := by dsimp [b]; rw [mul_pow, mul_pow]; ring

end Critical2DKPZ.SHF.Moments

end
