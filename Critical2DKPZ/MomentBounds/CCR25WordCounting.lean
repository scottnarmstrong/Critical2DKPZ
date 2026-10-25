/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25GeometricSeries
import Mathlib.Tactic

/-! # Finite CCR25 partition-word counting -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

/-- Encode a partition by the finite relation graph on ordered replica pairs. -/
noncomputable def ccr25PartitionRelationEncoding {h : ℕ}
    (I : ReplicaPartition h) : Finset (Fin h × Fin h) := by
  classical
  exact Finset.univ.filter (fun p => I.r p.1 p.2)

/-- The relation-graph encoding determines the partition. -/
theorem ccr25PartitionRelationEncoding_injective {h : ℕ} :
    Function.Injective (ccr25PartitionRelationEncoding (h := h)) := by
  intro I J hIJ
  apply Setoid.ext
  intro i j
  have hmem : (i, j) ∈ ccr25PartitionRelationEncoding I ↔
      (i, j) ∈ ccr25PartitionRelationEncoding J := by rw [hIJ]
  simpa only [ccr25PartitionRelationEncoding, Finset.mem_filter, Finset.mem_univ,
    true_and] using hmem

/-- A crude explicit Bell-number bound, obtained by injecting equivalence
relations into subsets of the ordered pair set. -/
theorem replicaPartition_card_le_two_pow_sq (h : ℕ) :
    Fintype.card (ReplicaPartition h) ≤ 2 ^ (h * h) := by
  have hinj := ccr25PartitionRelationEncoding_injective (h := h)
  have hcard := Fintype.card_le_of_injective
    (ccr25PartitionRelationEncoding (h := h)) hinj
  calc
    Fintype.card (ReplicaPartition h) ≤ Fintype.card (Finset (Fin h × Fin h)) := hcard
    _ = 2 ^ (h * h) := by simp

/-- The number of admissible length-`n + 1` partition words is bounded by the
number of all words on the finite partition alphabet. -/
theorem ccr25_admissibleWords_card_le {h n : ℕ} :
    (ccr25AdmissibleWords h n).card ≤ Fintype.card (ReplicaPartition h) ^ (n + 1) := by
  calc
    (ccr25AdmissibleWords h n).card ≤
        Fintype.card (Fin (n + 1) → ReplicaPartition h) :=
      Finset.card_le_univ _
    _ = Fintype.card (ReplicaPartition h) ^ (n + 1) := by
      simp only [Fintype.card_fun, Fintype.card_fin]

/-- An entirely elementary explicit cardinal bound for admissible words. -/
theorem ccr25_admissibleWords_card_le_explicit {h n : ℕ} :
    (ccr25AdmissibleWords h n).card ≤ 2 ^ ((h * h) * (n + 1)) := by
  calc
    (ccr25AdmissibleWords h n).card ≤ Fintype.card (ReplicaPartition h) ^ (n + 1) :=
      ccr25_admissibleWords_card_le
    _ ≤ (2 ^ (h * h)) ^ (n + 1) :=
      pow_le_pow_left' (replicaPartition_card_le_two_pow_sq h) _
    _ = 2 ^ ((h * h) * (n + 1)) := by rw [← pow_mul]


/-- Explicit version of the word-weight bound, with no opaque alphabet-size
constant. -/
theorem ccr25_admissibleWords_weight_sum_le_explicit {h n : ℕ}
    (mom : ReplicaPartition h → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hmom : ∀ I, |mom I| ≤ M) :
    (∑ I ∈ ccr25AdmissibleWords h n,
      ∏ j : Fin (n + 1), |mom (I j)|) ≤
      (M * (2 ^ (h * h) : ℝ)) ^ (n + 1) := by
  classical
  have hcard : ((ccr25AdmissibleWords h n).card : ℝ) ≤
      (2 ^ ((h * h) * (n + 1)) : ℝ) := by
    exact_mod_cast ccr25_admissibleWords_card_le_explicit (h := h) (n := n)
  have hcount : (2 ^ ((h * h) * (n + 1)) : ℝ) =
      ((2 ^ (h * h) : ℝ) ^ (n + 1)) := by
    exact_mod_cast (show 2 ^ ((h * h) * (n + 1)) =
      (2 ^ (h * h)) ^ (n + 1) by rw [pow_mul])
  rw [hcount] at hcard
  exact ccr25_wordWeight_sum_le (ccr25AdmissibleWords h n) mom M
    (2 ^ (h * h) : ℝ) hM hmom hcard

/-- The finite operator word estimate after applying an explicit bound on
partition moments and the elementary partition-alphabet count. This is the
finite-run input to the geometric summation in CSZ25. -/
theorem ccr25_finite_word_operator_bound {h n : ℕ}
    (s : Finset (LatticeConfiguration h)) (L : ℕ) (lam β : ℝ)
    (W : LatticeConfiguration h → ℝ) (hW : ∀ x ∈ s, 0 < W x)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (u v : ReplicaPartition h → LatticeConfiguration h → ℝ)
    (mom : ReplicaPartition h → ℝ) (M cU cQ left right : ℝ)
    (hM : 0 ≤ M) (hmom : ∀ I, |mom I| ≤ M)
    (hCU : 0 ≤ cU) (hCQ : 0 ≤ cQ) (hleft : 0 ≤ left) (hright : 0 ≤ right)
    (hleft_bound : ∀ I, I ≠ ⊥ →
      finiteLpNorm s p (fun x => u I x / W x) ≤ left)
    (hright_bound : ∀ I, I ≠ ⊥ →
      finiteLpNorm s q (fun x => W x * v I x) ≤ right)
    (hU_bound : ∀ I, I ≠ ⊥ → ∀ f : LatticeConfiguration h → ℝ,
      finiteLpNorm s q
        (finiteKernelApply s
          (weightedKernel W (ccr25LabelKernel L lam β (.interacting I))) f) ≤
        cU * finiteLpNorm s q f)
    (hQ_bound : ∀ I J, I ≠ ⊥ → J ≠ ⊥ → I ≠ J →
      ∀ f : LatticeConfiguration h → ℝ,
      finiteLpNorm s q
        (finiteKernelApply s
          (weightedKernel W (ccr25LabelKernel L lam β (.free I J))) f) ≤
        cQ * finiteLpNorm s q f) :
    (∑ I ∈ ccr25AdmissibleWords h n,
      (∏ j : Fin (n + 1), |mom (I j)|) *
        ccr25FiniteWordPairing s L lam β I u v) ≤
      left * right *
        (cU * M * (2 ^ (h * h) : ℝ)) ^ (n + 1) * cQ ^ n := by
  have hop := ccr25_finite_word_bound (h := h) (n := n)
    s L lam β W hW hpq u v mom cU cQ left right
    hCU hCQ hleft hleft_bound hright_bound hU_bound hQ_bound
  have hweights := ccr25_admissibleWords_weight_sum_le_explicit
    (h := h) (n := n) mom M hM hmom
  have hcoeff : 0 ≤ left * right * cU ^ (n + 1) * cQ ^ n := by positivity
  calc
    (∑ I ∈ ccr25AdmissibleWords h n,
        (∏ j : Fin (n + 1), |mom (I j)|) *
          ccr25FiniteWordPairing s L lam β I u v) ≤
        left * right * cU ^ (n + 1) * cQ ^ n *
          ∑ I ∈ ccr25AdmissibleWords h n, ∏ j : Fin (n + 1), |mom (I j)| := hop
    _ ≤ left * right * cU ^ (n + 1) * cQ ^ n *
          (M * (2 ^ (h * h) : ℝ)) ^ (n + 1) :=
      mul_le_mul_of_nonneg_left hweights hcoeff
    _ = left * right *
          (cU * M * (2 ^ (h * h) : ℝ)) ^ (n + 1) * cQ ^ n := by
      calc
        _ = left * right * (cU ^ (n + 1) *
              (M * (2 ^ (h * h) : ℝ)) ^ (n + 1)) * cQ ^ n := by ring
        _ = left * right *
              (cU * (M * (2 ^ (h * h) : ℝ))) ^ (n + 1) * cQ ^ n := by
          rw [← mul_pow]
        _ = left * right *
              (cU * M * (2 ^ (h * h) : ℝ)) ^ (n + 1) * cQ ^ n := by ring

end Critical2DKPZ.MomentBounds

end
