/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25Operators
public import Critical2DKPZ.MomentBounds.PairSelection
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-! # Finite partition words and CCR25's operator factorization -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- A typed CCR25 operator label keeps free and interacting operator bounds
separate even when two kernels happen to be extensionally equal. -/
inductive CCR25OperatorLabel (h : ℕ)
  | interacting (I : ReplicaPartition h)
  | free (I J : ReplicaPartition h)

/-- The alternating operator labels along a partition word. -/
def ccr25PartitionWordLabels {h : ℕ} : (n : ℕ) →
    (Fin (n + 1) → ReplicaPartition h) → List (CCR25OperatorLabel h)
  | 0, I => [.interacting (I 0)]
  | n + 1, I => .interacting (I 0) :: .free (I 0) (I 1) ::
      ccr25PartitionWordLabels n (fun j => I j.succ)

/-- The operator kernel named by a CCR25 factor label. -/
def ccr25LabelKernel {h : ℕ} (L : ℕ) (lam β : ℝ) :
    CCR25OperatorLabel h → LatticeConfiguration h → LatticeConfiguration h → ℝ
  | .interacting I => hattedInteractingReplicaKernelAbs L lam β I
  | .free I J => hattedFreeReplicaKernel L I J

/-- The constant assigned to each occurrence of a free or interacting
operator in the factorization. -/
def ccr25LabelCost {h : ℕ} (cU cQ : ℝ) : CCR25OperatorLabel h → ℝ
  | .interacting _ => cU
  | .free _ _ => cQ

/-- A free factor is used only between distinct nontrivial partition runs. -/
def ccr25LabelValid {h : ℕ} : CCR25OperatorLabel h → Prop
  | .interacting I => I ≠ ⊥
  | .free I J => I ≠ ⊥ ∧ J ≠ ⊥ ∧ I ≠ J

/-- Apply a word of typed kernel labels from left to right, preserving the
separate bound attached to each operator type and index. -/
def finiteTaggedKernelWordApply {α ι : Type*} (s : Finset α)
    (K : ι → α → α → ℝ) (word : List ι) (f : α → ℝ) : α → ℝ :=
  finiteKernelWordApply s (word.map K) f

/-- Conjugating each kernel in a finite word conjugates the resulting word application. -/
theorem finiteTaggedKernelWordApply_weighted {α ι : Type*} [DecidableEq α]
    (s : Finset α) (W : α → ℝ) (hW : ∀ x ∈ s, 0 < W x)
    (K : ι → α → α → ℝ) (word : List ι) (f : α → ℝ) :
    ∀ x ∈ s,
      finiteTaggedKernelWordApply s (fun i => weightedKernel W (K i)) word
          (fun y => W y * f y) x =
        W x * finiteTaggedKernelWordApply s K word f x := by
  intro x hx
  change finiteKernelWordApply s
      (word.map (fun i => weightedKernel W (K i))) (fun y => W y * f y) x = _
  have hmap :
      word.map (fun i => weightedKernel W (K i)) =
        (word.map K).map (weightedKernel W) := by
    induction word with
    | nil => rfl
    | cons i is ih => simp [ih]
  rw [hmap]
  exact finiteKernelWordApply_weighted s W hW (word.map K) f x hx

/-- Weighted norm bound for a tagged word, with a possibly different operator
bound for each free or interacting factor. -/
theorem finiteTaggedKernelWordApply_weighted_norm_le {α ι : Type*} [DecidableEq α]
    {q : ℝ} (s : Finset α) (W : α → ℝ) (word : List ι)
    (K : ι → α → α → ℝ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hbound : ∀ i ∈ word, ∀ f,
      finiteLpNorm s q (finiteKernelApply s (weightedKernel W (K i)) f) ≤
        c i * finiteLpNorm s q f)
    (f : α → ℝ) :
    finiteLpNorm s q
      (finiteTaggedKernelWordApply s (fun i => weightedKernel W (K i)) word f) ≤
      (word.map c).prod * finiteLpNorm s q f := by
  induction word with
  | nil =>
      simp [finiteTaggedKernelWordApply, finiteKernelWordApply]
  | cons i is ih =>
      have hi := hbound i (by simp) (finiteTaggedKernelWordApply s
        (fun j => weightedKernel W (K j)) is f)
      have ht := ih (by
        intro j hj g
        exact hbound j (by simp [hj]) g)
      change finiteLpNorm s q
          (finiteKernelApply s (weightedKernel W (K i))
            (finiteTaggedKernelWordApply s
              (fun j => weightedKernel W (K j)) is f)) ≤ _
      calc
        finiteLpNorm s q
            (finiteKernelApply s (weightedKernel W (K i))
              (finiteTaggedKernelWordApply s
                (fun j => weightedKernel W (K j)) is f)) ≤
            c i * finiteLpNorm s q
              (finiteTaggedKernelWordApply s
                (fun j => weightedKernel W (K j)) is f) := hi
        _ ≤ c i * ((is.map c).prod * finiteLpNorm s q f) :=
          mul_le_mul_of_nonneg_left ht (hc i)
        _ = ((i :: is).map c).prod * finiteLpNorm s q f := by
          simp only [List.map_cons, List.prod_cons]
          ring

/-- Finite weighted pairing estimate for a tagged kernel word. -/
theorem finite_weighted_taggedKernelWord_pairing_le {α ι : Type*}
    [DecidableEq α] (s : Finset α) {p q : ℝ} (hpq : p.HolderConjugate q)
    (W : α → ℝ) (hW : ∀ x ∈ s, 0 < W x)
    (word : List ι) (K : ι → α → α → ℝ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hbound : ∀ i ∈ word, ∀ f,
      finiteLpNorm s q (finiteKernelApply s (weightedKernel W (K i)) f) ≤
        c i * finiteLpNorm s q f)
    (u v : α → ℝ) :
    (∑ x ∈ s, u x * finiteTaggedKernelWordApply s K word v x) ≤
      finiteLpNorm s p (fun x => u x / W x) *
        (word.map c).prod *
        finiteLpNorm s q (fun x => W x * v x) := by
  let uW : α → ℝ := fun x => u x / W x
  let vW : α → ℝ := fun x => W x * v x
  have hcov (x : α) (hx : x ∈ s) :
      finiteTaggedKernelWordApply s (fun i => weightedKernel W (K i)) word vW x =
        W x * finiteTaggedKernelWordApply s K word v x := by
    simpa [uW, vW] using
      finiteTaggedKernelWordApply_weighted s W hW K word v x hx
  have hpair :
      (∑ x ∈ s, u x * finiteTaggedKernelWordApply s K word v x) =
        ∑ x ∈ s, uW x *
          finiteTaggedKernelWordApply s (fun i => weightedKernel W (K i)) word vW x := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [hcov x hx]
    dsimp [uW]
    field_simp [ne_of_gt (hW x hx)]
  have hword := finiteTaggedKernelWordApply_weighted_norm_le s W word K c hc hbound
    (q := q) vW
  have hholder := Real.inner_le_Lp_mul_Lq s uW
    (finiteTaggedKernelWordApply s (fun i => weightedKernel W (K i)) word vW) hpq
  calc
    (∑ x ∈ s, u x * finiteTaggedKernelWordApply s K word v x) =
        ∑ x ∈ s, uW x *
          finiteTaggedKernelWordApply s (fun i => weightedKernel W (K i)) word vW x := hpair
    _ ≤ finiteLpNorm s p uW *
        finiteLpNorm s q
          (finiteTaggedKernelWordApply s (fun i => weightedKernel W (K i)) word vW) := by
      simpa [finiteLpNorm, uW] using hholder
    _ ≤ finiteLpNorm s p uW * ((word.map c).prod * finiteLpNorm s q vW) :=
      mul_le_mul_of_nonneg_left hword (finiteLpNorm_nonneg s p uW)
    _ = finiteLpNorm s p uW * (word.map c).prod * finiteLpNorm s q vW := by ring

/-- A finite-volume word pairing in the row/column convention of CCR25. -/
def ccr25FiniteWordPairing {h n : ℕ} (s : Finset (LatticeConfiguration h))
    (L : ℕ) (lam β : ℝ) (I : Fin (n + 1) → ReplicaPartition h)
    (u v : ReplicaPartition h → LatticeConfiguration h → ℝ) : ℝ := by
  classical
  exact ∑ x ∈ s, u (I 0) x *
    finiteKernelWordApply s
      ((ccr25PartitionWordLabels n I).map (ccr25LabelKernel L lam β))
      (v (I (Fin.last n))) x

/-- Full support of a finite partition word: each replica label appears in a
nonsingleton block at some word position. -/
def ccr25WordFullSupport {h : ℕ} {n : ℕ}
    (I : Fin (n + 1) → ReplicaPartition h) : Prop :=
  ∀ a : Fin h, ∃ j : Fin (n + 1), InCollisionBlock (I j) a

/-- The admissibility conditions for a CCR25 partition word. -/
def ccr25AdmissibleWord {h : ℕ} {n : ℕ}
    (I : Fin (n + 1) → ReplicaPartition h) : Prop :=
  (∀ j, I j ≠ ⊥) ∧
  (∀ j : Fin n, I j.castSucc ≠ I j.succ) ∧
  ccr25WordFullSupport I

/-- The labels extracted from a partition word satisfy the required validity condition. -/
theorem ccr25PartitionWordLabels_valid {h n : ℕ}
    (I : Fin (n + 1) → ReplicaPartition h)
    (hpart : ∀ j, I j ≠ ⊥)
    (hadj : ∀ j : Fin n, I j.castSucc ≠ I j.succ) :
    ∀ a ∈ ccr25PartitionWordLabels n I, ccr25LabelValid a := by
  induction n with
  | zero =>
      intro a ha
      simp only [ccr25PartitionWordLabels, List.mem_singleton] at ha
      subst a
      exact hpart 0
  | succ n ih =>
      intro a ha
      simp only [ccr25PartitionWordLabels, List.mem_cons] at ha
      rcases ha with rfl | rfl | ha
      · exact hpart 0
      · refine ⟨hpart 0, hpart 1, ?_⟩
        simpa using hadj (0 : Fin (n + 1))
      · apply ih (fun j => I j.succ)
        · intro j
          exact hpart j.succ
        · intro j
          have hj := hadj j.succ
          have he : (j.castSucc).succ = (j.succ).castSucc := by
            apply Fin.ext
            simp
          rw [he]
          exact hj
        · exact ha

/-- The product of label costs equals the partition-word cost. -/
theorem ccr25PartitionWordLabels_cost_prod {h n : ℕ}
    (cU cQ : ℝ) (I : Fin (n + 1) → ReplicaPartition h) :
    ((ccr25PartitionWordLabels n I).map (ccr25LabelCost cU cQ)).prod =
      cU ^ (n + 1) * cQ ^ n := by
  induction n with
  | zero => simp [ccr25PartitionWordLabels, ccr25LabelCost]
  | succ n ih =>
      simp only [ccr25PartitionWordLabels, List.map_cons,
        ccr25LabelCost, List.prod_cons]
      rw [ih (fun j => I j.succ)]
      simp only [pow_succ]
      ring

/-- The finite set of admissible words with `n + 1` collision runs. -/
def ccr25AdmissibleWords (h n : ℕ) : Finset (Fin (n + 1) → ReplicaPartition h) := by
  classical
  exact Finset.univ.filter ccr25AdmissibleWord

/-- Finite-volume CCR25 word bound. The endpoint norms and the individual
free/interacting operator bounds are explicit hypotheses; the conclusion
retains the exact absolute disorder-moment weight of each admissible word. -/
theorem ccr25_finite_word_bound {h n : ℕ}
    (s : Finset (LatticeConfiguration h)) (L : ℕ) (lam β : ℝ)
    (W : LatticeConfiguration h → ℝ) (hW : ∀ x ∈ s, 0 < W x)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (u v : ReplicaPartition h → LatticeConfiguration h → ℝ)
    (mom : ReplicaPartition h → ℝ) (cU cQ left right : ℝ)
    (hCU : 0 ≤ cU) (hCQ : 0 ≤ cQ) (hleft : 0 ≤ left)
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
        cQ * finiteLpNorm s q f)
    :
    (∑ I ∈ ccr25AdmissibleWords h n,
      (∏ j : Fin (n + 1), |mom (I j)|) *
        ccr25FiniteWordPairing s L lam β I u v) ≤
      left * right * cU ^ (n + 1) * cQ ^ n *
        ∑ I ∈ ccr25AdmissibleWords h n, ∏ j : Fin (n + 1), |mom (I j)| := by
  classical
  let words := ccr25AdmissibleWords h n
  let K : CCR25OperatorLabel h → LatticeConfiguration h →
      LatticeConfiguration h → ℝ := ccr25LabelKernel L lam β
  let c : CCR25OperatorLabel h → ℝ := ccr25LabelCost cU cQ
  have hword_bound : ∀ I ∈ words,
      ccr25FiniteWordPairing s L lam β I u v ≤
        left * right * cU ^ (n + 1) * cQ ^ n := by
    intro I hI
    have hIadm : ccr25AdmissibleWord I := (Finset.mem_filter.mp hI).2
    have hvalid : ∀ a ∈ ccr25PartitionWordLabels n I, ccr25LabelValid a := by
      apply ccr25PartitionWordLabels_valid
      · exact hIadm.1
      · exact hIadm.2.1
    have hcost : ∀ a, 0 ≤ c a := by
      intro a
      cases a with
      | interacting J => exact hCU
      | free J J' => exact hCQ
    have hfactor_bound : ∀ a ∈ ccr25PartitionWordLabels n I, ∀ f,
        finiteLpNorm s q (finiteKernelApply s (weightedKernel W (K a)) f) ≤
          c a * finiteLpNorm s q f := by
      intro a ha f
      cases a with
      | interacting J =>
          have hJ : J ≠ ⊥ := hvalid (.interacting J) ha
          simpa [K, c, ccr25LabelKernel, ccr25LabelCost] using hU_bound J hJ f
      | free J J' =>
          obtain ⟨hJ, hJ', hne⟩ := hvalid (.free J J') ha
          simpa [K, c, ccr25LabelKernel, ccr25LabelCost] using
            hQ_bound J J' hJ hJ' hne f
    have hpair := finite_weighted_taggedKernelWord_pairing_le s hpq W hW
      (ccr25PartitionWordLabels n I) K c hcost hfactor_bound
      (u (I 0)) (v (I (Fin.last n)))
    have hcostprod :
        ((ccr25PartitionWordLabels n I).map c).prod = cU ^ (n + 1) * cQ ^ n := by
      simpa [c] using ccr25PartitionWordLabels_cost_prod cU cQ I
    have hleftI : finiteLpNorm s p (fun x => u (I 0) x / W x) ≤ left :=
      hleft_bound (I 0) (hIadm.1 0)
    have hrightI : finiteLpNorm s q (fun x => W x * v (I (Fin.last n)) x) ≤ right :=
      hright_bound (I (Fin.last n)) (hIadm.1 (Fin.last n))
    have hprod_nonneg : 0 ≤
        ((ccr25PartitionWordLabels n I).map c).prod :=
      List.prod_nonneg (by
        intro a ha
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        exact hcost b)
    calc
      ccr25FiniteWordPairing s L lam β I u v ≤
          finiteLpNorm s p (fun x => u (I 0) x / W x) *
            ((ccr25PartitionWordLabels n I).map c).prod *
            finiteLpNorm s q (fun x => W x * v (I (Fin.last n)) x) := by
        simpa [ccr25FiniteWordPairing, finiteTaggedKernelWordApply, K] using hpair
      _ ≤ left * ((ccr25PartitionWordLabels n I).map c).prod * right := by
        calc
          _ ≤ left * ((ccr25PartitionWordLabels n I).map c).prod *
              finiteLpNorm s q (fun x => W x * v (I (Fin.last n)) x) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hleftI hprod_nonneg)
              (finiteLpNorm_nonneg s q (fun x => W x * v (I (Fin.last n)) x))
          _ ≤ left * ((ccr25PartitionWordLabels n I).map c).prod * right :=
            mul_le_mul_of_nonneg_left hrightI (mul_nonneg hleft hprod_nonneg)
      _ = left * right * cU ^ (n + 1) * cQ ^ n := by rw [hcostprod]; ring
  have hweighted : ∀ I ∈ words,
      (∏ j : Fin (n + 1), |mom (I j)|) * ccr25FiniteWordPairing s L lam β I u v ≤
        (∏ j : Fin (n + 1), |mom (I j)|) *
          (left * right * cU ^ (n + 1) * cQ ^ n) := by
    intro I hI
    exact mul_le_mul_of_nonneg_left (hword_bound I hI)
      (Finset.prod_nonneg fun j _ => abs_nonneg _)
  calc
    (∑ I ∈ words,
        (∏ j : Fin (n + 1), |mom (I j)|) *
          ccr25FiniteWordPairing s L lam β I u v) ≤
        ∑ I ∈ words,
          (∏ j : Fin (n + 1), |mom (I j)|) *
            (left * right * cU ^ (n + 1) * cQ ^ n) := by
      apply Finset.sum_le_sum
      intro I hI
      exact hweighted I hI
    _ = left * right * cU ^ (n + 1) * cQ ^ n *
          ∑ I ∈ words, ∏ j : Fin (n + 1), |mom (I j)| := by
      calc
        ∑ I ∈ words,
            (∏ j : Fin (n + 1), |mom (I j)|) *
              (left * right * cU ^ (n + 1) * cQ ^ n) =
            ∑ I ∈ words,
              (left * right * cU ^ (n + 1) * cQ ^ n) *
                (∏ j : Fin (n + 1), |mom (I j)|) := by
          apply Finset.sum_congr rfl
          intro I hI
          ring
        _ = left * right * cU ^ (n + 1) * cQ ^ n *
              ∑ I ∈ words, ∏ j : Fin (n + 1), |mom (I j)| := by
          rw [Finset.mul_sum]

end

end Critical2DKPZ.MomentBounds
