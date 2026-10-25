/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonFourthRunTail
import Mathlib.Tactic

/-! # Finite fourth-moment operator bounds and their word consequences -/

@[expose] public noncomputable section

open Critical2DKPZ.MomentBounds
open scoped BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- The deterministic finite operator estimates used in the CCR remainder.
The weight and each numerical bound remain explicit fields. -/
structure FourthWordOperatorBounds (s : Finset (LatticeConfiguration 4)) (L : ℕ) (β : ℝ)
    (u v : ReplicaPartition 4 → LatticeConfiguration 4 → ℝ) where
  weight : LatticeConfiguration 4 → ℝ
  weight_pos : ∀ x ∈ s, 0 < weight x
  interactionCost : ℝ
  freeCost : ℝ
  leftCost : ℝ
  rightCost : ℝ
  interactionCost_nonneg : 0 ≤ interactionCost
  freeCost_nonneg : 0 ≤ freeCost
  leftCost_nonneg : 0 ≤ leftCost
  rightCost_nonneg : 0 ≤ rightCost
  left_bound : ∀ I, I ≠ ⊥ → finiteLpNorm s 2 (fun x => u I x / weight x) ≤ leftCost
  right_bound : ∀ I, I ≠ ⊥ → finiteLpNorm s 2 (fun x => weight x * v I x) ≤ rightCost
  interaction_bound : ∀ I, I ≠ ⊥ → ∀ f : LatticeConfiguration 4 → ℝ,
    finiteLpNorm s 2 (finiteKernelApply s
      (weightedKernel weight (ccr25LabelKernel L 0 β (.interacting I))) f) ≤
        interactionCost * finiteLpNorm s 2 f
  free_bound : ∀ I J, I ≠ ⊥ → J ≠ ⊥ → I ≠ J → ∀ f : LatticeConfiguration 4 → ℝ,
    finiteLpNorm s 2 (finiteKernelApply s
      (weightedKernel weight (ccr25LabelKernel L 0 β (.free I J))) f) ≤
        freeCost * finiteLpNorm s 2 f
  left_nonneg : ∀ I x, 0 ≤ u I x
  right_nonneg : ∀ I x, 0 ≤ v I x

/-- Each admissible word is bounded by the product of its boundary costs and
its individual free and interacting operator costs. -/
theorem FourthWordOperatorBounds.word_le
    {s : Finset (LatticeConfiguration 4)} {L : ℕ} {β : ℝ}
    {u v : ReplicaPartition 4 → LatticeConfiguration 4 → ℝ}
    (b : FourthWordOperatorBounds s L β u v) {n : ℕ}
    (I : Fin (n + 1) → ReplicaPartition 4) (hI : ccr25AdmissibleWord I) :
    ccr25FiniteWordPairing s L 0 β I u v ≤
      b.leftCost * b.rightCost * b.interactionCost ^ (n + 1) * b.freeCost ^ n := by
  let K : CCR25OperatorLabel 4 → LatticeConfiguration 4 → LatticeConfiguration 4 → ℝ :=
    ccr25LabelKernel L 0 β
  let c : CCR25OperatorLabel 4 → ℝ := ccr25LabelCost b.interactionCost b.freeCost
  have hvalid : ∀ a ∈ ccr25PartitionWordLabels n I, ccr25LabelValid a :=
    ccr25PartitionWordLabels_valid I hI.1 hI.2.1
  have hc (a : CCR25OperatorLabel 4) : 0 ≤ c a := by
    cases a with
    | interacting J => exact b.interactionCost_nonneg
    | free J J' => exact b.freeCost_nonneg
  have hfactor : ∀ a ∈ ccr25PartitionWordLabels n I, ∀ f,
      finiteLpNorm s 2 (finiteKernelApply s (weightedKernel b.weight (K a)) f) ≤
        c a * finiteLpNorm s 2 f := by
    intro a ha f
    cases a with
    | interacting J => exact b.interaction_bound J (hvalid _ ha) f
    | free J J' =>
      obtain ⟨hJ, hJ', hne⟩ := hvalid (.free J J') ha
      exact b.free_bound J J' hJ hJ' hne f
  have hpair := finite_weighted_taggedKernelWord_pairing_le s Real.HolderConjugate.two_two
    b.weight b.weight_pos (ccr25PartitionWordLabels n I) K c hc hfactor
    (u (I 0)) (v (I (Fin.last n)))
  have hprod : 0 ≤ ((ccr25PartitionWordLabels n I).map c).prod :=
    List.prod_nonneg (by intro a ha; obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha; exact hc j)
  calc
    _ ≤ finiteLpNorm s 2 (fun x => u (I 0) x / b.weight x) *
        ((ccr25PartitionWordLabels n I).map c).prod *
        finiteLpNorm s 2 (fun x => b.weight x * v (I (Fin.last n)) x) := by
      simpa only [ccr25FiniteWordPairing, finiteTaggedKernelWordApply, K] using hpair
    _ ≤ b.leftCost * ((ccr25PartitionWordLabels n I).map c).prod * b.rightCost := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (b.left_bound _ (hI.1 0)) hprod)
        (b.right_bound _ (hI.1 _)) (finiteLpNorm_nonneg _ _ _)
        (mul_nonneg b.leftCost_nonneg hprod)
    _ = _ := by
      rw [show ((ccr25PartitionWordLabels n I).map c).prod =
        b.interactionCost ^ (n + 1) * b.freeCost ^ n from
          ccr25PartitionWordLabels_cost_prod _ _ I]
      ring

/-- The bundled bounds instantiate the Gaussian full-support run estimate. -/
theorem FourthWordOperatorBounds.run_le
    {s : Finset (LatticeConfiguration 4)} {L : ℕ} {β : ℝ}
    {u v : ReplicaPartition 4 → LatticeConfiguration 4 → ℝ}
    (b : FourthWordOperatorBounds s L β u v) (hσ : Polymer.sigmaSq β ≤ 1) (n : ℕ) :
    ccr25GaussianFiniteWordRun s L 0 β u v n ≤
      b.leftCost * b.rightCost *
        (ccr25GaussianFiniteWordOperatorScale 4 b.interactionCost) ^ (n + 1) * b.freeCost ^ n *
        Real.sqrt (Polymer.sigmaSq β) ^ Nat.max (2 * (n + 1)) 4 :=
  ccr25GaussianFiniteWordRun_le s L 0 β b.weight b.weight_pos Real.HolderConjugate.two_two
    u v b.interactionCost b.freeCost b.leftCost b.rightCost
    b.interactionCost_nonneg b.freeCost_nonneg b.leftCost_nonneg b.rightCost_nonneg
    b.left_bound b.right_bound b.interaction_bound b.free_bound hσ

/-- Full support gives the one-run fourth contribution two variance powers. -/
theorem FourthWordOperatorBounds.first_run_le
    {s : Finset (LatticeConfiguration 4)} {L : ℕ} {β : ℝ}
    {u v : ReplicaPartition 4 → LatticeConfiguration 4 → ℝ}
    (b : FourthWordOperatorBounds s L β u v) (hσ : Polymer.sigmaSq β ≤ 1) :
    ccr25GaussianFiniteWordRun s L 0 β u v 0 ≤
      b.leftCost * b.rightCost * ccr25GaussianFiniteWordOperatorScale 4 b.interactionCost *
        Polymer.sigmaSq β ^ 2 := by
  have h := b.run_le hσ 0
  have hpow : Real.sqrt (Polymer.sigmaSq β) ^ 4 = Polymer.sigmaSq β ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt (sigmaSq_nonneg β)]
  simpa only [Nat.zero_add, Nat.mul_one, show Nat.max 2 4 = 4 by decide,
    pow_one, pow_zero, mul_one, hpow] using h

/-- The same actual norm bundle controls the complete at-least-three-run tail. -/
theorem FourthWordOperatorBounds.tail_summable_le
    {s : Finset (LatticeConfiguration 4)} {L : ℕ} {β : ℝ}
    {u v : ReplicaPartition 4 → LatticeConfiguration 4 → ℝ}
    (b : FourthWordOperatorBounds s L β u v) (hσ : Polymer.sigmaSq β ≤ 1)
    (hsmall : (ccr25GaussianFiniteWordOperatorScale 4 b.interactionCost * Polymer.sigmaSq β) *
      b.freeCost < 1) :
    Summable (fun n => ccr25GaussianFiniteWordRun s L 0 β u v (n + 2)) ∧
      (∑' n, ccr25GaussianFiniteWordRun s L 0 β u v (n + 2)) ≤
        b.leftCost * b.rightCost * (ccr25GaussianFiniteWordOperatorScale 4 b.interactionCost) ^ 3 *
          b.freeCost ^ 2 * Polymer.sigmaSq β ^ 3 /
            (1 - (ccr25GaussianFiniteWordOperatorScale 4 b.interactionCost * Polymer.sigmaSq β) * b.freeCost) :=
  summable_fourth_word_run_tail s L 0 β b.weight b.weight_pos Real.HolderConjugate.two_two
    u v b.interactionCost b.freeCost b.leftCost b.rightCost
    b.interactionCost_nonneg b.freeCost_nonneg b.leftCost_nonneg b.rightCost_nonneg
    b.left_bound b.right_bound b.interaction_bound b.free_bound b.left_nonneg b.right_nonneg hσ hsmall

end Critical2DKPZ.Extensions.GffTangent
