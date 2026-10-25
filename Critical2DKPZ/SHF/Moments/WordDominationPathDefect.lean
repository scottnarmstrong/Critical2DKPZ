/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationPairSelections
public import Critical2DKPZ.SHF.Moments.WordDominationLocalPairPart
import Mathlib.Tactic

/-! # The non-pair remainder as a chronological local-potential defect -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Polymer DeltaBose

attribute [local instance] Classical.propDecidable

/-- The free and single-pair part of one microscopic Gaussian interaction. -/
def collisionWordLocalPairPotential (β : ℝ) {h : ℕ} (x : Fin h → Site) : ℝ :=
  1 + sigmaSq β * ∑ α : CollisionPair h,
    if x α.1.1 = x α.1.2 then (1 : ℝ) else 0

private theorem collisionWord_prod_fin_positive_eq_prod_Icc (n : ℕ) (f : ℕ → ℝ) :
    (∏ j : Fin n, f (j.val + 1)) = ∏ t ∈ Finset.Icc 1 n, f t := by
  apply Finset.prod_bij (fun j hj => j.val + 1)
  · intro j hj
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i hi j hj he
    exact Fin.ext (by omega)
  · intro t ht
    have ht' := Finset.mem_Icc.mp ht
    refine ⟨⟨t - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    change t - 1 + 1 = t
    omega
  · intro j hj
    rfl

/-- Exact chronological form of the pair-simple collision expansion. At
each positive time, either no pair or one pair is selected. -/
theorem pairSimple_collisionExpansion_eq_pathPairPotential
    (β : ℝ) (n h : ℕ) (x y : Fin h → Site) :
    (∑ A ∈ (collisionEdges n h).powerset.filter IsPairSimple,
      sigmaSq β ^ A.card * collisionSubsetCoefficient n h A x y) =
      ∑ s : Fin h → Fin n → Fin 4,
        ((4 : ℝ)⁻¹ ^ n) ^ h *
          (∏ j : Fin n, collisionWordLocalPairPotential β
            (fun i => walkPosition (x i) (s i) (j.val + 1))) *
          ∏ i, if walkPosition (x i) (s i) n = y i then (1 : ℝ) else 0 := by
  classical
  have hterm (A : Finset (ℕ × CollisionPair h)) :
      sigmaSq β ^ A.card * collisionSubsetCoefficient n h A x y =
        ∑ s : Fin h → Fin n → Fin 4,
          ((4 : ℝ)⁻¹ ^ n) ^ h * (∏ e ∈ A, sigmaSq β * edgeIndicator x s e) *
            ∏ i, if walkPosition (x i) (s i) n = y i then (1 : ℝ) else 0 := by
    unfold collisionSubsetCoefficient
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    ring
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  have hchoices := sum_pairSimple_edge_products_eq_prod_one_add_sum n h
    (fun e => sigmaSq β * edgeIndicator x s e)
  have hchoices' :
      (∑ A ∈ (collisionEdges n h).powerset.filter IsPairSimple,
        ∏ e ∈ A, sigmaSq β * edgeIndicator x s e) =
        ∏ j : Fin n, collisionWordLocalPairPotential β
          (fun i => walkPosition (x i) (s i) (j.val + 1)) := by
    simpa only [collisionWordLocalPairPotential, Finset.mul_sum, edgeIndicator] using hchoices
  calc
    _ = ((4 : ℝ)⁻¹ ^ n) ^ h *
        (∑ A ∈ (collisionEdges n h).powerset.filter IsPairSimple,
          ∏ e ∈ A, sigmaSq β * edgeIndicator x s e) *
          ∏ i, if walkPosition (x i) (s i) n = y i then (1 : ℝ) else 0 := by
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ = _ := by rw [hchoices']

/-- The exact non-pair remainder is the difference between the product of
full local Gaussian potentials and the product allowing at most one pair at
each time. The terminal microscopic slice is included in both products. -/
theorem nonpairCollisionRemainder_eq_pathDefect (β : ℝ) (n h : ℕ)
    (x y : Fin h → Site) :
    nonpairCollisionRemainder β n h x y =
      ∑ s : Fin h → Fin n → Fin 4, ((4 : ℝ)⁻¹ ^ n) ^ h *
        ((∏ j : Fin n, Real.exp (β ^ 2 * replicaPotential
            (fun i => walkPosition (x i) (s i) (j.val + 1)))) -
          (∏ j : Fin n, collisionWordLocalPairPotential β
            (fun i => walkPosition (x i) (s i) (j.val + 1)))) *
        ∏ i, if walkPosition (x i) (s i) n = y i then (1 : ℝ) else 0 := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not
    ((collisionEdges n h).powerset) IsPairSimple
    (f := fun A => sigmaSq β ^ A.card * collisionSubsetCoefficient n h A x y)
  have hfull := pointToPoint_collision_expansion β 0 n h x y
  have hrep := pointToPoint_replica β 0 n h x y
  have hexp (s : Fin h → Fin n → Fin 4) :
      Real.exp (β ^ 2 * ∑ t ∈ Finset.Icc 1 n,
        replicaPotential (fun i => walkPosition (x i) (s i) t)) =
      ∏ j : Fin n, Real.exp (β ^ 2 * replicaPotential
        (fun i => walkPosition (x i) (s i) (j.val + 1))) := by
    rw [Finset.mul_sum, Real.exp_sum,
      ← collisionWord_prod_fin_positive_eq_prod_Icc]
  have hfullPath :
      (∑ A ∈ (collisionEdges n h).powerset,
        sigmaSq β ^ A.card * collisionSubsetCoefficient n h A x y) =
      ∑ s : Fin h → Fin n → Fin 4, ((4 : ℝ)⁻¹ ^ n) ^ h *
        (∏ j : Fin n, Real.exp (β ^ 2 * replicaPotential
          (fun i => walkPosition (x i) (s i) (j.val + 1)))) *
        ∏ i, if walkPosition (x i) (s i) n = y i then (1 : ℝ) else 0 := by
    rw [← hfull, hrep]
    simp_rw [hexp]
  have hdefect : nonpairCollisionRemainder β n h x y =
      (∑ A ∈ (collisionEdges n h).powerset,
        sigmaSq β ^ A.card * collisionSubsetCoefficient n h A x y) -
      (∑ A ∈ (collisionEdges n h).powerset.filter IsPairSimple,
        sigmaSq β ^ A.card * collisionSubsetCoefficient n h A x y) := by
    change (∑ A ∈ (collisionEdges n h).powerset.filter (fun A => ¬ IsPairSimple A),
      sigmaSq β ^ A.card * collisionSubsetCoefficient n h A x y) = _
    linarith only [hsplit]
  rw [hdefect, hfullPath, pairSimple_collisionExpansion_eq_pathPairPotential,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  ring

end Critical2DKPZ.SHF.Moments

end
