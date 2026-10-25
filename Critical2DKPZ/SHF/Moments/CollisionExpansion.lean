/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.JointMoment
public import Critical2DKPZ.SHF.DeltaBose.CollisionWords
import Mathlib.Tactic

/-! # Finite collision expansions

Expanding over subsets of time-pair edges retains simultaneous collisions with their Gaussian coefficients. -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Polymer DeltaBose

/-- The replica collision potential is the sum of coincidence indicators over unordered pairs. -/
theorem replicaPotential_eq_sum_pairs {h : ℕ} (x : Fin h → Site) :
    replicaPotential x = ∑ α : CollisionPair h, if x α.val.1 = x α.val.2 then 1 else 0 := by
  classical
  change (∑ i, ∑ j, if i < j ∧ x i = x j then (1 : ℝ) else 0) = _
  rw [← Fintype.sum_prod_type (fun p : Fin h × Fin h =>
    if p.1 < p.2 ∧ x p.1 = x p.2 then (1 : ℝ) else 0)]
  simp only [ite_and]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by intro p; simp only [Finset.mem_filter, Finset.mem_univ, true_and]) _

/-- Available collision edges: every positive microscopic time and every unordered pair. -/
def collisionEdges (n h : ℕ) : Finset (ℕ × CollisionPair h) :=
  (Finset.Icc 1 n).product Finset.univ

/-- The indicator that the indicated pair occupies one site at the indicated time. -/
def edgeIndicator {n h : ℕ} (w : Fin h → Site) (s : Fin h → Fin n → Fin 4)
    (e : ℕ × CollisionPair h) : ℝ :=
  if walkPosition (w e.2.val.1) (s e.2.val.1) e.1 =
    walkPosition (w e.2.val.2) (s e.2.val.2) e.1 then 1 else 0

/-- The indicator of a prescribed collision edge is nonnegative. -/
theorem edgeIndicator_nonneg {n h : ℕ} (w : Fin h → Site)
    (s : Fin h → Fin n → Fin 4) (e : ℕ × CollisionPair h) :
    0 ≤ edgeIndicator w s e := by
  unfold edgeIndicator
  split_ifs <;> norm_num

/-- The exponential collision weight factors into one variance-weighted coincidence term for each replica pair. -/
theorem exp_potential_eq_prod_pairs (β : ℝ) {h : ℕ} (x : Fin h → Site) :
    Real.exp (β ^ 2 * replicaPotential x) =
      ∏ α : CollisionPair h,
        (1 + sigmaSq β * if x α.val.1 = x α.val.2 then 1 else 0) := by
  rw [replicaPotential_eq_sum_pairs, Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro α _
  split_ifs <;> simp only [sigmaSq, mul_one, mul_zero, Real.exp_zero, add_sub_cancel,
    add_zero]

/-- Before any resummation, the Gaussian interaction is a finite product over pair edges. -/
theorem replica_weight_eq_prod_edges (β : ℝ) (n h : ℕ) (w : Fin h → Site)
    (s : Fin h → Fin n → Fin 4) :
    Real.exp (β ^ 2 * ∑ j ∈ Finset.Icc 1 n,
      replicaPotential (fun i => walkPosition (w i) (s i) j)) =
      ∏ e ∈ collisionEdges n h, (1 + sigmaSq β * edgeIndicator w s e) := by
  rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [exp_potential_eq_prod_pairs]
  rw [collisionEdges, Finset.product_eq_sprod, Finset.prod_product (Finset.Icc 1 n) Finset.univ
    (fun e : ℕ × CollisionPair h => 1 + sigmaSq β * edgeIndicator w s e)]
  rfl

/-- Exact finite collision-subset expansion, retaining simultaneous edges at one time. -/
theorem replica_weight_collision_expansion (β : ℝ) (n h : ℕ) (w : Fin h → Site)
    (s : Fin h → Fin n → Fin 4) :
    Real.exp (β ^ 2 * ∑ j ∈ Finset.Icc 1 n,
      replicaPotential (fun i => walkPosition (w i) (s i) j)) =
      ∑ A ∈ (collisionEdges n h).powerset,
        sigmaSq β ^ A.card * ∏ e ∈ A, edgeIndicator w s e := by
  rw [replica_weight_eq_prod_edges, Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro A _
  rw [Finset.prod_mul_distrib, Finset.prod_const]

end Critical2DKPZ.SHF.Moments
