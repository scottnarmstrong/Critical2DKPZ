/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.Replica
public import Critical2DKPZ.Blocks.PredictableNoise
import Mathlib.Tactic

/-! # The one-time active-label expansion of Gaussian replica interactions -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.SHF.Moments

open Polymer

/-- The centered-disorder product for the labels active at one time. -/
def collisionWordLocalVertexProduct (β : ℝ) {h : ℕ} (x : Fin h → Site)
    (A : Finset (Fin h)) (ω : Disorder) : ℝ :=
  ∏ i ∈ A, xi β (0, x i) ω

/-- Every local active-label product has all finite moments, including when
several labels occupy the same disorder coordinate. -/
theorem memLp_collisionWordLocalVertexProduct (β : ℝ) {h : ℕ} (x : Fin h → Site)
    (A : Finset (Fin h)) :
    ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp (collisionWordLocalVertexProduct β x A) p disorderLaw := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      intro p hp
      change MemLp (fun _ : Disorder => (1 : ℝ)) p disorderLaw
      exact memLp_const 1
  | @insert i A hi ih =>
      intro p hp
      have hp2 : 2 * p ≠ ∞ := ENNReal.mul_ne_top (by norm_num) hp
      have heq : collisionWordLocalVertexProduct β x (insert i A) =
          fun ω => xi β (0, x i) ω * collisionWordLocalVertexProduct β x A ω := by
        funext ω
        simp [collisionWordLocalVertexProduct, hi]
      rw [heq]
      exact memLp_mul_double p (memLp_xi β (0, x i) (2 * p) hp2) (ih (2 * p) hp2)

/-- Integrability of each one-time active-label product. -/
theorem integrable_collisionWordLocalVertexProduct (β : ℝ) {h : ℕ} (x : Fin h → Site)
    (A : Finset (Fin h)) : Integrable (collisionWordLocalVertexProduct β x A) disorderLaw :=
  memLp_one_iff_integrable.mp (memLp_collisionWordLocalVertexProduct β x A 1 (by simp))

/-- The one-time centered Gaussian moment associated with an active label set. -/
def collisionWordLocalVertexMoment (β : ℝ) {h : ℕ} (x : Fin h → Site)
    (A : Finset (Fin h)) : ℝ :=
  ∫ ω, collisionWordLocalVertexProduct β x A ω ∂disorderLaw

/-- No active labels contribute the unit factor. -/
theorem collisionWordLocalVertexMoment_empty (β : ℝ) {h : ℕ} (x : Fin h → Site) :
    collisionWordLocalVertexMoment β x ∅ = 1 := by
  simp [collisionWordLocalVertexMoment, collisionWordLocalVertexProduct]

/-- One active centered coordinate contributes zero. -/
theorem collisionWordLocalVertexMoment_singleton (β : ℝ) {h : ℕ} (x : Fin h → Site)
    (i : Fin h) : collisionWordLocalVertexMoment β x {i} = 0 := by
  simpa [collisionWordLocalVertexMoment, collisionWordLocalVertexProduct] using integral_xi β (0, x i)

/-- Two distinct active labels contribute exactly the pair variance and
their collision indicator. -/
theorem collisionWordLocalVertexMoment_pair (β : ℝ) {h : ℕ} (x : Fin h → Site)
    (i j : Fin h) (hij : i ≠ j) :
    collisionWordLocalVertexMoment β x {i, j} = if x i = x j then sigmaSq β else 0 := by
  classical
  have hnot : i ∉ ({j} : Finset (Fin h)) := by simpa using hij
  unfold collisionWordLocalVertexMoment collisionWordLocalVertexProduct
  simp_rw [Finset.prod_insert hnot, Finset.prod_singleton]
  simpa only [Prod.mk.injEq, true_and] using
    Critical2DKPZ.Blocks.integral_xi_mul β (0, x i) (0, x j)

/-- Exact local expansion of the Gaussian replica potential over active
label sets. Integrability is supplied by `integrable_collisionWordLocalVertexProduct`. -/
theorem exp_replicaPotential_eq_sum_collisionWordLocalVertexMoment (β : ℝ) {h : ℕ}
    (x : Fin h → Site) :
    Real.exp (β ^ 2 * replicaPotential x) =
      ∑ A ∈ (Finset.univ : Finset (Fin h)).powerset, collisionWordLocalVertexMoment β x A := by
  classical
  have hid : (∫ ω, ∏ i : Fin h, boltzmann β (0, x i) ω ∂disorderLaw) =
      Real.exp (β ^ 2 * replicaPotential x) := by
    simpa only [collisionCount_time, replicaPotential] using
      integral_prod_boltzmann β (fun i : Fin h => (0, x i))
  have hpoint (ω : Disorder) : (∏ i : Fin h, boltzmann β (0, x i) ω) =
      ∑ A ∈ (Finset.univ : Finset (Fin h)).powerset,
        collisionWordLocalVertexProduct β x A ω := by
    calc
      _ = ∏ i : Fin h, (1 + xi β (0, x i) ω) := by
          apply Finset.prod_congr rfl
          intro i hi
          simp [boltzmann, xi]
      _ = _ := Finset.prod_one_add Finset.univ
  rw [← hid]
  simp_rw [hpoint]
  rw [integral_finsetSum _ (fun A hA => integrable_collisionWordLocalVertexProduct β x A)]
  rfl

end Critical2DKPZ.SHF.Moments

end
