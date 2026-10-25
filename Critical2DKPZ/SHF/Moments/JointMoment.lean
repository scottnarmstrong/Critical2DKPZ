/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.Replica
public import Critical2DKPZ.Polymer.Endpoints
import Mathlib.Tactic

/-!
# Joint moments of finitely many polymer kernels

The replica formula is valid at every finite order, with arbitrary deterministic endpoint
tests. Probability factors are those of independent simple walks, including both parity classes
at their respective microscopic times. No limiting or non-collision assumption is made.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Polymer

/-- A product of terminal polymer profiles expands as a finite sum over replica walk paths. -/
theorem prod_terminalProfile_eq_sum (β : ℝ) (a n h : ℕ)
    (w : Fin h → Site) (f : Fin h → Site → ℝ) (ω : Disorder) :
    (∏ i, ∑' z, pointToPoint β a n (w i) z ω * f i z) =
      ∑ s : Fin h → Fin n → Fin 4,
        ((4 : ℝ)⁻¹ ^ n) ^ h * (∏ i, pathWeight β a (w i) (s i) ω) *
          ∏ i, f i (walkPosition (w i) (s i) n) := by
  simp_rw [tsum_pointToPoint_mul]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]


/-- The exact tested joint replica identity at every finite order. -/
theorem terminalProfile_replica (β : ℝ) (a n h : ℕ)
    (w : Fin h → Site) (f : Fin h → Site → ℝ) :
    (∫ ω, ∏ i, ∑' z, pointToPoint β a n (w i) z ω * f i z ∂disorderLaw) =
      ∑ s : Fin h → Fin n → Fin 4,
        ((4 : ℝ)⁻¹ ^ n) ^ h *
          Real.exp (β ^ 2 * ∑ j ∈ Finset.Icc 1 n,
            replicaPotential (fun i => walkPosition (w i) (s i) j)) *
          ∏ i, f i (walkPosition (w i) (s i) n) := by
  simp_rw [prod_terminalProfile_eq_sum]
  rw [integral_finsetSum _ fun s _ =>
    ((integrable_prod_pathWeight β a n h w s).const_mul _).mul_const _]
  simp_rw [integral_mul_const, integral_const_mul, integral_prod_pathWeight]

/-- Point-to-point joint moments: the Gaussian replica formula in the endpoint convention. -/
theorem pointToPoint_replica (β : ℝ) (a n h : ℕ) (w z : Fin h → Site) :
    (∫ ω, ∏ i, pointToPoint β a n (w i) (z i) ω ∂disorderLaw) =
      ∑ s : Fin h → Fin n → Fin 4,
        ((4 : ℝ)⁻¹ ^ n) ^ h *
          Real.exp (β ^ 2 * ∑ j ∈ Finset.Icc 1 n,
            replicaPotential (fun i => walkPosition (w i) (s i) j)) *
          ∏ i, if walkPosition (w i) (s i) n = z i then 1 else 0 := by
  have hh := terminalProfile_replica β a n h w
    (fun i v => if v = z i then 1 else 0)
  simpa only [mul_ite, mul_one, mul_zero, tsum_ite_eq] using hh


end Critical2DKPZ.SHF.Moments
