/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.Chaos
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

/-! # Exact orthogonality of square-free Gaussian polymer chaos monomials -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.Polymer

/-- Two functions with finite L²ᵖ norms have a product with finite Lᵖ norm. -/
theorem memLp_mul_double {f g : Disorder → ℝ} (p : ℝ≥0∞)
    (hf : MemLp f (2 * p) disorderLaw) (hg : MemLp g (2 * p) disorderLaw) :
    MemLp (fun ω => f ω * g ω) p disorderLaw := by
  have : ENNReal.HolderTriple (2 * p) (2 * p) p := by
    constructor
    rw [ENNReal.mul_inv (by left; norm_num) (by left; norm_num),
      ← add_mul]
    have htwo : (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = 1 :=
      ENNReal.HolderConjugate.inv_add_inv_eq_one 2 2
    rw [htwo, one_mul]
  exact hf.fun_mul hg

/-- Every square-free chaos monomial belongs to Lᵖ for every finite exponent. -/
theorem memLp_chaosMonomial (β : ℝ) (A : Finset (ℕ × Site))
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (chaosMonomial β A) p disorderLaw := by
  induction A using Finset.induction_on generalizing p with
  | empty =>
    change MemLp (fun _ : Disorder => (1 : ℝ)) p disorderLaw
    exact memLp_const 1
  | @insert i A hi ih =>
    have hp2 : 2 * p ≠ ∞ := ENNReal.mul_ne_top (by norm_num) hp
    have heq : chaosMonomial β (insert i A) =
        fun ω => xi β i ω * chaosMonomial β A ω := by
      funext ω
      exact Finset.prod_insert hi
    rw [heq]
    exact memLp_mul_double p (memLp_xi β i (2 * p) hp2) (ih (2 * p) hp2)

/-- A product of chaos monomials factors over the union of their coordinate sets, retaining repeated factors. -/
theorem chaosMonomial_mul_eq_union (β : ℝ) (A B : Finset (ℕ × Site))
    (ω : Disorder) :
    chaosMonomial β A ω * chaosMonomial β B ω =
      ∏ i ∈ A ∪ B, ((if i ∈ A then xi β i ω else 1) *
        (if i ∈ B then xi β i ω else 1)) := by
  rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.prod_ite_mem]
  simp only [Finset.union_inter_distrib_right, Finset.inter_self,
    Finset.union_eq_left.2 Finset.inter_subset_right,
    Finset.union_eq_right.2 Finset.inter_subset_right, chaosMonomial]

/-- Distinct square-free chaos monomials are orthogonal, and the second moment of the monomial on `A` is `(σ²)^|A|`. -/
theorem integral_chaosMonomial_mul (β : ℝ) (A B : Finset (ℕ × Site)) :
    ∫ ω, chaosMonomial β A ω * chaosMonomial β B ω ∂disorderLaw =
      if A = B then sigmaSq β ^ A.card else 0 := by
  simp_rw [chaosMonomial_mul_eq_union]
  let f : (ℕ × Site) → ℝ → ℝ := fun i x =>
    (if i ∈ A then Real.exp (β * x - β ^ 2 / 2) - 1 else 1) *
    (if i ∈ B then Real.exp (β * x - β ^ 2 / 2) - 1 else 1)
  have hf : ∀ i, Measurable (f i) := by
    intro i
    dsimp only [f]
    split_ifs <;> fun_prop
  change (∫ ω : Disorder, ∏ i ∈ A ∪ B, f i (ω i) ∂disorderLaw) = _
  rw [integral_coordinateProduct (A ∪ B) f hf]
  have hint (i : ℕ × Site) (hi : i ∈ A ∪ B) :
      (∫ ω : Disorder, f i (ω i) ∂disorderLaw) =
        if i ∈ A ∩ B then sigmaSq β else 0 := by
    by_cases hA : i ∈ A <;> by_cases hB : i ∈ B
    · simp only [f, hA, hB, ite_true, Finset.mem_inter, and_self]
      change (∫ ω : Disorder, xi β i ω * xi β i ω ∂disorderLaw) = sigmaSq β
      simp only [← pow_two, integral_xi_sq]
    · simp only [f, hA, hB, ite_true, ite_false, mul_one, Finset.mem_inter, and_false]
      exact integral_xi β i
    · simp only [f, hA, hB, ite_true, ite_false, one_mul, Finset.mem_inter, false_and]
      exact integral_xi β i
    · exact False.elim ((Finset.mem_union.1 hi).elim hA hB)
  rw [Finset.prod_congr rfl hint]
  by_cases hAB : A = B
  · subst B
    simp only [Finset.union_self, Finset.inter_self, ite_true]
    rw [Finset.prod_congr rfl (fun i hi => ite_eq_left hi), Finset.prod_const]
  · rw [ite_eq_right hAB]
    have hex : ∃ i ∈ A ∪ B, i ∉ A ∩ B := by
      by_contra h
      push Not at h
      apply hAB
      apply Finset.ext
      intro i
      constructor
      · intro hi
        exact (Finset.mem_inter.1 (h i (Finset.mem_union_left B hi))).2
      · intro hi
        exact (Finset.mem_inter.1 (h i (Finset.mem_union_right A hi))).1
    obtain ⟨i, hi, hnot⟩ := hex
    exact Finset.prod_eq_zero hi (ite_eq_right hnot)


end Critical2DKPZ.Polymer
