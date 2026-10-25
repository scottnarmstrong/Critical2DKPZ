/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.Moments
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic

/-! Finite polymer path weights expand as square-free products of centered independent Gaussian disorder factors. -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.Polymer

/-- The centered single-site disorder factor is `exp(β ωᵢ - β²/2) - 1`. -/
def xi (β : ℝ) (i : ℕ × Site) (ω : Disorder) : ℝ :=
  Real.exp (β * ω i - β ^ 2 / 2) - 1

/-- Variance of one centered disorder coordinate. -/
def sigmaSq (β : ℝ) : ℝ := Real.exp (β ^ 2) - 1

/-- The centered disorder factor is measurable. -/
theorem measurable_xi (β : ℝ) (i : ℕ × Site) : Measurable (xi β i) := by
  unfold xi
  fun_prop

/-- The centered single-site disorder factor belongs to Lᵖ for every finite exponent. -/
theorem memLp_xi (β : ℝ) (i : ℕ × Site) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (xi β i) p disorderLaw := by
  have h := memLp_finiteExp (fun _ : Fin 1 => i)
    (fun _ _ _ => Subsingleton.elim _ _) (fun _ => β) (-(β ^ 2 / 2)) p hp
  have heq : finiteExp (fun _ : Fin 1 => i) (fun _ => β) (-(β ^ 2 / 2)) =
      fun ω => Real.exp (β * ω i - β ^ 2 / 2) := by
    funext ω
    simp only [finiteExp, Fin.sum_univ_one, sub_eq_add_neg]
  rw [heq] at h
  exact h.sub (memLp_const 1)

/-- The centered disorder factor has expectation zero. -/
theorem integral_xi (β : ℝ) (i : ℕ × Site) :
    ∫ ω, xi β i ω ∂disorderLaw = 0 := by
  have h : Integrable (fun ω : Disorder => Real.exp (β * ω i))
      disorderLaw := Integrable.of_integral_ne_zero (by
        rw [integral_exp_coordinate]
        exact Real.exp_ne_zero _)
  have heq : xi β i = fun ω =>
      Real.exp (β * ω i) * Real.exp (-(β ^ 2 / 2)) - 1 := by
    funext ω
    simp only [xi, sub_eq_add_neg, Real.exp_add]
  rw [heq, integral_sub (h.mul_const _) (integrable_const 1),
    integral_mul_const, integral_exp_coordinate]
  simp only [integral_const, probReal_univ, one_smul]
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, sub_self]

/-- The second moment of the centered disorder factor equals the disorder variance. -/
theorem integral_xi_sq (β : ℝ) (i : ℕ × Site) :
    ∫ ω, xi β i ω ^ 2 ∂disorderLaw = sigmaSq β := by
  have h1 : Integrable (fun ω : Disorder => Real.exp (β * ω i))
      disorderLaw :=
    Integrable.of_integral_ne_zero (by
      rw [integral_exp_coordinate]
      exact Real.exp_ne_zero _)
  have h2 : Integrable (fun ω : Disorder => Real.exp ((2 * β) * ω i))
      disorderLaw :=
    Integrable.of_integral_ne_zero (by
      rw [integral_exp_coordinate]
      exact Real.exp_ne_zero _)
  have heq (ω : Disorder) :
      xi β i ω ^ 2 =
        Real.exp ((2 * β) * ω i) * Real.exp (-(β ^ 2)) -
        2 * (Real.exp (β * ω i) * Real.exp (-(β ^ 2 / 2))) + 1 := by
    unfold xi
    simp only [sub_eq_add_neg, Real.exp_add]
    have hh : Real.exp ((2 * β) * ω i) * Real.exp (-(β ^ 2)) =
        (Real.exp (β * ω i) * Real.exp (-(β ^ 2 / 2))) ^ 2 := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      ring
    rw [hh]
    ring
  simp_rw [heq]
  rw [integral_add (f := fun ω : Disorder =>
      Real.exp ((2 * β) * ω i) * Real.exp (-(β ^ 2)) -
      2 * (Real.exp (β * ω i) * Real.exp (-(β ^ 2 / 2))))
      (g := fun _ => (1 : ℝ))
      ((h2.mul_const _).sub ((h1.mul_const _).const_mul _)) (integrable_const 1),
    integral_sub (h2.mul_const _) ((h1.mul_const _).const_mul _),
    integral_const_mul, integral_mul_const, integral_mul_const,
    integral_exp_coordinate, integral_exp_coordinate]
  simp only [integral_const, probReal_univ, one_smul]
  rw [← Real.exp_add, ← Real.exp_add]
  have htwo : (2 * β) ^ 2 / 2 + -(β ^ 2) = β ^ 2 := by ring
  rw [htwo, add_neg_cancel, Real.exp_zero]
  unfold sigmaSq
  ring

/-- A square-free chaos monomial, with each space-time coordinate used once. -/
def chaosMonomial (β : ℝ) (A : Finset (ℕ × Site)) (ω : Disorder) : ℝ :=
  ∏ i ∈ A, xi β i ω


/-- The expectation of a finite coordinate product factors over its independent coordinates. -/
theorem integral_coordinateProduct (A : Finset (ℕ × Site))
    (f : (ℕ × Site) → ℝ → ℝ) (hf : ∀ i, Measurable (f i)) :
    ∫ ω : Disorder, (∏ i ∈ A, f i (ω i)) ∂disorderLaw =
      ∏ i ∈ A, ∫ ω : Disorder, f i (ω i) ∂disorderLaw := by
  have hi := iIndepFun.precomp (g := fun i : A => i.val)
    Subtype.val_injective coordinates_independent
  have hh := hi.comp (fun i => f i.val) (fun i => hf i.val)
  have h := hh.integral_fun_prod_eq_prod_integral (fun i =>
    ((hf i.val).comp (measurable_pi_apply i.val)).aestronglyMeasurable)
  calc
    _ = ∫ ω : Disorder, ∏ i : A, f i.val (ω i.val) ∂disorderLaw := by
      congr 1
      funext ω
      exact (Finset.prod_coe_sort A (fun i => f i (ω i))).symm
    _ = ∏ i : A, ∫ ω : Disorder, f i.val (ω i.val) ∂disorderLaw := h
    _ = _ := Finset.prod_coe_sort A (fun i => ∫ ω : Disorder, f i (ω i) ∂disorderLaw)


/-- A path weight has the finite chaos expansion over its visited coordinates. -/
theorem pathWeight_chaos (β : ℝ) (a : ℕ) (w : Site) {n : ℕ}
    (s : Fin n → Fin 4) (ω : Disorder) :
    pathWeight β a w s ω =
      ∑ A ∈ (Finset.Icc 1 n).powerset,
        ∏ j ∈ A, xi β (a + j, walkPosition w s j) ω := by
  rw [← Finset.prod_one_add]
  simp only [xi, add_sub_cancel]
  exact Real.exp_sum _ _

/-- The point-to-plane partition function has its finite chaos expansion. -/
theorem pointToPlane_chaos (β : ℝ) (a n : ℕ) (w : Site) (ω : Disorder) :
    pointToPlane β a n w ω =
      ∑ A ∈ (Finset.Icc 1 n).powerset,
        ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n *
          ∏ j ∈ A, xi β (a + j, walkPosition w s j) ω := by
  rw [pointToPlane_eq_sum]
  simp_rw [pathWeight_chaos, Finset.mul_sum]
  exact Finset.sum_comm

/-- The point-to-point partition function has its finite constrained chaos expansion. -/
theorem pointToPoint_chaos (β : ℝ) (a n : ℕ) (w z : Site) (ω : Disorder) :
    pointToPoint β a n w z ω =
      ∑ A ∈ (Finset.Icc 1 n).powerset,
        ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n *
          (∏ j ∈ A, xi β (a + j, walkPosition w s j) ω) *
          if walkPosition w s n = z then 1 else 0 := by
  rw [pointToPoint_eq_sum]
  simp_rw [pathWeight_chaos, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

end Critical2DKPZ.Polymer
