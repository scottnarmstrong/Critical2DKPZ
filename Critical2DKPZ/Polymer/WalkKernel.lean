/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.ChapmanKolmogorov
public import Critical2DKPZ.RandomWalk.KernelBridge
import Mathlib.Tactic

/-! The planar simple-walk kernel satisfies exact convolution and reflection identities. -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.Polymer

/-- Simple-walk transition kernels compose by convolution. -/
theorem srwKernel_convolution (n m : ℕ) (w z : Site) :
    srwKernel (n + m) (z - w) =
      ∑' y, srwKernel n (y - w) * srwKernel m (z - y) := by
  have h := pointToPoint_chapmanKolmogorov 0 0 n m w z (fun _ => 0)
  simpa only [pointToPoint_zero_beta] using h

/-- Permutation exchanging each step with its opposite. -/
def oppositeStep : Fin 4 ≃ Fin 4 where
  toFun i := ![1, 0, 3, 2] i
  invFun i := ![1, 0, 3, 2] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- Opposite walk directions have opposite step vectors. -/
theorem srwStep_opposite (i : Fin 4) :
    srwStep (oppositeStep i) = -srwStep i := by
  fin_cases i <;> decide

/-- Reversing every step direction negates the walk displacement. -/
theorem walkPosition_opposite {n : ℕ} (s : Fin n → Fin 4) (j : ℕ) :
    walkPosition 0 (fun i => oppositeStep (s i)) j = -walkPosition 0 s j := by
  simp only [walkPosition, srwStep_opposite, Finset.sum_neg_distrib, zero_add]

/-- The simple-walk kernel is invariant under spatial negation. -/
theorem srwKernel_neg (n : ℕ) (z : Site) :
    srwKernel n (-z) = srwKernel n z := by
  unfold srwKernel
  let e : (Fin n → Fin 4) ≃ (Fin n → Fin 4) :=
    Equiv.piCongrRight (fun _ => oppositeStep)
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro s _
  have he : e s = fun i => oppositeStep (s i) := rfl
  rw [he, walkPosition_opposite]
  simp only [neg_inj]

/-- The simple-walk kernel is unchanged when the two displacement endpoints are exchanged. -/
theorem srwKernel_sub_swap (n : ℕ) (w z : Site) :
    srwKernel n (w - z) = srwKernel n (z - w) := by
  rw [← neg_sub z w, srwKernel_neg]

/-- The overlap of two walk kernels equals the walk kernel at the sum of their times. -/
theorem srwKernel_collision (n : ℕ) (w v : Site) :
    (∑' z, srwKernel n (z - w) * srwKernel n (z - v)) =
      srwKernel (2 * n) (v - w) := by
  rw [two_mul, srwKernel_convolution]
  apply tsum_congr
  intro z
  rw [srwKernel_sub_swap n v z]

/-- Removing the first step gives the shifted remaining walk position. -/
theorem walkPosition_cons_succ {n : ℕ} (w : Site) (i : Fin 4)
    (s : Fin n → Fin 4) (j : ℕ) :
    walkPosition w (Fin.cons i s) (j + 1) =
      walkPosition (w + srwStep i) s j := by
  rw [walkPosition_eq_sum_ite, Fin.sum_univ_succ, walkPosition_eq_sum_ite]
  simp only [Fin.val_zero, Nat.succ_pos, ite_true, Fin.cons_zero,
    Fin.val_succ, Nat.add_lt_add_iff_right, Fin.cons_succ, add_assoc]

/-- The position after the first step equals the starting site plus that step. -/
theorem walkPosition_cons_one {n : ℕ} (w : Site) (i : Fin 4) (s : Fin n → Fin 4) :
    walkPosition w (Fin.cons i s) 1 = w + srwStep i := by
  have h := walkPosition_cons_succ w i s 0
  simpa only [Nat.zero_add, walkPosition_zero] using h

/-- A path weight factors into its first-site factor and the remaining path weight. -/
theorem pathWeight_cons (β : ℝ) (a : ℕ) (w : Site) {n : ℕ}
    (i : Fin 4) (s : Fin n → Fin 4) (ω : Disorder) :
    pathWeight β a w (Fin.cons i s) ω =
      Real.exp (β * ω (a + 1, w + srwStep i) - β ^ 2 / 2) *
        pathWeight β (a + 1) (w + srwStep i) s ω := by
  unfold pathWeight
  have hsum (f : ℕ → ℝ) : (∑ j ∈ Finset.Icc 1 (n + 1), f j) =
      f 1 + ∑ j ∈ Finset.Icc 1 n, f (j + 1) := by
    have h := sum_Icc_split 1 n f
    simpa only [Finset.Icc_self, Finset.sum_singleton, Nat.add_comm] using h
  rw [hsum]
  simp only [walkPosition_cons_one]
  rw [Real.exp_add]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [walkPosition_cons_succ, show a + (j + 1) = a + 1 + j by omega]

/-- The point-to-plane partition function satisfies its one-step recursion. -/
theorem pointToPlane_succ (β : ℝ) (a n : ℕ) (w : Site) (ω : Disorder) :
    pointToPlane β a (n + 1) w ω =
      ∑ i : Fin 4, (4 : ℝ)⁻¹ *
        Real.exp (β * ω (a + 1, w + srwStep i) - β ^ 2 / 2) *
        pointToPlane β (a + 1) n (w + srwStep i) ω := by
  rw [pointToPlane_eq_sum,
    ← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 4)).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ s : Fin n → Fin 4,
    (4 : ℝ)⁻¹ ^ (n + 1) * pathWeight β a w (Fin.cons i s) ω) = _
  rw [pointToPlane_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [pathWeight_cons, pow_succ]
  ring

/-- The terminal-profile partition function satisfies its one-step recursion. -/
theorem terminalProfile_succ (β : ℝ) (a n : ℕ) (w : Site)
    (f : Site → ℝ) (ω : Disorder) :
    (∑' z, pointToPoint β a (n + 1) w z ω * f z) =
      ∑ i : Fin 4, (4 : ℝ)⁻¹ *
        Real.exp (β * ω (a + 1, w + srwStep i) - β ^ 2 / 2) *
        ∑' z, pointToPoint β (a + 1) n (w + srwStep i) z ω * f z := by
  simp_rw [tsum_pointToPoint_mul]
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 4)).sum_comp,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ (n + 1) *
    pathWeight β a w (Fin.cons i s) ω * f (walkPosition w (Fin.cons i s) (n + 1))) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [pathWeight_cons, walkPosition_cons_succ, pow_succ]
  ring


end Critical2DKPZ.Polymer
