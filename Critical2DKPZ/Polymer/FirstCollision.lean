/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.PairRecurrence
public import Critical2DKPZ.RandomWalk.KernelBridge
import Mathlib.Tactic

/-! Expanding each replica collision factor as `exp(β²) = 1 + σ²` and selecting the earliest nontrivial factor gives the first-collision formula. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.Polymer

/-- One free step of two independent nearest-neighbor walks. -/
def pairStep (f : Site → Site → ℝ) (w v : Site) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 4, ((4 : ℝ)⁻¹ * (4 : ℝ)⁻¹) *
    f (w + srwStep i) (v + srwStep j)

/-- The pair-transition averaging operator preserves the constant function one. -/
theorem pairStep_one (w v : Site) :
    pairStep (fun _ _ => 1) w v = 1 := by
  norm_num [pairStep, Fin.sum_univ_succ]

/-- Pair-transition averaging preserves sums of two functions. -/
theorem pairStep_add (f g : Site → Site → ℝ) (w v : Site) :
    pairStep (fun x y => f x y + g x y) w v = pairStep f w v + pairStep g w v := by
  simp only [pairStep, mul_add, Finset.sum_add_distrib]

/-- Pair-transition averaging commutes with finite sums. -/
theorem pairStep_sum {ι : Type*} (A : Finset ι) (f : ι → Site → Site → ℝ) (w v : Site) :
    pairStep (fun x y => ∑ i ∈ A, f i x y) w v =
      ∑ i ∈ A, pairStep (f i) w v := by
  simp only [pairStep, Finset.mul_sum]
  calc
    _ = ∑ i : Fin 4, ∑ k ∈ A, ∑ j : Fin 4,
        (4⁻¹ * 4⁻¹) * f k (w + srwStep i) (v + srwStep j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Averaging a displacement heat kernel over a pair step increases its time by two. -/
theorem pairStep_kernel (k : ℕ) (w v : Site) :
    pairStep (fun x y => srwKernel k (y - x)) w v =
      srwKernel (k + 2) (v - w) := by
  symm
  rw [show k + 2 = (k + 1) + 1 by omega, Critical2DKPZ.srwKernel_succ,
    Finset.sum_div]
  unfold pairStep
  apply Finset.sum_congr rfl
  intro i _
  rw [Critical2DKPZ.srwKernel_succ, Finset.sum_div, Finset.sum_div]
  rw [← oppositeStep.sum_comp (fun j : Fin 4 =>
    (srwKernel k (v - w - srwStep i - srwStep j) / 4) / 4)]
  apply Finset.sum_congr rfl
  intro j _
  rw [srwStep_opposite]
  have heq : v - w - srwStep i - -srwStep j =
      (v + srwStep j) - (w + srwStep i) := by abel
  rw [heq]
  ring

/-- The simple-walk kernel at zero time is the identity kernel. -/
theorem srwKernel_zero (z : Site) : srwKernel 0 z = if z = 0 then 1 else 0 := by
  simp only [srwKernel, walkPosition_zero, pow_zero, one_mul]
  simp only [Finset.univ_unique, Finset.sum_singleton, eq_comm]

/-- Summing pair transitions over a common endpoint gives the meeting kernel. -/
theorem pairStep_meeting (w v : Site) :
    pairStep (fun x y => if x = y then 1 else 0) w v =
      srwKernel 2 (v - w) := by
  have h := pairStep_kernel 0 w v
  simpa only [srwKernel_zero, sub_eq_zero, eq_comm, Nat.zero_add] using h

/-- The pair moment satisfies the first-collision recurrence. -/
theorem pairMoment_recurrence (β : ℝ) (n : ℕ) (w v : Site) :
    pairMoment β (n + 1) w v =
      pairStep (pairMoment β n) w v +
        sigmaSq β * srwKernel 2 (v - w) * pairMoment β n 0 0 := by
  rw [pairMoment_succ, ← pairStep_meeting]
  unfold pairStep
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  by_cases h : w + srwStep i = v + srwStep j
  · simp only [h, ite_true, mul_one]
    rw [← h, pairMoment_diagonal]
    unfold sigmaSq
    ring
  · simp only [h, ite_false, mul_zero, zero_mul, add_zero, mul_one]

/-- A sum over a nonempty integer interval splits off its first term. -/
theorem sum_Icc_first (n : ℕ) (f : ℕ → ℝ) :
    (∑ r ∈ Finset.Icc 1 (n + 1), f r) =
      f 1 + ∑ r ∈ Finset.Icc 1 n, f (r + 1) := by
  have h := sum_Icc_split 1 n f
  simpa only [Finset.Icc_self, Finset.sum_singleton, Nat.add_comm] using h

/-- The pair moment equals its expansion according to the first collision time. -/
theorem pairMoment_firstCollision (β : ℝ) (n : ℕ) (w v : Site) :
    pairMoment β n w v = 1 +
      ∑ r ∈ Finset.Icc 1 n, sigmaSq β * srwKernel (2 * r) (v - w) *
        pairMoment β (n - r) 0 0 := by
  induction n generalizing w v with
  | zero =>
    simp only [pairMoment_zero, Finset.Icc_eq_empty_of_lt (by omega : 0 < 1),
      Finset.sum_empty, add_zero]
  | succ n ih =>
    rw [pairMoment_recurrence]
    have hstep :
        pairStep (pairMoment β n) w v =
          1 + ∑ r ∈ Finset.Icc 1 n,
            sigmaSq β * srwKernel (2 * (r + 1)) (v - w) *
              pairMoment β (n - r) 0 0 := by
      have heq : pairMoment β n = fun x y => 1 +
          ∑ r ∈ Finset.Icc 1 n, sigmaSq β * srwKernel (2 * r) (y - x) *
            pairMoment β (n - r) 0 0 := by
        funext x y
        exact ih x y
      rw [heq, pairStep_add, pairStep_one, pairStep_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      have hk := pairStep_kernel (2 * r) w v
      have heqk : 2 * r + 2 = 2 * (r + 1) := by omega
      rw [heqk] at hk
      unfold pairStep at *
      calc
        _ = sigmaSq β *
          (∑ i : Fin 4, ∑ j : Fin 4, (4⁻¹ * 4⁻¹) *
            srwKernel (2 * r) ((v + srwStep j) - (w + srwStep i))) *
              pairMoment β (n - r) 0 0 := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := by rw [hk]
    rw [hstep, sum_Icc_first]
    simp only [Nat.mul_one, Nat.add_sub_cancel, Nat.add_sub_add_right]
    ring

/-- The point-to-plane product moment equals its first-collision expansion. -/
theorem pointToPlane_firstCollision (β : ℝ) (a n : ℕ) (w v : Site) :
    (∫ ω, pointToPlane β a n w ω * pointToPlane β a n v ω ∂disorderLaw) - 1 =
      ∑ r ∈ Finset.Icc 1 n, srwKernel (2 * r) (v - w) * sigmaSq β *
        (∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw) := by
  rw [integral_pairMoment, pairMoment_firstCollision, add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro r _
  rw [pairMoment_eq_secondMoment, mul_comm (sigmaSq β)]

end Critical2DKPZ.Polymer
