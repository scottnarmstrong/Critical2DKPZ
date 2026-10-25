/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.Replica
import Mathlib.Tactic

/-! # Two-replica formula with constrained or tested terminal endpoints -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.Polymer

/-- The product expectation of terminal-profile partition functions has the two-replica representation. -/
theorem terminalProfile_two_replica (β : ℝ) (a n : ℕ) (w v : Site)
    (f g : Site → ℝ) :
    (∫ ω, (∑' z, pointToPoint β a n w z ω * f z) *
      (∑' z, pointToPoint β a n v z ω * g z) ∂disorderLaw) =
      ∑ s : Fin n → Fin 4, ∑ t : Fin n → Fin 4,
        ((4 : ℝ)⁻¹ ^ n * (4 : ℝ)⁻¹ ^ n) *
          (∏ j ∈ Finset.Icc 1 n,
            if walkPosition w s j = walkPosition v t j then Real.exp (β ^ 2) else 1) *
          f (walkPosition w s n) * g (walkPosition v t n) := by
  let C (s t : Fin n → Fin 4) :=
    ((4 : ℝ)⁻¹ ^ n * (4 : ℝ)⁻¹ ^ n) *
      f (walkPosition w s n) * g (walkPosition v t n)
  have hint (s t : Fin n → Fin 4) :
      Integrable (fun ω => pathWeight β a w s ω * pathWeight β a v t ω) disorderLaw :=
    memLp_one_iff_integrable.mp (memLp_mul_double 1
      (by simpa only [mul_one] using memLp_pathWeight β a w s 2 (by norm_num))
      (by simpa only [mul_one] using memLp_pathWeight β a v t 2 (by norm_num)))
  have heq (ω : Disorder) :
      (∑' z, pointToPoint β a n w z ω * f z) *
        (∑' z, pointToPoint β a n v z ω * g z) =
        ∑ s : Fin n → Fin 4, ∑ t : Fin n → Fin 4,
          C s t * (pathWeight β a w s ω * pathWeight β a v t ω) := by
    rw [tsum_pointToPoint_mul, tsum_pointToPoint_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    unfold C
    ring
  simp_rw [heq]
  rw [integral_finsetSum _ fun s _ =>
    integrable_finsetSum _ fun t _ => (hint s t).const_mul _]
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_finsetSum _ fun t _ => (hint s t).const_mul _]
  apply Finset.sum_congr rfl
  intro t _
  rw [integral_const_mul, integral_pathWeight_mul]
  unfold C
  ring


end Critical2DKPZ.Polymer
