/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.Moments
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic

/-! At a fixed walk horizon, only finitely many endpoints contribute to the polymer kernel and its smoothed averages. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.Polymer

/-- The finite set of sites reachable in a given number of steps. -/
def endpoints (w : Site) (n : ℕ) : Finset Site :=
  Finset.univ.image (fun s : Fin n → Fin 4 => walkPosition w s n)

/-- A site is reachable exactly when some finite walk ends there. -/
theorem mem_endpoints_iff (w z : Site) (n : ℕ) :
    z ∈ endpoints w n ↔ Reachable n w z := by
  simp only [endpoints, Finset.mem_image, Finset.mem_univ, true_and, Reachable]

/-- The point-to-point partition function vanishes outside the reachable endpoint set. -/
theorem pointToPoint_eq_zero_of_not_mem (β : ℝ) (a n : ℕ)
    (w z : Site) (ω : Disorder) (hz : z ∉ endpoints w n) :
    pointToPoint β a n w z ω = 0 :=
  (pointToPoint_eq_zero_iff β a n w z ω).2
    (fun h => hz ((mem_endpoints_iff w z n).2 h))

/-- A terminally weighted kernel sum equals the finite average of terminally weighted paths. -/
theorem tsum_pointToPoint_mul (β : ℝ) (a n : ℕ) (w : Site)
    (f : Site → ℝ) (ω : Disorder) :
    ∑' z, pointToPoint β a n w z ω * f z =
      ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n * pathWeight β a w s ω *
        f (walkPosition w s n) := by
  have hs : ∀ s : Fin n → Fin 4, Summable (fun z : Site =>
      (4 : ℝ)⁻¹ ^ n * pathWeight β a w s ω *
        (if walkPosition w s n = z then 1 else 0) * f z) := by
    intro s
    apply summable_of_ne_finset_zero (s := {walkPosition w s n})
    intro z hz
    have hne : walkPosition w s n ≠ z := by
      simpa only [Finset.mem_singleton, not_not, ne_eq, eq_comm] using hz
    simp only [ite_eq_right hne, mul_zero, zero_mul]
  simp only [pointToPoint_eq_sum, Finset.sum_mul]
  rw [Summable.tsum_finsetSum (fun s _ => hs s)]
  apply Finset.sum_congr rfl
  intro s _
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, tsum_ite_eq']

/-- The sum of the point-to-point kernel over its endpoint is the point-to-plane partition function. -/
theorem tsum_pointToPoint (β : ℝ) (a n : ℕ) (w : Site) (ω : Disorder) :
    ∑' z, pointToPoint β a n w z ω = pointToPlane β a n w ω := by
  simpa only [mul_one, pointToPlane_eq_sum] using
    tsum_pointToPoint_mul β a n w (fun _ => 1) ω

/-- The infinite terminally weighted partition sum equals its finite endpoint sum. -/
theorem tsum_pointToPoint_mul_eq_sum (β : ℝ) (a n : ℕ) (w : Site)
    (f : Site → ℝ) (ω : Disorder) :
    ∑' z, pointToPoint β a n w z ω * f z =
      ∑ z ∈ endpoints w n, pointToPoint β a n w z ω * f z := by
  apply tsum_eq_sum
  intro z hz
  rw [pointToPoint_eq_zero_of_not_mem β a n w z ω hz, zero_mul]

/-- The simple-walk kernel is a finite sum over walks with the prescribed endpoint. -/
theorem srwKernel_eq_sum (n : ℕ) (w z : Site) :
    srwKernel n (z - w) = ∑ s : Fin n → Fin 4,
      (4 : ℝ)⁻¹ ^ n * if walkPosition w s n = z then 1 else 0 := by
  unfold srwKernel
  apply Finset.sum_congr rfl
  intro s _
  rw [walkPosition_eq_start_add w s n]
  simp only [eq_sub_iff_add_eq, add_comm]

/-- The simple-walk kernel vanishes at unreachable endpoints. -/
theorem srwKernel_eq_zero_of_not_mem (n : ℕ) (w z : Site)
    (hz : z ∉ endpoints w n) : srwKernel n (z - w) = 0 := by
  rw [srwKernel_eq_sum n w z]
  apply Finset.sum_eq_zero
  intro s _
  have hne : walkPosition w s n ≠ z := by
    intro hs
    exact hz ((mem_endpoints_iff w z n).2 ⟨s, hs⟩)
  simp only [ite_eq_right hne, mul_zero]

/-- The smoothed partition function equals its finite reachable-endpoint sum. -/
theorem smoothedP2Plane_eq_sum (β : ℝ) (s n : ℕ) (x : Site) (ω : Disorder) :
    smoothedP2Plane β s n x ω =
      ∑ y ∈ endpoints x s, srwKernel s (y - x) *
        pointToPlane β s (n - s) y ω := by
  unfold smoothedP2Plane
  apply tsum_eq_sum
  intro y hy
  rw [srwKernel_eq_zero_of_not_mem s x y hy, zero_mul]

/-- The smoothed point-to-plane partition function is measurable. -/
theorem measurable_smoothedP2Plane (β : ℝ) (s n : ℕ) (x : Site) :
    Measurable (smoothedP2Plane β s n x) := by
  change Measurable (fun ω => ∑' y : Site,
    srwKernel s (y - x) * pointToPlane β s (n - s) y ω)
  exact Measurable.tsum fun y =>
    measurable_const.mul (measurable_pointToPlane β s (n - s) y)

/-- The smoothed point-to-plane partition function belongs to Lᵖ for every finite exponent. -/
theorem memLp_smoothedP2Plane (β : ℝ) (s n : ℕ) (x : Site)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (smoothedP2Plane β s n x) p disorderLaw := by
  have heq : smoothedP2Plane β s n x =
      fun ω => ∑ y ∈ endpoints x s, srwKernel s (y - x) *
        pointToPlane β s (n - s) y ω := by
    funext ω
    exact smoothedP2Plane_eq_sum β s n x ω
  rw [heq]
  exact memLp_finsetSum _ fun y _ =>
    (memLp_pointToPlane β s (n - s) y p hp).const_mul _

/-- The final walk position is the endpoint of the finite path. -/
theorem walkPosition_end {n : ℕ} (w : Site) (s : Fin n → Fin 4) :
    walkPosition w s n = w + ∑ i, srwStep (s i) := by
  rw [walkPosition, Finset.filter_eq_self.2 (fun i _ => i.is_lt)]

/-- Each nearest-neighbor step reverses site parity. -/
theorem step_parity (s : Fin 4) :
    Int.ModEq 2 (srwStep s 0 + srwStep s 1) 1 := by
  fin_cases s <;> decide

/-- Walk position parity is determined by the starting site and elapsed time. -/
theorem walkPosition_parity {n : ℕ} (w : Site) (s : Fin n → Fin 4) :
    Int.ModEq 2 (walkPosition w s n 0 + walkPosition w s n 1)
      (w 0 + w 1 + n) := by
  have h := Int.ModEq.sum (s := (Finset.univ : Finset (Fin n)))
    (fun i _ => step_parity (s i))
  have hh : Int.ModEq 2 (∑ i, (srwStep (s i) 0 + srwStep (s i) 1)) (n : ℤ) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] using h
  rw [walkPosition_end]
  simp only [Pi.add_apply, Finset.sum_apply]
  have heq : (w 0 + ∑ i, srwStep (s i) 0) + (w 1 + ∑ i, srwStep (s i) 1) =
      (w 0 + w 1) + ∑ i, (srwStep (s i) 0 + srwStep (s i) 1) := by
    rw [Finset.sum_add_distrib]
    ring
  rw [heq]
  exact hh.add_left _

/-- The point-to-point partition function vanishes when the endpoint parity is incompatible. -/
theorem pointToPoint_eq_zero_of_parity (β : ℝ) (a n : ℕ) (w z : Site)
    (ω : Disorder) (h : ¬ Int.ModEq 2 (z 0 + z 1) (w 0 + w 1 + n)) :
    pointToPoint β a n w z ω = 0 := by
  apply (pointToPoint_eq_zero_iff β a n w z ω).2
  rintro ⟨s, hs⟩
  apply h
  simpa only [hs] using walkPosition_parity w s

end Critical2DKPZ.Polymer
