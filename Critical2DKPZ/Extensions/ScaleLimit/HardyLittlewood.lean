/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.Plane
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # The planar Hardy–Littlewood weak inequality

The maximal functions take values in the extended nonnegative reals. The
covering argument uses disjoint open balls and their fivefold enlargements.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The centered average of the absolute value on a ball. -/
def ballAverage (g : Plane → ℝ) (y : Plane) (r : ℝ) : ℝ≥0∞ :=
  (volume (ball y r))⁻¹ * ∫⁻ z in ball y r, ‖g z‖ₑ

/-- The centered Hardy–Littlewood maximal function, including infinite values. -/
def maximalFn (g : Plane → ℝ) (y : Plane) : ℝ≥0∞ :=
  ⨆ r : {r : ℝ // 0 < r}, ballAverage g y r

/-- The centered maximal function with radii bounded above. -/
def maximalFnLe (rbar : ℝ) (g : Plane → ℝ) (y : Plane) : ℝ≥0∞ :=
  ⨆ r : {r : ℝ // 0 < r ∧ r ≤ rbar}, ballAverage g y r

/-- Increasing the allowed radii increases the maximal function. -/
theorem maximalFnLe_mono (g : Plane → ℝ) (y : Plane) :
    Monotone (fun R => maximalFnLe R g y) := by
  intro R S hRS
  apply iSup_le
  intro r
  exact le_iSup_of_le ⟨r.1, r.2.1, r.2.2.trans hRS⟩ le_rfl

/-- Bounded maximal functions exhaust the full maximal function. -/
theorem maximalFn_eq_iSup (g : Plane → ℝ) (y : Plane) :
    maximalFn g y = ⨆ n : ℕ, maximalFnLe n g y := by
  apply le_antisymm
  · apply iSup_le
    intro r
    obtain ⟨n, hn⟩ := exists_nat_ge (r : ℝ)
    exact le_iSup_of_le n (le_iSup_of_le ⟨r.1, r.2, hn⟩ le_rfl)
  · apply iSup_le
    intro n
    apply iSup_le
    intro r
    exact le_iSup_of_le ⟨r.1, r.2.1⟩ le_rfl

/-- A ball with average above a threshold carries the corresponding mass. -/
theorem mul_ball_volume_le_of_lt_average {g : Plane → ℝ} {y : Plane} {r : ℝ}
    (hr : 0 < r) {Λ : ℝ≥0∞} (h : Λ < ballAverage g y r) :
    Λ * volume (ball y r) ≤ ∫⁻ z in ball y r, ‖g z‖ₑ := by
  have h0 : volume (ball y r) ≠ 0 := (measure_ball_pos volume y hr).ne'
  have ht : volume (ball y r) ≠ ⊤ := measure_ball_lt_top.ne
  calc
    Λ * volume (ball y r) ≤ ballAverage g y r * volume (ball y r) :=
      mul_le_mul' h.le le_rfl
    _ = ∫⁻ z in ball y r, ‖g z‖ₑ := by
      dsimp [ballAverage]
      rw [mul_right_comm, ENNReal.inv_mul_cancel h0 ht, one_mul]

/-- Fivefold enlargement multiplies planar ball volume by twenty-five. -/
theorem volume_ball_five_mul (y : Plane) (r : ℝ) :
    volume (ball y (5 * r)) = 25 * volume (ball y r) := by
  rw [volume.addHaar_ball_mul_of_pos y (by norm_num : (0 : ℝ) < 5) r,
    volume.addHaar_ball_center y r]
  norm_num [Plane, finrank_euclideanSpace]

/-- Explicit volume formula valid also at nonpositive radii. -/
theorem volume_ball_eq_radius_sq (y : Plane) (r : ℝ) :
    volume (ball y r) = (ENNReal.ofReal r) ^ 2 * volume (ball (0 : Plane) 1) := by
  by_cases hr : 0 ≤ r
  · rw [volume.addHaar_ball y hr]
    simp only [Plane, finrank_euclideanSpace, Fintype.card_fin, ENNReal.ofReal_pow hr]
  · have hr' : r ≤ 0 := (lt_of_not_ge hr).le
    simp only [ball_eq_empty.mpr hr', measure_empty, ENNReal.ofReal_eq_zero.mpr hr',
      zero_pow (by norm_num : 2 ≠ 0), zero_mul]

/-- Ball volume depends continuously on the radius. -/
theorem continuous_volume_ball (y : Plane) :
    Continuous (fun r : ℝ => volume (ball y r)) := by
  have hc : Continuous (fun r : ℝ => (ENNReal.ofReal r) ^ 2 *
      volume (ball (0 : Plane) 1)) :=
    (ENNReal.continuous_mul_const measure_ball_lt_top.ne).comp
      ((ENNReal.continuous_pow 2).comp ENNReal.continuous_ofReal)
  exact hc.congr (fun r => (volume_ball_eq_radius_sq y r).symm)


/-- Weak type estimate with bounded radii, from the Vitali covering theorem. -/
theorem maximalFnLe_weak11 (rbar : ℝ) (g : Plane → ℝ) (Λ : ℝ≥0∞) :
    Λ * volume {y | Λ < maximalFnLe rbar g y} ≤ 25 * ∫⁻ z, ‖g z‖ₑ := by
  classical
  let s := {y : Plane | Λ < maximalFnLe rbar g y}
  have hex (y : s) : ∃ r : {r : ℝ // 0 < r ∧ r ≤ rbar}, Λ < ballAverage g y r :=
    lt_iSup_iff.mp y.2
  choose ρ hρ using hex
  let x : s → Plane := Subtype.val
  let r : s → ℝ := fun y => (ρ y).1
  have hr (y : s) : 0 < r y := (ρ y).2.1
  obtain ⟨u, _, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball
      (univ : Set s) x r rbar (fun y _ => (ρ y).2.2) 5 (by norm_num)
  have hcount : u.Countable := hdisj.countable_of_isOpen
    (fun _ _ => isOpen_ball) (fun y _ => ⟨x y, mem_ball_self (hr y)⟩)
  have hs : s ⊆ ⋃ i ∈ u, ball (x i) (5 * r i) := by
    intro y hy
    obtain ⟨i, hi, hball⟩ := hcover ⟨y, hy⟩ (mem_univ _)
    exact mem_iUnion₂.mpr ⟨i, hi, hball (mem_ball_self (hr ⟨y, hy⟩))⟩
  have hmass (i : u) : Λ * volume (ball (x i.1) (r i.1)) ≤
      ∫⁻ z in ball (x i.1) (r i.1), ‖g z‖ₑ :=
    mul_ball_volume_le_of_lt_average (hr i.1) (hρ i.1)
  calc
    Λ * volume s ≤ Λ * volume (⋃ i ∈ u, ball (x i) (5 * r i)) :=
      mul_le_mul' le_rfl (measure_mono hs)
    _ ≤ Λ * ∑' i : u, volume (ball (x i.1) (5 * r i.1)) :=
      mul_le_mul' le_rfl (measure_biUnion_le volume hcount _)
    _ = 25 * ∑' i : u, Λ * volume (ball (x i.1) (r i.1)) := by
      simp only [volume_ball_five_mul, ENNReal.tsum_mul_left]
      ac_rfl
    _ ≤ 25 * ∑' i : u, ∫⁻ z in ball (x i.1) (r i.1), ‖g z‖ₑ :=
      mul_le_mul' le_rfl (ENNReal.tsum_le_tsum hmass)
    _ = 25 * ∫⁻ z in ⋃ i ∈ u, ball (x i) (r i), ‖g z‖ₑ := by
      rw [lintegral_biUnion hcount (fun _ _ => measurableSet_ball) hdisj]
    _ ≤ 25 * ∫⁻ z, ‖g z‖ₑ := mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)

/-- The planar Hardy–Littlewood maximal function satisfies the weak `(1,1)` estimate. -/
theorem hardyLittlewood_weak11 : ∃ C : ℝ≥0, ∀ (g : Plane → ℝ), Integrable g →
    ∀ Λ : ℝ≥0∞, Λ * volume {y | Λ < maximalFn g y} ≤ C * ∫⁻ z, ‖g z‖ₑ := by
  refine ⟨25, fun g _ Λ => ?_⟩
  have hsets : {y | Λ < maximalFn g y} =
      ⋃ n : ℕ, {y | Λ < maximalFnLe n g y} := by
    ext y
    simp only [mem_ofPred_eq, mem_iUnion, maximalFn_eq_iSup, lt_iSup_iff]
  have hmono : Monotone (fun n : ℕ => {y | Λ < maximalFnLe n g y}) := by
    intro n m hnm y hy
    exact hy.trans_le (maximalFnLe_mono g y (by exact_mod_cast hnm))
  rw [hsets, hmono.measure_iUnion, ENNReal.mul_iSup]
  exact iSup_le fun n => maximalFnLe_weak11 n g Λ

end Critical2DKPZ.Extensions.ScaleLimit

end
