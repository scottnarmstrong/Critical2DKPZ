/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.ChapmanKolmogorov
public import Critical2DKPZ.PolymerCalculus.KernelReversal
public import Critical2DKPZ.Polymer.Endpoints
public import Mathlib.Tactic
public import Critical2DKPZ.PolymerCalculus.KernelReversal
import Mathlib.Tactic

/-! # Endpoint mass under lattice time reversal -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.LocalSobolev

/-- The parity of a walk endpoint is the starting parity toggled once per step. -/
theorem walkPosition_parity (z : Site) {n : ℕ} (s : Fin n → Fin 4) :
    Even (z 0 + z 1 + n) ↔
      Even ((walkPosition z s n) 0 + (walkPosition z s n) 1) := by
  revert z
  induction n with
  | zero => intro z; simp [walkPosition]
  | succ n ih =>
      intro z
      have hs : Fin.cons (s 0) (fun j => s j.succ) = s := by
        funext j
        exact Fin.cases rfl (fun i => rfl) j
      rw [← hs, Polymer.walkPosition_cons_succ]
      have hstep (i : Fin 4) :
          Even (z 0 + z 1 + (n + 1)) ↔
            Even ((z + srwStep i) 0 + (z + srwStep i) 1 + n) := by
        fin_cases i <;>
          simp [srwStep, Pi.add_apply, Int.even_add, Int.not_even_iff_odd,
            add_assoc, add_comm]
        all_goals
          by_cases hp : Even (z 0)
          · by_cases hq : Even (z 1)
            · simp [hp, hq]
            · have ho : Odd (z 1) := Int.not_even_iff_odd.mp hq
              simp [hp, hq, ho]
          · by_cases hq : Even (z 1)
            · simp [hp, hq]
            · have ho : Odd (z 1) := Int.not_even_iff_odd.mp hq
              simp [hp, hq, ho]
      exact (hstep (s 0)).trans (ih (fun j => s j.succ) (z + srwStep (s 0)))

/-- Summing the point-to-point kernel over its terminal sites after deleting the last
terminal-inclusive disorder factor leaves the preceding point-to-plane mass. -/
theorem tsum_pointToPoint_mul_remove_terminalSlice (β : ℝ) (n : ℕ) (x : Site)
    (ω : Disorder) :
    (∑' z, pointToPoint β 0 (n + 1) x z ω *
      Real.exp (-β * ω (n + 1, z))) =
      Real.exp (-(β ^ 2) / 2) * pointToPlane β 0 n x ω := by
  have hStep (z : Site) :
      (∑' w, pointToPoint β n 1 z w ω *
        Real.exp (-β * ω (n + 1, w))) = Real.exp (-(β ^ 2) / 2) := by
    rw [Polymer.tsum_pointToPoint_mul]
    simp_rw [show (4 : ℝ)⁻¹ ^ 1 = (4 : ℝ)⁻¹ by norm_num]
    have hterm (s : Fin 1 → Fin 4) :
        Polymer.pathWeight β n z s ω *
          Real.exp (-β * ω (n + 1, walkPosition z s 1) ) =
          Real.exp (-(β ^ 2) / 2) := by
      let e : Fin 0 → Fin 4 := fun j => Fin.elim0 j
      have hs : Fin.cons (s 0) e = s := by
        funext j
        fin_cases j
        rfl
      rw [← hs, Polymer.pathWeight_cons, Polymer.pathWeight_zero,
        Polymer.walkPosition_cons_one]
      simp only [mul_one]
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = ∑ s : Fin 1 → Fin 4,
          (4 : ℝ)⁻¹ * (Polymer.pathWeight β n z s ω *
            Real.exp (-β * ω (n + 1, walkPosition z s 1))) := by
        apply Finset.sum_congr rfl
        intro s hs
        ring
      _ = ∑ _s : Fin 1 → Fin 4, (4 : ℝ)⁻¹ * Real.exp (-(β ^ 2) / 2) := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [hterm]
      _ = Real.exp (-(β ^ 2) / 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
          Fintype.card_fin, nsmul_eq_mul]
        ring
  calc
    _ = ∑' x', pointToPoint β 0 n x x' ω *
        (∑' z, pointToPoint β n 1 x' z ω *
          Real.exp (-β * ω (n + 1, z))) := by
      simpa only [Nat.zero_add] using
        Polymer.terminalProfile_chapmanKolmogorov β 0 n 1 x
          (fun z => Real.exp (-β * ω (n + 1, z))) ω
    _ = ∑' x', pointToPoint β 0 n x x' ω *
        Real.exp (-(β ^ 2) / 2) := by
      apply tsum_congr
      intro x'
      rw [hStep]
    _ = Real.exp (-(β ^ 2) / 2) * pointToPlane β 0 n x ω := by
      calc
        _ = (∑' x', pointToPoint β 0 n x x' ω) * Real.exp (-(β ^ 2) / 2) :=
          tsum_mul_right
        _ = pointToPlane β 0 n x ω * Real.exp (-(β ^ 2) / 2) := by
          rw [Polymer.tsum_pointToPoint]
        _ = _ := by ring

/-- Reversing a flat terminal mass gives a point-to-plane mass with one fewer layer and
the explicit Gaussian factor at the fixed endpoint. -/
theorem tsum_pointToPoint_start_time_reversal (β : ℝ) {n : ℕ} (hn : 1 ≤ n)
    (x : Site) (ω : Disorder) :
    (∑' y, pointToPoint β 0 n y x ω) =
      Real.exp (β * ω (n, x) - β ^ 2 / 2) *
        pointToPlane β 0 (n - 1) x (PolymerCalculus.reversedDisorder n ω) := by
  have hterm (y : Site) :
      pointToPoint β 0 n y x ω =
        Real.exp (β * ω (n, x)) *
          (pointToPoint β 0 n x y (PolymerCalculus.reversedDisorder n ω) *
            Real.exp (-β * ω (0, y))) := by
    have hrev := PolymerCalculus.pointToPoint_time_reversal β n 0 n (by omega)
      y x ω
    simp only [Nat.zero_add, Nat.sub_self] at hrev
    have hexp : Real.exp (β * ω (0, y)) * Real.exp (-β * ω (0, y)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      pointToPoint β 0 n y x ω =
          (Real.exp (β * ω (0, y)) * Real.exp (-β * ω (0, y))) *
            pointToPoint β 0 n y x ω := by rw [hexp, one_mul]
      _ = (Real.exp (β * ω (0, y)) * pointToPoint β 0 n y x ω) *
            Real.exp (-β * ω (0, y)) := by ring
      _ = (Real.exp (β * ω (n, x)) *
          pointToPoint β 0 n x y (PolymerCalculus.reversedDisorder n ω)) *
            Real.exp (-β * ω (0, y)) := by rw [hrev]
      _ = _ := by ring
  calc
    _ = ∑' y, Real.exp (β * ω (n, x)) *
        (pointToPoint β 0 n x y (PolymerCalculus.reversedDisorder n ω) *
          Real.exp (-β * ω (0, y))) := by
      apply tsum_congr
      exact hterm
    _ = Real.exp (β * ω (n, x)) *
        (∑' y, pointToPoint β 0 n x y (PolymerCalculus.reversedDisorder n ω) *
          Real.exp (-β * ω (0, y))) := by rw [← tsum_mul_left]
    _ = Real.exp (β * ω (n, x)) *
        (Real.exp (-(β ^ 2) / 2) * pointToPlane β 0 (n - 1) x
          (PolymerCalculus.reversedDisorder n ω)) := by
      have hmass := tsum_pointToPoint_mul_remove_terminalSlice β (n - 1) x
        (PolymerCalculus.reversedDisorder n ω)
      have htime : n - 1 + 1 = n := by omega
      rw [htime] at hmass
      have hnoise : (fun y : Site => Real.exp (-β * ω (0, y))) =
          fun y => Real.exp (-β * PolymerCalculus.reversedDisorder n ω (n, y)) := by
        funext y
        simp [PolymerCalculus.reversedDisorder, Gaussian.reindexDisorder,
          PolymerCalculus.timeReversalIndex, PolymerCalculus.reflectedTime]
      have hsum :
          (∑' y, pointToPoint β 0 n x y (PolymerCalculus.reversedDisorder n ω) *
            Real.exp (-β * ω (0, y))) =
          ∑' y, pointToPoint β 0 n x y (PolymerCalculus.reversedDisorder n ω) *
            Real.exp (-β * PolymerCalculus.reversedDisorder n ω (n, y)) := by
        apply tsum_congr
        intro y
        rw [congrFun hnoise y]
      exact congrArg (fun q : ℝ => Real.exp (β * ω (n, x)) * q) (hsum.trans hmass)
    _ = _ := by
      calc
        _ = (Real.exp (β * ω (n, x)) * Real.exp (-(β ^ 2) / 2)) *
            pointToPlane β 0 (n - 1) x (PolymerCalculus.reversedDisorder n ω) := by ring
        _ = Real.exp (β * ω (n, x) + (-(β ^ 2) / 2)) *
            pointToPlane β 0 (n - 1) x (PolymerCalculus.reversedDisorder n ω) := by
          rw [← Real.exp_add]
        _ = _ := by
          rw [show β * ω (n, x) + (-(β ^ 2) / 2) =
            β * ω (n, x) - β ^ 2 / 2 by ring]

end Critical2DKPZ.LocalSobolev

end
