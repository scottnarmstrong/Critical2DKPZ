/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.Profiles
public import Critical2DKPZ.Gaussian.TimeBlocks
import Mathlib.Tactic

/-! Polymer partition functions are measurable with respect to their time interval’s disorder and transform covariantly under simultaneous translations of space and disorder. -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Critical2DKPZ.Polymer

/-- Each coordinate belonging to a disorder block is measurable for that block. -/
theorem measurable_block_coordinate (a b : ℕ) (i : ℕ × Site)
    (hi : a < i.1 ∧ i.1 ≤ b) :
    Measurable[Gaussian.disorderBlock a b] (fun ω : Disorder => ω i) := by
  exact (measurable_pi_apply (⟨i, hi⟩ : Gaussian.timeBlock a b)).comp
    (comap_measurable (fun (ω : Disorder) (j : Gaussian.timeBlock a b) => ω j))

/-- A path weight is measurable with respect to its disorder block. -/
theorem measurable_pathWeight_block (β : ℝ) (a : ℕ) (w : Site) {n : ℕ}
    (s : Fin n → Fin 4) :
    Measurable[Gaussian.disorderBlock a (a + n)] (pathWeight β a w s) := by
  unfold pathWeight
  apply Measurable.exp
  apply Finset.measurable_sum
  intro j hj
  exact (measurable_const.mul (measurable_block_coordinate a (a + n)
    (a + j, walkPosition w s j) (by
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
      constructor <;> dsimp <;> omega))).sub measurable_const

/-- The point-to-plane partition function is measurable with respect to its disorder block. -/
theorem measurable_pointToPlane_block (β : ℝ) (a n : ℕ) (w : Site) :
    Measurable[Gaussian.disorderBlock a (a + n)] (pointToPlane β a n w) := by
  change Measurable[Gaussian.disorderBlock a (a + n)] (fun ω =>
    ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n * pathWeight β a w s ω)
  exact Finset.measurable_sum _ fun s _ =>
    measurable_const.mul (measurable_pathWeight_block β a w s)

/-- The point-to-point partition function is measurable with respect to its disorder block. -/
theorem measurable_pointToPoint_block (β : ℝ) (a n : ℕ) (w z : Site) :
    Measurable[Gaussian.disorderBlock a (a + n)] (pointToPoint β a n w z) := by
  change Measurable[Gaussian.disorderBlock a (a + n)] (fun ω =>
    ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n * pathWeight β a w s ω *
      if walkPosition w s n = z then 1 else 0)
  exact Finset.measurable_sum _ fun s _ =>
    (measurable_const.mul (measurable_pathWeight_block β a w s)).mul_const _

/-- The point-to-plane partition function is measurable with respect to the past disorder. -/
theorem measurable_pointToPlane_past (β : ℝ) (n : ℕ) (w : Site) :
    Measurable[disorderPast n] (pointToPlane β 0 n w) := by
  convert measurable_pointToPlane_block β 0 n w using 1
  rw [Nat.zero_add]
  rfl

/-- The point-to-point partition function is measurable with respect to the past disorder. -/
theorem measurable_pointToPoint_past (β : ℝ) (n : ℕ) (w z : Site) :
    Measurable[disorderPast n] (pointToPoint β 0 n w z) := by
  convert measurable_pointToPoint_block β 0 n w z using 1
  rw [Nat.zero_add]
  rfl


/-- Translating the starting point translates the walk positions. -/
theorem walkPosition_translate {n : ℕ} (w v : Site) (s : Fin n → Fin 4) (j : ℕ) :
    walkPosition (w + v) s j = walkPosition w s j + v := by
  simp only [walkPosition]
  abel

/-- Translating the walk and its disorder preserves the path weight. -/
theorem pathWeight_translate (β : ℝ) (a : ℕ) (w v : Site) {n : ℕ}
    (s : Fin n → Fin 4) (ω : Disorder) :
    pathWeight β a (w + v) s ω =
      pathWeight β a w s (fun p => ω (p.1, p.2 + v)) := by
  simp only [pathWeight, walkPosition_translate]

/-- Translating space and disorder preserves the point-to-plane partition function. -/
theorem pointToPlane_translate (β : ℝ) (a n : ℕ) (w v : Site) (ω : Disorder) :
    pointToPlane β a n (w + v) ω =
      pointToPlane β a n w (fun p => ω (p.1, p.2 + v)) := by
  simp only [pointToPlane_eq_sum, pathWeight_translate]

/-- Translating space and disorder preserves the point-to-point partition function. -/
theorem pointToPoint_translate (β : ℝ) (a n : ℕ) (w z v : Site) (ω : Disorder) :
    pointToPoint β a n (w + v) (z + v) ω =
      pointToPoint β a n w z (fun p => ω (p.1, p.2 + v)) := by
  simp only [pointToPoint_eq_sum, pathWeight_translate, walkPosition_translate,
    add_left_inj]


end Critical2DKPZ.Polymer
