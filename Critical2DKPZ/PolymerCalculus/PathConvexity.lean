/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.Basic
public import Critical2DKPZ.PolymerCalculus.LogSumExp
import Mathlib.Tactic

/-! For nonnegative coefficients with at least one positive, the finite path mass has a convex logarithm, which is also increasing in the disorder when `β ≥ 0`. -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Critical2DKPZ.PolymerCalculus

/-- The affine disorder energy of one path, with noise on `(a,a+n]`. -/
def pathEnergy (β : ℝ) (a : ℕ) (w : Site) {n : ℕ}
    (s : Fin n → Fin 4) (ω : Disorder) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, (β * ω (a + j, walkPosition w s j) - β ^ 2 / 2)

/-- Path energy preserves convex combinations of disorder fields. -/
theorem pathEnergy_combo (β : ℝ) (a : ℕ) (w : Site) {n : ℕ}
    (s : Fin n → Fin 4) (x y : Disorder) {u v : ℝ} (huv : u + v = 1) :
    pathEnergy β a w s (u • x + v • y) =
      u * pathEnergy β a w s x + v * pathEnergy β a w s y := by
  simp only [pathEnergy, Finset.mul_sum, ← Finset.sum_add_distrib,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  linear_combination (β ^ 2 / 2) * huv

/-- The path energy is an affine, hence convex, function of the disorder. -/
theorem convexOn_pathEnergy (β : ℝ) (a : ℕ) (w : Site) {n : ℕ}
    (s : Fin n → Fin 4) : ConvexOn ℝ univ (pathEnergy β a w s) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ u v _ _ huv
  exact (pathEnergy_combo β a w s x y huv).le

/-- For `β ≥ 0`, the path energy is increasing in every disorder coordinate. -/
theorem monotone_pathEnergy {β : ℝ} (hβ : 0 ≤ β) (a : ℕ) (w : Site) {n : ℕ}
    (s : Fin n → Fin 4) : Monotone (pathEnergy β a w s) := by
  intro x y hxy
  exact Finset.sum_le_sum fun j _ =>
    sub_le_sub_right (mul_le_mul_of_nonneg_left (hxy _) hβ) _

/-- The finite path mass is the sum of Boltzmann weights multiplied by deterministic path coefficients. -/
def finitePathMass {ι : Type*} [Fintype ι] (β : ℝ) (a n : ℕ)
    (w : ι → Site) (c : ι × (Fin n → Fin 4) → ℝ) (ω : Disorder) : ℝ :=
  ∑ p, c p * Real.exp (pathEnergy β a (w p.1) p.2 ω)

/-- A finite path mass with nonnegative coefficients is strictly positive if at least one coefficient is positive. -/
theorem finitePathMass_pos {ι : Type*} [Fintype ι] (β : ℝ) (a n : ℕ)
    (w : ι → Site) {c : ι × (Fin n → Fin 4) → ℝ}
    (hc : ∀ p, 0 ≤ c p) (hp : ∃ p, 0 < c p) (ω : Disorder) :
    0 < finitePathMass β a n w c ω := weighted_exp_sum_pos hc hp _


/-- With nonnegative coefficients and at least one positive coefficient, the logarithm of the finite path mass is convex in the disorder. -/
theorem convexOn_log_finitePathMass {ι : Type*} [Fintype ι] (β : ℝ) (a n : ℕ)
    (w : ι → Site) {c : ι × (Fin n → Fin 4) → ℝ}
    (hc : ∀ p, 0 ≤ c p) (hp : ∃ p, 0 < c p) :
    ConvexOn ℝ univ (fun ω => Real.log (finitePathMass β a n w c ω)) :=
  convexOn_log_weighted_exp_sum convex_univ hc hp (fun _ => convexOn_pathEnergy ..)


/-- For `β ≥ 0` and nonnegative coefficients with at least one positive, the log mass is increasing in every disorder coordinate. -/
theorem monotone_log_finitePathMass {ι : Type*} [Fintype ι] {β : ℝ} (hβ : 0 ≤ β)
    (a n : ℕ) (w : ι → Site) {c : ι × (Fin n → Fin 4) → ℝ}
    (hc : ∀ p, 0 ≤ c p) (hp : ∃ p, 0 < c p) :
    Monotone (fun ω => Real.log (finitePathMass β a n w c ω)) :=
  monotone_log_weighted_exp_sum hc hp (fun _ => monotone_pathEnergy hβ ..)

/-- The finite weighted path mass is measurable. -/
theorem measurable_finitePathMass {ι : Type*} [Fintype ι] (β : ℝ) (a n : ℕ)
    (w : ι → Site) (c : ι × (Fin n → Fin 4) → ℝ) :
    Measurable (finitePathMass β a n w c) := by
  unfold finitePathMass pathEnergy
  fun_prop

/-- The logarithm of the finite weighted path mass is measurable. -/
theorem measurable_log_finitePathMass {ι : Type*} [Fintype ι] (β : ℝ) (a n : ℕ)
    (w : ι → Site) (c : ι × (Fin n → Fin 4) → ℝ) :
    Measurable (fun ω => Real.log (finitePathMass β a n w c ω)) :=
  (measurable_finitePathMass β a n w c).log





/-- The deterministic endpoint indicator is absorbed into the nonnegative coefficients. -/
theorem pointToPoint_eq_weighted_exp (β : ℝ) (a n : ℕ) (w z : Site) (ω : Disorder) :
    pointToPoint β a n w z ω = ∑ s : Fin n → Fin 4,
      ((4 : ℝ)⁻¹ ^ n * if walkPosition w s n = z then 1 else 0) *
        Real.exp (pathEnergy β a w s ω) := by
  rw [Polymer.pointToPoint_eq_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Polymer.pathWeight, pathEnergy]
  ring


/-- For a reachable endpoint, the logarithm of the point-to-point partition function is convex in the disorder. -/
theorem convexOn_log_pointToPoint (β : ℝ) (a n : ℕ) (w z : Site)
    (hz : Polymer.Reachable n w z) :
    ConvexOn ℝ univ (fun ω => Real.log (pointToPoint β a n w z ω)) := by
  simp_rw [pointToPoint_eq_weighted_exp]
  apply convexOn_log_weighted_exp_sum convex_univ (fun _ => by positivity)
  · obtain ⟨s, hs⟩ := hz
    exact ⟨s, by rw [ite_eq_left hs, mul_one]; positivity⟩
  · exact fun _ => convexOn_pathEnergy ..



end Critical2DKPZ.PolymerCalculus
