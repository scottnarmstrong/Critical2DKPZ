/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.CollisionCount
public import Critical2DKPZ.Polymer.Replica
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic

/-!
# Exact Gaussian replica formula for arbitrary finite order

Every microscopic time from one through the terminal time is included. The potential
counts unordered pairs even at higher multiple collisions; no aperiodicity is used.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Polymer

/-- A finite product of normalized Boltzmann weights equals the corresponding Gaussian exponential. -/
theorem prod_boltzmann_eq_finiteExp {ι : Type*} [Fintype ι]
    (β : ℝ) (e : ι → ℕ × Site) :
    (fun ω => ∏ i, boltzmann β (e i) ω) =
      finiteExp e (fun _ => β) (-((Fintype.card ι : ℝ) * β ^ 2 / 2)) := by
  funext ω
  simp only [boltzmann, ← Real.exp_sum, finiteExp, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  ring

/-- Exact pair additivity at a single time, including every multiple collision. -/
theorem integral_prod_boltzmann {ι : Type*} [Fintype ι] [LinearOrder ι]
    (β : ℝ) (e : ι → ℕ × Site) :
    ∫ ω, ∏ i, boltzmann β (e i) ω ∂disorderLaw =
      Real.exp (β ^ 2 * collisionCount e) := by
  rw [prod_boltzmann_eq_finiteExp, integral_finiteExp_repeated]
  rw [← Finset.sum_div, sum_constantCoefficient_sq]
  congr 1
  ring

/-- Adding the same time coordinate to every site preserves the collision count. -/
theorem collisionCount_time {ι : Type*} [Fintype ι] [LinearOrder ι]
    (a : ℕ) (x : ι → Site) :
    collisionCount (fun i => (a, x i)) = collisionCount x := by
  simp only [collisionCount, Prod.mk.injEq, true_and]

/-- Collision potential of a configuration of replica positions. -/
def replicaPotential {h : ℕ} (x : Fin h → Site) : ℝ := collisionCount x

/-- A prescribed collection of paths has exactly the pair-additive Gaussian weight. -/
theorem integral_prod_pathWeight (β : ℝ) (a n h : ℕ)
    (w : Fin h → Site) (s : Fin h → Fin n → Fin 4) :
    ∫ ω, ∏ i, pathWeight β a (w i) (s i) ω ∂disorderLaw =
      Real.exp (β ^ 2 * ∑ j ∈ Finset.Icc 1 n,
        replicaPotential (fun i => walkPosition (w i) (s i) j)) := by
  let F : ↥(Finset.Icc 1 n) → Disorder → ℝ := fun j ω =>
    ∏ i, boltzmann β (a + j.val, walkPosition (w i) (s i) j.val) ω
  have hm : ∀ j, Measurable[Gaussian.disorderBlock (a + j.val - 1) (a + j.val)]
      (F j) := by
    intro j
    have htime : a + j.val - 1 < a + j.val ∧ a + j.val ≤ a + j.val := by
      have hj := (Finset.mem_Icc.1 j.property).1
      omega
    apply Finset.measurable_prod
    intro i _
    exact ((measurable_const.mul (measurable_block_coordinate _ _ _ htime)).sub
      measurable_const).exp
  have hd : Pairwise fun i j : ↥(Finset.Icc 1 n) =>
      Disjoint (Set.Ioc (a + i.val - 1) (a + i.val))
        (Set.Ioc (a + j.val - 1) (a + j.val)) := by
    intro i j hij
    apply Set.disjoint_left.2
    intro r hi hj
    have hne : i.val ≠ j.val := fun hh => hij (Subtype.ext hh)
    obtain ⟨hi1, hi2⟩ := hi
    obtain ⟨hj1, hj2⟩ := hj
    omega
  have hind := independent_of_blockMeasurable
    (fun j : ↥(Finset.Icc 1 n) => a + j.val - 1)
    (fun j => a + j.val) hd F hm
  have hh := hind.integral_fun_prod_eq_prod_integral (fun j =>
    ((hm j).mono (Gaussian.disorderBlock_le _ _) le_rfl).aestronglyMeasurable)
  have heq (ω : Disorder) : (∏ i, pathWeight β a (w i) (s i) ω) =
      ∏ j : ↥(Finset.Icc 1 n), F j ω := by
    simp_rw [pathWeight_eq_prod]
    rw [Finset.prod_comm]
    exact (Finset.prod_coe_sort _ _).symm
  simp_rw [heq]
  rw [hh]
  calc
    _ = ∏ j : ↥(Finset.Icc 1 n),
        Real.exp (β ^ 2 * replicaPotential
          (fun i => walkPosition (w i) (s i) j.val)) := by
      apply Finset.prod_congr rfl
      intro j _
      change (∫ ω, ∏ i, boltzmann β
        (a + j.val, walkPosition (w i) (s i) j.val) ω ∂disorderLaw) = _
      rw [integral_prod_boltzmann, collisionCount_time]
      rfl
    _ = _ := by
      rw [← Real.exp_sum, ← Finset.mul_sum]
      rw [Finset.sum_coe_sort (Finset.Icc 1 n)
        (fun j => replicaPotential (fun i => walkPosition (w i) (s i) j))]

/-- A finite product of replica path weights is integrable in the disorder. -/
theorem integrable_prod_pathWeight (β : ℝ) (a n h : ℕ)
    (w : Fin h → Site) (s : Fin h → Fin n → Fin 4) :
    Integrable (fun ω => ∏ i, pathWeight β a (w i) (s i) ω) disorderLaw :=
  Integrable.of_integral_ne_zero (by
    rw [integral_prod_pathWeight]
    exact Real.exp_ne_zero _)

end Critical2DKPZ.SHF.Moments
