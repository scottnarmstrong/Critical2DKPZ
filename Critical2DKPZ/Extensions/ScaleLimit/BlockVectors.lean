/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.LatticeBlockConvergence
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-! # The finite block vector underlying the ratio estimates -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Initial reversed indices for the long mass followed by its individual blocks. -/
def blockVectorStart (n ℓ : ℕ) : Fin (n - ℓ + 1) → ℕ :=
  Fin.cases n (fun i => ℓ + i.val + 1)

/-- Terminal reversed indices in the same order. -/
def blockVectorEnd (n ℓ : ℕ) : Fin (n - ℓ + 1) → ℕ :=
  Fin.cases ℓ (fun i => ℓ + i.val)

/-- The finite lattice vector at fixed reversed indices. -/
def latticeBlockVector (ϑ ρ : ℝ) (n ℓ N : ℕ) (ω : Disorder) : Fin (n - ℓ + 1) → ℝ :=
  fun i => latticeGeometricMass ϑ ρ N (blockVectorStart n ℓ i) (blockVectorEnd n ℓ i) ω

/-- The corresponding vector of the prescribed flow. -/
def flowBlockVector {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (ρ : ℝ) (n ℓ : ℕ) (ω : Ω) : Fin (n - ℓ + 1) → ℝ :=
  fun i => shfPairing Z (tau ρ (blockVectorStart n ℓ i)) (tau ρ (blockVectorEnd n ℓ i))
    (fun y => heatKernel (tau ρ (blockVectorStart n ℓ i)) y) (fun _ => 1) ω

/-- The block vector converges jointly at every fixed pair of endpoints. -/
theorem blockVector_tendsto (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) (n ℓ : ℕ) (hℓn : ℓ < n) :
    TendstoInDistribution (latticeBlockVector ϑ ρ n ℓ) atTop
      (flowBlockVector Z ρ n ℓ) (fun _ => disorderLaw) P := by
  apply latticeGeometricMass_joint_tendsto ϑ P Z hZ hρ
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hℓn
  · change ℓ + j.val < ℓ + j.val + 1
    omega

/-- Coordinate zero is the multi-block flow mass. -/
theorem flowBlockVector_zero {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (ρ : ℝ) (n ℓ : ℕ) (ω : Ω) : flowBlockVector Z ρ n ℓ ω 0 = blockA Z ρ n ℓ ω := rfl

/-- Successor coordinates are the positive-index individual blocks. -/
theorem flowBlockVector_succ {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (ρ : ℝ) (n ℓ : ℕ) (ω : Ω) (i : Fin (n - ℓ)) :
    flowBlockVector Z ρ n ℓ ω i.succ = blockMass Z ρ (ℓ + i.val + 1) ω := by
  simp only [flowBlockVector, blockVectorStart, blockVectorEnd, Fin.cases_succ,
    blockMass, Nat.add_sub_cancel]

/-- The product of successor coordinates is the denominator of the flow ratio. -/
theorem prod_flowBlockVector_succ {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (ρ : ℝ) (n ℓ : ℕ) (ω : Ω) :
    (∏ i : Fin (n - ℓ), flowBlockVector Z ρ n ℓ ω i.succ) =
      ∏ j ∈ Finset.Ioc ℓ n, blockMass Z ρ j ω := by
  simp only [flowBlockVector_succ]
  rw [Fin.prod_univ_eq_prod_range (fun i => blockMass Z ρ (ℓ + i + 1) ω)]
  rw [show Finset.Ioc ℓ n = Finset.Ico (ℓ + 1) (n + 1) from by ext j; simp]
  rw [Finset.prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_add_right]
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  omega

end Critical2DKPZ.Extensions.ScaleLimit
