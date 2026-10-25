/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BlockVectors
public import Critical2DKPZ.Blocks.Core
import Critical2DKPZ.Extensions.ScaleLimit.BlockIndependence
import Mathlib.Tactic

/-! # Continuous polynomial events for the block ratio

Multiplying out the positive denominator expresses the ratio tail as an open
set of the finite block vector. This avoids a discontinuous division at zero.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Product of the individual-block coordinates. -/
def blockVectorProduct (m : ℕ) (v : Fin (m + 1) → ℝ) : ℝ := ∏ i : Fin m, v i.succ

/-- The ratio tail, expressed as an open polynomial event. -/
def ratioBadEvent (m : ℕ) : Set (Fin (m + 1) → ℝ) :=
  {v | 0 < blockVectorProduct m v ∧ blockVectorProduct m v / 2 < |v 0 - blockVectorProduct m v|}

/-- The polynomial form is open on the finite-dimensional vector space. -/
theorem isOpen_ratioBadEvent (m : ℕ) : IsOpen (ratioBadEvent m) := by
  have hp : Continuous (blockVectorProduct m) := by unfold blockVectorProduct; fun_prop
  exact (isOpen_lt continuous_const hp).inter
    (isOpen_lt (hp.div_const 2) ((continuous_apply 0).sub hp).abs)

/-- Positive denominators identify the polynomial event with the ratio tail. -/
theorem mem_ratioBadEvent_iff {m : ℕ} (v : Fin (m + 1) → ℝ)
    (hp : 0 < blockVectorProduct m v) :
    v ∈ ratioBadEvent m ↔ 1 / 2 < |v 0 / blockVectorProduct m v - 1| := by
  have heq : v 0 / blockVectorProduct m v - 1 =
      (v 0 - blockVectorProduct m v) / blockVectorProduct m v := by field_simp
  rw [heq, abs_div, abs_of_pos hp, lt_div_iff₀ hp]
  change (0 < blockVectorProduct m v ∧ blockVectorProduct m v / 2 <
    |v 0 - blockVectorProduct m v|) ↔ _
  constructor
  · intro h
    nlinarith [h.2]
  · intro h
    exact ⟨hp, by nlinarith⟩

/-- The product in the lattice block vector is exactly the denominator of the
usual forward-indexed lattice block ratio. -/
theorem prod_latticeBlockVector_succ (ϑ ρ : ℝ) (N n ℓ : ℕ)
    (hℓn : ℓ < n) (hnK : n ≤ blockCount (2 * N) ρ) (ω : Disorder) :
    blockVectorProduct (n - ℓ) (latticeBlockVector ϑ ρ n ℓ N ω) =
      ∏ j ∈ Finset.Icc (blockCount (2 * N) ρ - n + 1) (blockCount (2 * N) ρ - ℓ),
        Blocks.blockMass (criticalBeta ϑ (2 * N)) (blockTime (2 * N) ρ) j ω := by
  let K := blockCount (2 * N) ρ
  change n ≤ K at hnK
  change (∏ i : Fin (n - ℓ), latticeGeometricMass ϑ ρ N (ℓ + i.val + 1) (ℓ + i.val) ω) = _
  rw [Fin.prod_univ_eq_prod_range (fun i => latticeGeometricMass ϑ ρ N (ℓ + i + 1) (ℓ + i) ω)]
  apply Finset.prod_bij (fun i _ => K - (ℓ + i))
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Icc]
    dsimp [K] at *
    omega
  · intro i hi j hj heq
    simp only [Finset.mem_range] at hi hj
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    refine ⟨K - ℓ - j, ?_, ?_⟩
    · simp only [Finset.mem_range]
      dsimp [K] at *
      omega
    · dsimp [K] at *
      omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    have hsub : K - (ℓ + i) - 1 = K - (ℓ + i + 1) := by omega
    change smoothedP2Plane _ (blockTime _ _ (K - (ℓ + i + 1)))
      (blockTime _ _ (K - (ℓ + i))) _ _ =
      smoothedP2Plane _ (blockTime _ _ (K - (ℓ + i) - 1)) (blockTime _ _ (K - (ℓ + i))) _ _
    rw [hsub]

/-- The vector ratio is the standard lattice block ratio after reversing indices. -/
theorem latticeBlockVector_ratio_eq (ϑ ρ : ℝ) (N n ℓ : ℕ)
    (hℓn : ℓ < n) (hnK : n ≤ blockCount (2 * N) ρ) (ω : Disorder) :
    latticeBlockVector ϑ ρ n ℓ N ω 0 /
        blockVectorProduct (n - ℓ) (latticeBlockVector ϑ ρ n ℓ N ω) =
      Blocks.blockRatio (criticalBeta ϑ (2 * N)) (blockTime (2 * N) ρ)
        (blockCount (2 * N) ρ - n + 1) (blockCount (2 * N) ρ - ℓ) ω := by
  rw [prod_latticeBlockVector_succ ϑ ρ N n ℓ hℓn hnK ω]
  simp only [latticeBlockVector, blockVectorStart, blockVectorEnd, Fin.cases_zero,
    latticeGeometricMass, Blocks.blockRatio, Nat.add_sub_cancel]

/-- All finite vector denominators are positive on the lattice. -/
theorem latticeBlockVector_product_pos (ϑ ρ : ℝ) (N n ℓ : ℕ) (ω : Disorder) :
    0 < blockVectorProduct (n - ℓ) (latticeBlockVector ϑ ρ n ℓ N ω) := by
  apply Finset.prod_pos
  intro i hi
  exact Polymer.smoothedP2Plane_pos _ _ _ _ _

/-- All finite vector denominators are almost surely positive in the flow. -/
theorem flowBlockVector_product_pos_ae (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) (n ℓ : ℕ) :
    ∀ᵐ ω ∂P, 0 < blockVectorProduct (n - ℓ) (flowBlockVector Z ρ n ℓ ω) := by
  have hp (i : Fin (n - ℓ)) := blockMass_pos_ae ϑ P Z hZ hρ (ℓ + i.val)
  filter_upwards [ae_all_iff.mpr hp] with ω hω
  apply Finset.prod_pos
  intro i hi
  rw [flowBlockVector_succ]
  exact hω i

/-- The ratio of the flow vector is the note's `R`. -/
theorem flowBlockVector_ratio_eq {Ω : Type*}
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (ρ : ℝ) (n ℓ : ℕ) (ω : Ω) :
    flowBlockVector Z ρ n ℓ ω 0 /
      blockVectorProduct (n - ℓ) (flowBlockVector Z ρ n ℓ ω) = blockR Z ρ n ℓ ω := by
  rw [blockVectorProduct, prod_flowBlockVector_succ, flowBlockVector_zero]
  rfl

end Critical2DKPZ.Extensions.ScaleLimit
