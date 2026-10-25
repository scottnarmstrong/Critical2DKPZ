/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.BlockRatioExpansion
import Mathlib.Tactic

/-! # Block moments and tilted block-ratio bounds -/

@[expose] public section

open MeasureTheory
open ProbabilityTheory
open Filter
open scoped Topology BigOperators

namespace Critical2DKPZ.OnePoint

open Critical2DKPZ.Blocks

/-- Uniform variance and fourth centered moment bounds for geometric block masses. -/
def BlockMomentsBound : Prop :=
  ∀ A ρ₀ ρ₁ : ℝ, 1 < ρ₀ → ∃ C : ℝ, ∀ ρ ∈ Set.Icc ρ₀ ρ₁,
    ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
      ∀ i : ℕ, 1 ≤ i → i ≤ Critical2DKPZ.blockCount N ρ →
        Var[fun ω => smoothedP2Plane (Critical2DKPZ.criticalBeta ϑ N)
          (Critical2DKPZ.blockTime N ρ (i - 1)) (Critical2DKPZ.blockTime N ρ i) 0 ω;
          disorderLaw] ≤ C / ((Critical2DKPZ.blockCount N ρ : ℝ) + 1 - i) ∧
        ∫ ω, |smoothedP2Plane (Critical2DKPZ.criticalBeta ϑ N)
          (Critical2DKPZ.blockTime N ρ (i - 1)) (Critical2DKPZ.blockTime N ρ i) 0 ω - 1| ^ 4
          ∂disorderLaw ≤ C / ((Critical2DKPZ.blockCount N ρ : ℝ) + 1 - i) ^ 2

/-- Uniform bounds for the bad-event probability and good-event squared block ratio under the inverse-mass tilted law. -/
def TiltedRatioBound : Prop :=
  ∀ A : ℝ, ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ₁ : ℝ, ∃ C : ℝ,
    ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
      ∀ r s : ℕ, 1 ≤ r → r ≤ s → s + 1 ≤ Critical2DKPZ.blockCount N ρ →
        (∫ ω in (blockGoodSet (Critical2DKPZ.criticalBeta ϑ N)
            (Critical2DKPZ.blockTime N ρ) r s)ᶜ,
          ∏ i ∈ Finset.Icc r s,
            (blockMass (Critical2DKPZ.criticalBeta ϑ N) (Critical2DKPZ.blockTime N ρ) i ω)⁻¹
          ∂disorderLaw) /
            (∫ ω, ∏ i ∈ Finset.Icc r s,
              (blockMass (Critical2DKPZ.criticalBeta ϑ N) (Critical2DKPZ.blockTime N ρ) i ω)⁻¹
              ∂disorderLaw) ≤ C / Real.sqrt ((Critical2DKPZ.blockCount N ρ : ℝ) - s) ∧
        (∫ ω in blockGoodSet (Critical2DKPZ.criticalBeta ϑ N)
            (Critical2DKPZ.blockTime N ρ) r s,
          (blockRatio (Critical2DKPZ.criticalBeta ϑ N) (Critical2DKPZ.blockTime N ρ) r s ω - 1) ^ 2 *
            ∏ i ∈ Finset.Icc r s,
              (blockMass (Critical2DKPZ.criticalBeta ϑ N) (Critical2DKPZ.blockTime N ρ) i ω)⁻¹
          ∂disorderLaw) /
            (∫ ω, ∏ i ∈ Finset.Icc r s,
              (blockMass (Critical2DKPZ.criticalBeta ϑ N) (Critical2DKPZ.blockTime N ρ) i ω)⁻¹
              ∂disorderLaw) ≤ C / Real.sqrt ((Critical2DKPZ.blockCount N ρ : ℝ) - s)

/-- The logarithm of the second-to-reciprocal moment ratio at the origin is bounded by an inverse fourth root of the logarithmic small-time scale. -/
def SmallTimeOriginBound (A : ℝ) : Prop :=
  ∃ δ₀ C : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    ∃ o : ℕ → ℝ, Tendsto o atTop (nhds 0) ∧ ∀ᶠ N : ℕ in atTop,
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ s : ℕ, Even s →
        s ≤ Critical2DKPZ.evenCeil (Real.sqrt δ * N) →
          Real.log ((∫ ω, smoothedP2Plane (Critical2DKPZ.criticalBeta ϑ N) s
              (Critical2DKPZ.evenCeil (Real.sqrt δ * N)) 0 ω ^ 2 ∂disorderLaw) /
            ∫ ω, (smoothedP2Plane (Critical2DKPZ.criticalBeta ϑ N) s
              (Critical2DKPZ.evenCeil (Real.sqrt δ * N)) 0 ω)⁻¹ ∂disorderLaw) ≤
              C / |Real.log δ| ^ ((1 : ℝ) / 4) + o N

end Critical2DKPZ.OnePoint

end
