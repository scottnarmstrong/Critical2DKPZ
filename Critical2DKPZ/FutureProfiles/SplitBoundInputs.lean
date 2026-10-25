/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.Core
public import Critical2DKPZ.FutureProfiles.ProfileLogTails
public import Critical2DKPZ.Smoothing.EndpointDistribution

/-! # Discrepancy, block-ratio and logarithmic-tail bounds -/

@[expose] public section

open MeasureTheory Filter Set
open scoped BigOperators ENNReal
open Critical2DKPZ.Blocks

namespace Critical2DKPZ.FutureProfiles

/-- A geometric second-moment bound for the open discrepancy mass. -/
def OpenStringBound : Prop := ∀ A : ℝ,
  ∃ C C₀ : ℝ, 0 < C₀ ∧ ∀ ρ : ℝ, Real.exp (C₀ ^ 2) < ρ → ∀ᶠ N : ℕ in atTop,
        ∀ ϑ ∈ Set.Icc (-A) A, ∀ u v : ℕ, 1 ≤ u → u < v → v + 1 ≤ blockCount N ρ →
          ∫ ω, openDiscrepancyMass (criticalBeta ϑ N) (blockTime N ρ) N u v ω ^ 2 ∂disorderLaw ≤
            (C * (C₀ / Real.sqrt (Real.log ρ)) ^ (v - u - 1)) ^ 2 /
              ((blockCount N ρ : ℝ) - u)

/-- The original-law probability and second-moment bounds for the block ratio. -/
def RatioBoundP : Prop := ∀ A : ℝ,
  ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ₁ : ℝ, ∃ C : ℝ,
      ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop,
        ∀ ϑ ∈ Set.Icc (-A) A, ∀ r s : ℕ, 1 ≤ r → r ≤ s → s + 1 ≤ blockCount N ρ →
          (disorderLaw (blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s)ᶜ).toReal ≤
              C / ((blockCount N ρ : ℝ) - s) ∧
          ∫ ω in blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s,
              (blockRatio (criticalBeta ϑ N) (blockTime N ρ) r s ω - 1) ^ 2 ∂disorderLaw ≤
            C / ((blockCount N ρ : ℝ) - s)

/-- Exponential tails for the absolute logarithms of the endpoint and smoothed-endpoint partition functions. -/
def LogProfileTailBound : Prop := ∀ A : ℝ,
  ∃ δ₁ C : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∀ᶠ N : ℕ in atTop,
        ∀ ϑ ∈ Set.Icc (-A) A, ∀ u : ℝ, 0 ≤ u →
          (disorderLaw {ω | u < |Real.log (profileP2Fun (criticalBeta ϑ N)
              (evenCeil (Real.sqrt δ * N)) N
              (endpointDist (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) 0 ω)
              (fun _ => 1) ω)|}).toReal ≤
            C * Real.sqrt |Real.log δ| * Real.exp (-u / 3) ∧
          (disorderLaw {ω | u < |Real.log (profileP2Fun (criticalBeta ϑ N)
              (evenCeil (Real.sqrt δ * N)) N
              (smoothedEndpointDist (criticalBeta ϑ N) (evenCeil (δ * N))
                (evenCeil (Real.sqrt δ * N)) 0 ω)
              (fun _ => 1) ω)|}).toReal ≤
            C * Real.sqrt |Real.log δ| * Real.exp (-u / 3)

end Critical2DKPZ.FutureProfiles

end
