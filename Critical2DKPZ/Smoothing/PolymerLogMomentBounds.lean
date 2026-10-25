/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.Basic
public import Critical2DKPZ.Definitions.GaussianityDefect
import Mathlib.Tactic

/-! # One-point moment bounds for logarithmic smoothing -/

@[expose] public section

open Filter
open scoped Topology BoundedContinuousFunction ENNReal

namespace Critical2DKPZ.Smoothing

/-- The one-point logarithmic variance-defect bound of Proposition 4.1, uniform over compact ranges of the critical parameter. -/
def PropVDBound : Prop := ∀ A : ℝ,
  (∀ T₀ T₁ : ℝ, 0 < T₀ → T₀ < T₁ → ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
        ∀ (x : Site) (s n : ℕ), Even s → Even n → s ≤ n → T₀ * N ≤ n → (n : ℝ) ≤ T₁ * N →
          0 ≤ gaussianityDefect disorderLaw (fun ω => Real.log (smoothedP2Plane (criticalBeta ϑ N) s n x ω)) ∧
          gaussianityDefect disorderLaw (fun ω => Real.log (smoothedP2Plane (criticalBeta ϑ N) s n x ω)) ≤
            Real.log ((∫ ω, smoothedP2Plane (criticalBeta ϑ N) s n x ω ^ 2 ∂disorderLaw) /
              ∫ ω, (smoothedP2Plane (criticalBeta ϑ N) s n x ω)⁻¹ ∂disorderLaw) ∧
          Real.log ((∫ ω, smoothedP2Plane (criticalBeta ϑ N) s n x ω ^ 2 ∂disorderLaw) /
              ∫ ω, (smoothedP2Plane (criticalBeta ϑ N) s n x ω)⁻¹ ∂disorderLaw) ≤ C) ∧
      (∃ δ₀ C : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∃ o : ℕ → ℝ, Tendsto o atTop (nhds 0) ∧ ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
          ∀ (x : Site) (s : ℕ), Even s → s ≤ evenCeil (Real.sqrt δ * N) →
            Real.log ((∫ ω, smoothedP2Plane (criticalBeta ϑ N) s (evenCeil (Real.sqrt δ * N)) x ω ^ 2
                ∂disorderLaw) /
              ∫ ω, (smoothedP2Plane (criticalBeta ϑ N) s (evenCeil (Real.sqrt δ * N)) x ω)⁻¹ ∂disorderLaw) ≤
              C / |Real.log δ| ^ ((1 : ℝ) / 4) + o N)

end Critical2DKPZ.Smoothing

end
