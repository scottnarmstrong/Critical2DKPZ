/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.FutureProfiles.Basic

/-! # Conditions on future-profile energies and logarithmic moments -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal Topology

namespace Critical2DKPZ.FutureProfiles

open Critical2DKPZ.Blocks

/-- The five good-event probability and future-energy bounds for endpoint profiles. -/
def ProfileEstimatesBound : Prop := ∀ A : ℝ,
  ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ₁ : ℝ, ∃ (C : ℝ) (ℓ : ℕ), ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop,
        ∀ ϑ ∈ Set.Icc (-A) A, ∀ r s : ℕ, 1 ≤ r → r ≤ s → s + ℓ ≤ blockCount N ρ →
          (disorderLaw (profileGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s)ᶜ).toReal ≤
              C / ((blockCount N ρ : ℝ) - s) ∧
          ∫ ω in blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s,
              futureEnergy (criticalBeta ϑ N) (blockTime N ρ s) N
                (commonCorrection (criticalBeta ϑ N) (blockTime N ρ) r s ω) ∂disorderLaw ≤
            C / ((blockCount N ρ : ℝ) - s) ∧
          ∫ ω in blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s,
              futureEnergy (criticalBeta ϑ N) (blockTime N ρ s) N
                (weightedCorrection (criticalBeta ϑ N) (blockTime N ρ) r s ω) ∂disorderLaw ≤
            C / ((blockCount N ρ : ℝ) - s) ∧
          ∫ ω in profileGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s,
              Real.sqrt (futureEnergy (criticalBeta ϑ N) (blockTime N ρ s) N (fun y =>
                smoothedEndpointDist (criticalBeta ϑ N) (blockTime N ρ (r - 1)) (blockTime N ρ s) 0 ω y -
                  srwKernel (blockTime N ρ s) y -
                  commonCorrection (criticalBeta ϑ N) (blockTime N ρ) r s ω y)) ∂disorderLaw ≤
            C / ((blockCount N ρ : ℝ) - s) ∧
          ∫ ω in profileGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s,
              futureEnergy (criticalBeta ϑ N) (blockTime N ρ s) N
                (smoothedEndpointDist (criticalBeta ϑ N) (blockTime N ρ (r - 1)) (blockTime N ρ s) 0 ω)
              ∂disorderLaw ≤
            C * ((blockCount N ρ : ℝ) - s)

/-- Good-event comparison and second-moment bounds for endpoint and smoothed-endpoint partition functions. -/
def PropPFOriginBound : Prop := ∀ A : ℝ,
  ∃ δ₀ C : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ᶠ N : ℕ in atTop,
        ∀ ϑ ∈ Set.Icc (-A) A, ∃ G : Set Disorder,
          MeasurableSet[disorderPast (evenCeil (Real.sqrt δ * N))] G ∧
          (disorderLaw Gᶜ).toReal ≤ C / |Real.log δ| ∧
          ∫ ω in G, |profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
              (endpointDist (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) 0 ω) (fun _ => 1) ω -
            profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
              (smoothedEndpointDist (criticalBeta ϑ N) (evenCeil (δ * N)) (evenCeil (Real.sqrt δ * N)) 0 ω)
              (fun _ => 1) ω| ∂disorderLaw ≤ C / |Real.log δ| ∧
          (∫ ω in G, profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
              (endpointDist (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) 0 ω) (fun _ => 1) ω ^ 2
              ∂disorderLaw ≤ C * |Real.log δ|) ∧
          (∫ ω in G, profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
              (smoothedEndpointDist (criticalBeta ϑ N) (evenCeil (δ * N)) (evenCeil (Real.sqrt δ * N)) 0 ω)
              (fun _ => 1) ω ^ 2 ∂disorderLaw ≤ C * |Real.log δ|) ∧
          ∀ (f : Site → ℝ) (M : ℝ), (∀ z, |f z| ≤ M) →
            ∫ ω in G, |profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
                (endpointDist (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) 0 ω) f ω -
              profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
                (smoothedEndpointDist (criticalBeta ϑ N) (evenCeil (δ * N)) (evenCeil (Real.sqrt δ * N)) 0 ω)
                f ω| ∂disorderLaw ≤ C * M * Real.sqrt (Real.log |Real.log δ|) / |Real.log δ|

/-- Uniform logarithmic moment bounds for endpoint and smoothed-endpoint partition functions. -/
def LogTailsOriginBound : Prop := ∀ A : ℝ,
  ∀ p : ENNReal, 1 ≤ p → p ≠ ⊤ → ∃ C δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₁ →
        ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
          eLpNorm (fun ω => Real.log (profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
              (endpointDist (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) 0 ω) (fun _ => 1) ω)) p
              disorderLaw ≤ ENNReal.ofReal (C * Real.log |Real.log δ|) ∧
          eLpNorm (fun ω => Real.log (profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
              (smoothedEndpointDist (criticalBeta ϑ N) (evenCeil (δ * N)) (evenCeil (Real.sqrt δ * N)) 0 ω)
              (fun _ => 1) ω)) p disorderLaw ≤ ENNReal.ofReal (C * Real.log |Real.log δ|)

end Critical2DKPZ.FutureProfiles

end
