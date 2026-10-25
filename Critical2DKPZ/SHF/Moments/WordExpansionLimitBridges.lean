/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordExpansionAssembly
public import Critical2DKPZ.SHF.TimeContinuity.LimitPassage
public import Critical2DKPZ.SHF.Flow.SubseqDenseInputs
public import Critical2DKPZ.SHF.Limit.FirstMoment

/-! # Moving and fixed-time polymer moment limits -/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators CompactlySupported Topology

namespace Critical2DKPZ.SHF.Moments

open Polymer DeltaBose

/-- Geometric domination, vanishing non-pair remainders and word limits through order four imply polymer moment convergence along moving times. -/
theorem polymerMovingMomentLimit_of_wordStages (ϑ : ℝ)
    (hdom : ∀ n, 1 ≤ n → n ≤ 4 → WordGeometricDomination ϑ n)
    (hnp : ∀ n, 1 ≤ n → n ≤ 4 → NonpairRemainderSmall ϑ n)
    (hlim : ∀ n, 1 ≤ n → n ≤ 4 → WordLimits ϑ n) :
    Critical2DKPZ.SHF.TimeContinuity.PolymerMovingMomentLimit ϑ := by
  intro n hn hn4 s t hs hst sN tN hsN htN hsN0 φ
  exact rescaledP2P_moment_tendsto_moving_of ϑ n hn hn4
    (hdom n hn hn4) (hnp n hn hn4) (hlim n hn hn4)
    hs hst sN tN hsN htN hsN0 φ

/-- A moving rescaled-density moment limit implies the fixed-time polymer-measure limit.
The density-to-measure conversion is `integral_polymerMeasure`. -/
theorem polymerMomentLimit_of_polymerMovingMomentLimit (ϑ : ℝ)
    (hmoving : Critical2DKPZ.SHF.TimeContinuity.PolymerMovingMomentLimit ϑ) :
    Critical2DKPZ.SHF.Flow.PolymerMomentLimit ϑ := by
  intro n hn hn4 s t hs hst φ
  let sN : ℕ → ℝ := fun _ => s
  let tN : ℕ → ℝ := fun _ => t
  have hsN : Tendsto sN atTop (𝓝 s) := tendsto_const_nhds
  have htN : Tendsto tN atTop (𝓝 t) := tendsto_const_nhds
  have hsN0 : ∀ N, 0 ≤ sN N := fun _ => hs
  have hrescaled := hmoving n hn hn4 hs hst sN tN hsN htN hsN0 φ
  have hpairEq : (fun N : ℕ =>
      ∫ ω, ∏ i, (∫ p, φ i p ∂(Critical2DKPZ.SHF.Limit.polymerMeasure ϑ N s t ω))
        ∂disorderLaw) =ᶠ[atTop]
      (fun N : ℕ => ∫ ω, ∏ i,
        (∫ p, φ i p * rescaledP2P ϑ N s t p ω) ∂disorderLaw) := by
    filter_upwards [] with N
    congr 1
    funext ω
    congr 1
    funext i
    exact Critical2DKPZ.SHF.Limit.integral_polymerMeasure ϑ N s t ω (φ i)
  exact Tendsto.congr' hpairEq.symm hrescaled

/-- Geometric domination, vanishing non-pair remainders and word limits through order four imply fixed-time polymer moment convergence. -/
theorem polymerMomentLimit_of_wordStages (ϑ : ℝ)
    (hdom : ∀ n, 1 ≤ n → n ≤ 4 → WordGeometricDomination ϑ n)
    (hnp : ∀ n, 1 ≤ n → n ≤ 4 → NonpairRemainderSmall ϑ n)
    (hlim : ∀ n, 1 ≤ n → n ≤ 4 → WordLimits ϑ n) :
    Critical2DKPZ.SHF.Flow.PolymerMomentLimit ϑ :=
  polymerMomentLimit_of_polymerMovingMomentLimit ϑ
    (polymerMovingMomentLimit_of_wordStages ϑ hdom hnp hlim)

end Critical2DKPZ.SHF.Moments

end
