/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.MomentKernelTwoSemigroup
public import Critical2DKPZ.SHF.Flow.SubseqBlockIndependence
public import Critical2DKPZ.SHF.Limit.Basic
public import Critical2DKPZ.SHF.Tsai.Cutoff
public import Critical2DKPZ.SHF.Tsai.Defs

/-! # Moment and approximate-composition conditions for polymer limits

These conditions specify compact-test moment convergence, sixth-moment bounds, cutoff tails, and approximate composition. -/

@[expose] public section

open MeasureTheory Filter
open scoped CompactlySupported Topology

namespace Critical2DKPZ.SHF.Flow

open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai

/-- The compact-test moment-convergence condition for one to four polymer replicas. Integrability follows by domination from `SHF.Limit.integrable_flat_polymerMeasure_pow`. -/
def PolymerMomentLimit (ϑ : ℝ) : Prop :=
  ∀ (n : ℕ), 1 ≤ n → n ≤ 4 → ∀ {s t : ℝ}, 0 ≤ s → s < t →
    ∀ φ : Fin n → C_c(Plane × Plane, ℝ),
      Tendsto
        (fun N => ∫ ω, ∏ i, (∫ p, φ i p ∂(polymerMeasure ϑ N s t ω)) ∂disorderLaw)
        atTop
        (𝓝 (∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
          (∏ i, φ i (x i, y i)) *
            (DeltaBose.momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal))

/-- The uniform sixth-moment condition for compact flat pairings over durations bounded away from zero. -/
def FlatSixthMomentBound (ϑ : ℝ) : Prop :=
  ∀ (χ : C_c(Plane, ℝ)) {τ T : ℝ}, 0 < τ →
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, ∀ s t : ℝ, 0 ≤ s → τ ≤ t - s → t ≤ T →
      Integrable
        (fun ω => (∫ x, |χ x| ∂((polymerMeasure ϑ N s t ω).map Prod.fst)) ^ 6)
        disorderLaw ∧
      ∫ ω, (∫ x, |χ x| ∂((polymerMeasure ϑ N s t ω).map Prod.fst)) ^ 6
        ∂disorderLaw ≤ C

/-- The uniform intermediate-cutoff tail condition for smoothed polymer products. Square integrability follows from `SHF.Flow.memLp_smoothedProductPairing_two`. -/
def SmoothedProductCutoffTail (ϑ : ℝ) : Prop :=
  ∀ {s t u : ℝ}, 0 ≤ s → s < t → t < u →
    ∀ (Φ : C_c(Plane × Plane, ℝ)) (k : Plane → ℝ),
      ((Continuous k ∧ HasCompactSupport k ∧ ∀ x, 0 ≤ k x) ∨
        ∃ v : ℝ, 0 < v ∧ k = heatKernel v) →
      ∀ ε > 0, ∃ R₀ : ℝ, ∀ R ≥ R₀, ∀ᶠ N : ℕ in atTop,
        ∫ ω,
          (smoothedProductPairing (polymerMeasure ϑ N s t ω) k
              (polymerMeasure ϑ N t u ω) Φ -
            ∫ q, Φ (q.1.1, q.2.2) * k (q.1.2 - q.2.1) *
              ballCutoff R q.1.2 * ballCutoff R q.2.1
              ∂((polymerMeasure ϑ N s t ω).prod
                (polymerMeasure ϑ N t u ω))) ^ 2 ∂disorderLaw ≤ ε

/-- The mean-square approximate-composition condition for smoothed polymer products. Square integrability follows from `SHF.Flow.memLp_smoothedProductPairing_two`. -/
def SmoothedProductApproxFlow (ϑ : ℝ) : Prop :=
  ∀ {s t u : ℝ}, 0 ≤ s → s < t → t < u →
    ∀ (Φ : C_c(Plane × Plane, ℝ)) (w : Plane → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) w → HasCompactSupport w → (∀ x, 0 ≤ w x) → ∫ x, w x = 1 →
      ∀ ε > 0, ∃ η > 0, ∀ e : ℝ, 0 < e → e < η → ∀ᶠ N : ℕ in atTop,
        ∫ ω,
          (smoothedProductPairing (polymerMeasure ϑ N s t ω)
              (fun x => e⁻¹ ^ 2 * w (e⁻¹ • x))
              (polymerMeasure ϑ N t u ω) Φ -
            ∫ p, Φ p ∂(polymerMeasure ϑ N s u ω)) ^ 2 ∂disorderLaw ≤ ε

end Critical2DKPZ.SHF.Flow

end
