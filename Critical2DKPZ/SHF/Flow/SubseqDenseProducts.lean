/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SubseqDenseMoments
public import Critical2DKPZ.SHF.Flow.SubseqBlockIndependence
public import Critical2DKPZ.SHF.Flow.SubseqDenseMollifierApplicable

/-! # Smoothed composition in polymer subsequential limits

Compact cutoff estimates and approximate composition pass to the limiting smoothed products. -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Flow

open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai

/-- The rescaled bump at index `ℓ` is exactly the profile dilation in thin-slab composition at
scale `1 / (ℓ + 1)`. -/
theorem subseqDenseMollifier_eq_approxFlowDilation (ℓ : ℕ) :
    subseqDenseMollifier ℓ = fun x =>
      (1 / ((ℓ : ℝ) + 1))⁻¹ ^ 2 * subseqDenseMollifierBase
        ((1 / ((ℓ : ℝ) + 1))⁻¹ • x) := by
  funext x
  have h : (1 / ((ℓ : ℝ) + 1))⁻¹ = (ℓ : ℝ) + 1 := by
    field_simp
  rw [subseqDenseMollifier, h]

/-- Thin-slab composition applies eventually to the complete shrinking-bump sequence used for
the limiting smoothed product. -/
theorem subseqDenseMollifier_approxFlow_eventually (ϑ : ℝ)
    (hSmoothedApproximateFlowInput : SmoothedProductApproxFlow ϑ)
    {s t u : ℝ} (hs : 0 ≤ s) (hst : s < t) (htu : t < u)
    (Φ : C_c(Plane × Plane, ℝ)) :
    ∀ ε > 0, ∀ᶠ ℓ : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
      ∫ ω, (smoothedProductPairing (polymerMeasure ϑ N s t ω)
          (subseqDenseMollifier ℓ) (polymerMeasure ϑ N t u ω) Φ -
        ∫ p, Φ p ∂(polymerMeasure ϑ N s u ω)) ^ 2 ∂disorderLaw ≤ ε := by
  intro ε hε
  obtain ⟨η, hη, hSmoothedApproximateFlowInputη⟩ := hSmoothedApproximateFlowInput hs hst htu Φ subseqDenseMollifierBase
    subseqDenseMollifierBase_spec.2.1 subseqDenseMollifierBase_spec.2.2.1
    subseqDenseMollifierBase_spec.1 subseqDenseMollifierBase_spec.2.2.2.1 ε hε
  have hevent : ∀ᶠ ℓ : ℕ in atTop,
      0 < (1 / ((ℓ : ℝ) + 1)) ∧ (1 / ((ℓ : ℝ) + 1)) < η := by
    have hlim : Tendsto (fun ℓ : ℕ => 1 / ((ℓ : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hpos : ∀ ℓ : ℕ, 0 < (1 / ((ℓ : ℝ) + 1)) := by
      intro ℓ
      positivity
    filter_upwards [hlim.eventually (Iio_mem_nhds hη)] with ℓ hℓ
    exact ⟨hpos ℓ, hℓ⟩
  filter_upwards [hevent] with ℓ hℓ
  have heq := subseqDenseMollifier_eq_approxFlowDilation ℓ
  have hN := hSmoothedApproximateFlowInputη (1 / ((ℓ : ℝ) + 1)) hℓ.1 hℓ.2
  filter_upwards [hN] with N hN
  simpa only [← heq] using hN


/-- The moment, cutoff-tail, and approximate-composition bounds imply the SHF conditions on the countable time set of a polymer subsequential limit. -/
theorem isDenseSHF_of_subseqLimit_components (ϑ : ℝ)
    (D : Set ℝ) (hD : D.Countable) (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z)
    (hB : ∀ t₀ ∈ D, ∀ t₁ ∈ D, ∀ t₂ ∈ D, t₀ < t₁ → t₁ < t₂ →
      ∃ w : ℕ → Plane → ℝ, IsL2ApplicableMollifier w ∧
        (∀ ℓ, ∀ᵐ ω ∂P, SmoothedProductWellDefined (Z t₀ t₁ ω) (w ℓ) (Z t₁ t₂ ω)) ∧
        ∀ f : C_c(Plane × Plane, ℝ),
          TendstoInMeasure P (fun ℓ ω => smoothedProductPairing
            (Z t₀ t₁ ω) (w ℓ) (Z t₁ t₂ ω) f - ∫ p, f p ∂(Z t₀ t₂ ω))
            atTop (fun _ => 0))
    (hM : ∀ n : ℕ, 1 ≤ n → n ≤ 4 → ∀ s ∈ D, ∀ t ∈ D, s < t →
      ∀ g g' : Fin n → Plane → ℝ, (∀ i, MemLp (g i) 2) → (∀ i, MemLp (g' i) 2) →
        (∀ᵐ ω ∂P, ∀ i, Integrable
          (fun p : Plane × Plane => g i p.1 * g' i p.2) (Z s t ω)) ∧
        Integrable (fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2 ∂Z s t ω) P ∧
        ∫ ω, ∏ i, (∫ p, g i p.1 * g' i p.2 ∂Z s t ω) ∂P =
          ∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
            (∏ i, g i (x i)) *
              (DeltaBose.momentKernel n (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal *
                ∏ i, g' i (y i)) :
    IsDenseSHF (ϑ - Real.eulerMascheroniConstant) D P Z := by
  refine ⟨polymerSubseqLimit_measurable_locallyFinite ϑ D ψ P Z hZ, hB, ?_, hM⟩
  intro k t ht htD
  exact iIndepFun_polymerSubseqLimit_consecutive ϑ D hD ψ hψ P Z hZ k t ht htD

end Critical2DKPZ.SHF.Flow

end
