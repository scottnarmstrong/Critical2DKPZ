/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CompactTensorTests
public import Critical2DKPZ.SHF.Tsai.Products

/-! # Approximate composition on compact spatial tensor tests

The composition axiom tests the raw smoothed pairing. Almost-sure local
finiteness and the axiom's absolute integrability identify it with the
integral against the actual smoothed product measure.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- The actual smoothed product converges on compact endpoint tensors. -/
theorem tendstoInMeasure_smoothedProductPairing_compactTensor (θ : ℝ) (D : Set ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsDenseSHF θ D P Z)
    {t₀ t₁ t₂ : ℝ} (h₀ : t₀ ∈ D) (h₁ : t₁ ∈ D) (h₂ : t₂ ∈ D) (h₀₁ : t₀ < t₁) (h₁₂ : t₁ < t₂)
    (w : ℕ → Plane → ℝ) (hw : IsL2ApplicableMollifier w)
    (hwP : ∀ ℓ, ∀ᵐ ω ∂P, SmoothedProductWellDefined (Z t₀ t₁ ω) (w ℓ) (Z t₁ t₂ ω))
    (hconv : ∀ f : C_c(Plane × Plane, ℝ),
      TendstoInMeasure P (fun ℓ ω => smoothedProductPairing (Z t₀ t₁ ω) (w ℓ) (Z t₁ t₂ ω) f -
        ∫ p, f p ∂(Z t₀ t₂ ω)) atTop (fun _ => 0))
    (g g' : C_c(Plane, ℝ)) :
    TendstoInMeasure P (fun ℓ ω => (∫ p, g p.1 * g' p.2
      ∂smoothedProductMeasure (Z t₀ t₁ ω) (w ℓ) (Z t₁ t₂ ω)) -
        ∫ p, g p.1 * g' p.2 ∂Z t₀ t₂ ω) atTop (fun _ => 0) := by
  apply (hconv (compactTensorTest g g')).congr_left
  intro ℓ
  filter_upwards [(hZ.1 t₀ h₀ t₁ h₁ h₀₁).2, (hZ.1 t₁ h₁ t₂ h₂ h₁₂).2, hwP ℓ]
    with ω hLF₁ hLF₂ hwell
  let : IsLocallyFiniteMeasure (Z t₀ t₁ ω) := hLF₁
  let : IsLocallyFiniteMeasure (Z t₁ t₂ ω) := hLF₂
  rw [← integral_smoothedProductMeasure _ _ _ (hw.1 ℓ) ((hw.2.1 ℓ).measurable)
    (compactTensorTest g g') hwell]
  rfl

end Critical2DKPZ.SHF.Tsai

end
