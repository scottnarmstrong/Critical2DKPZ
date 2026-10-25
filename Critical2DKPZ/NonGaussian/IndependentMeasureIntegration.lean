/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.MeasureKernels
public import Critical2DKPZ.RandomMeasure.GeneralRandom
public import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Tactic

/-! # Integrating an independent random measure with an outer parameter -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Tsai
open scoped ENNReal

namespace Critical2DKPZ.NonGaussian

/-- An independent almost surely locally finite random measure can be replaced by its mean
inside a nonnegative integral depending jointly measurably on a random parameter. -/
theorem lintegral_independent_measure_parameter {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → A) (hX : Measurable X)
    (B : Ω → Measure (Plane × Plane)) (hB : Measurable B)
    (hBLF : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (B ω)) (hind : IndepFun X B P)
    (H : A → (Plane × Plane) → ℝ≥0∞) (hH : Measurable (Function.uncurry H)) :
    (∫⁻ ω, ∫⁻ z, H (X ω) z ∂B ω ∂P) =
      ∫⁻ a, ∫⁻ z, H a z ∂P.bind B ∂P.map X := by
  let E : CompactExhaustion (Plane × Plane) := RandomMeasure.vagueCompactExhaustion (Plane × Plane)
  let M : Measure (Plane × Plane) → Measure (Plane × Plane) :=
    RandomMeasure.locallyFiniteMeasureModification E id
  have hM : Measurable M := RandomMeasure.measurable_locallyFiniteMeasureModification E id measurable_id
  have hMLF (μ : Measure (Plane × Plane)) : IsLocallyFiniteMeasure (M μ) :=
    RandomMeasure.locallyFinite_locallyFiniteMeasureModification E id μ
  let κ : Kernel (A × Measure (Plane × Plane)) (Plane × Plane) :=
    ⟨fun q => M q.2, hM.comp measurable_snd⟩
  let : IsSFiniteKernel κ := isSFiniteKernel_of_locallyFinite κ (fun q => hMLF q.2)
  let Φ : A × Measure (Plane × Plane) → ℝ≥0∞ := fun q => ∫⁻ z, H q.1 z ∂M q.2
  have hJoint : Measurable (fun q : (A × Measure (Plane × Plane)) × (Plane × Plane) => H q.1.1 q.2) :=
    hH.comp (measurable_fst.fst.prodMk measurable_snd)
  have hΦ : Measurable Φ := hJoint.lintegral_kernel_prod_right' (κ := κ)
  have hMB : ∀ᵐ ω ∂P, M (B ω) = B ω := by
    filter_upwards [hBLF] with ω hω
    exact RandomMeasure.locallyFiniteMeasureModification_apply_of_isLocallyFinite E id (B ω) hω
  have hPair : Measurable (fun ω => (X ω, B ω)) := hX.prodMk hB
  calc
    (∫⁻ ω, ∫⁻ z, H (X ω) z ∂B ω ∂P) = ∫⁻ ω, Φ (X ω, B ω) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hMB] with ω hω
      dsimp [Φ]
      rw [hω]
    _ = ∫⁻ q, Φ q ∂P.map (fun ω => (X ω, B ω)) :=
      (lintegral_map' hΦ.aemeasurable hPair.aemeasurable).symm
    _ = ∫⁻ q, Φ q ∂(P.map X).prod (P.map B) := by
      rw [hind.map_prod_eq_prod_map_map hX.aemeasurable hB.aemeasurable]
    _ = ∫⁻ a, ∫⁻ μ, Φ (a, μ) ∂P.map B ∂P.map X := lintegral_prod _ hΦ.aemeasurable
    _ = ∫⁻ a, ∫⁻ z, H a z ∂P.bind B ∂P.map X := by
      apply lintegral_congr
      intro a
      have hΦa : Measurable (fun μ => Φ (a, μ)) := hΦ.comp (measurable_const.prodMk measurable_id)
      have hHa : Measurable (H a) := hH.comp (measurable_const.prodMk measurable_id)
      calc
        (∫⁻ μ, Φ (a, μ) ∂P.map B) = ∫⁻ ω, Φ (a, B ω) ∂P :=
          lintegral_map' hΦa.aemeasurable hB.aemeasurable
        _ = ∫⁻ ω, ∫⁻ z, H a z ∂B ω ∂P := by
          apply lintegral_congr_ae
          filter_upwards [hMB] with ω hω
          dsimp [Φ]
          rw [hω]
        _ = ∫⁻ z, H a z ∂P.bind B := (Measure.lintegral_bind hB.aemeasurable hHa.aemeasurable).symm

end Critical2DKPZ.NonGaussian

end
