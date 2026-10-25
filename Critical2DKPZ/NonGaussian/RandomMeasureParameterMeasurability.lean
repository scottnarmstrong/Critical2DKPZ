/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.MeasureKernels
public import Critical2DKPZ.RandomMeasure.GeneralRandom
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-! # Measurability of integrals against almost surely locally finite measures -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Tsai
open scoped ENNReal

namespace Critical2DKPZ.NonGaussian

/-- Integrating a jointly measurable nonnegative function against an almost surely locally finite
random measure gives an almost-everywhere measurable function. -/
theorem aemeasurable_lintegral_locallyFinite_randomMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : Ω → Measure (Plane × Plane)) (hB : Measurable B)
    (hBLF : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (B ω))
    (H : Ω → (Plane × Plane) → ℝ≥0∞) (hH : Measurable (Function.uncurry H)) :
    AEMeasurable (fun ω => ∫⁻ z, H ω z ∂B ω) P := by
  let E : CompactExhaustion (Plane × Plane) := RandomMeasure.vagueCompactExhaustion (Plane × Plane)
  let M : Ω → Measure (Plane × Plane) := RandomMeasure.locallyFiniteMeasureModification E B
  have hM : Measurable M := RandomMeasure.measurable_locallyFiniteMeasureModification E B hB
  let κ : Kernel Ω (Plane × Plane) := ⟨M, hM⟩
  let : IsSFiniteKernel κ := isSFiniteKernel_of_locallyFinite κ
    (RandomMeasure.locallyFinite_locallyFiniteMeasureModification E B)
  have hMeas : Measurable (fun ω => ∫⁻ z, H ω z ∂M ω) :=
    hH.lintegral_kernel_prod_right (κ := κ)
  apply hMeas.aemeasurable.congr
  filter_upwards [hBLF] with ω hω
  exact congrArg (fun μ : Measure (Plane × Plane) => ∫⁻ z, H ω z ∂μ)
    (RandomMeasure.locallyFiniteMeasureModification_apply_of_isLocallyFinite E B ω hω)

/-- A nonnegative integral against an almost surely locally finite random measure
is almost-everywhere measurable when its integrand also depends measurably on a random parameter. -/
theorem aemeasurable_lintegral_locallyFinite_randomMeasure_parameter {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) (X : Ω → A) (hX : Measurable X)
    (B : Ω → Measure (Plane × Plane)) (hB : Measurable B)
    (hBLF : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (B ω))
    (H : A → (Plane × Plane) → ℝ≥0∞) (hH : Measurable (Function.uncurry H)) :
    AEMeasurable (fun ω => ∫⁻ z, H (X ω) z ∂B ω) P := by
  have hJoint : Measurable (fun q : Ω × (Plane × Plane) => H (X q.1) q.2) :=
    hH.comp ((hX.comp measurable_fst).prodMk measurable_snd)
  exact aemeasurable_lintegral_locallyFinite_randomMeasure P B hB hBLF
    (fun ω z => H (X ω) z) hJoint

end Critical2DKPZ.NonGaussian

end
