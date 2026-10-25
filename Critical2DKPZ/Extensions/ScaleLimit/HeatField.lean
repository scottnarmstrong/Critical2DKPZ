/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.Blocks
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Critical2DKPZ.CovarianceKernel.PointwiseMoments
import Critical2DKPZ.Assembly.Final
import Critical2DKPZ.SHF.Positivity.HeatPairingEhrhard

/-! # Measurability and integrability of the heat-start field

The field is used only on the classical domain `0 < δ < 1`.
-/

@[expose] public section

open MeasureTheory
open scoped BoundedContinuousFunction ENNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The heat-start logarithm is a.e. measurable at every admissible width. -/
theorem aemeasurable_Fheat (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (x : Plane) :
    AEMeasurable (Fheat Z δ x) P := by
  have hh := SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType
    ϑ P Z hZ δ 1 δ x (0 : Plane →ᵇ ℝ) hδ.le hδ1 hδ
  change AEMeasurable (fun ω => Real.log (shfPairing Z δ 1
    (fun y => heatKernel δ (y - x)) (fun _ => 1) ω)) P
  simpa only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] using hh.2.1

/-- The heat-start logarithm has an integrable square at every admissible width. -/
theorem memLp_Fheat_two (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (x : Plane) : MemLp (Fheat Z δ x) 2 P := by
  exact CovarianceKernel.log_heatStartPairing_memLp_two_of ϑ P Z hZ
    (Assembly.shfSymmetriesAt ϑ P Z hZ) hδ.le hδ1 hδ x

/-- In particular every admissible heat-start logarithm is integrable. -/
theorem integrable_Fheat (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (x : Plane) : Integrable (Fheat Z δ x) P :=
  (memLp_Fheat_two ϑ P Z hZ δ hδ hδ1 x).integrable one_le_two

end Critical2DKPZ.Extensions.ScaleLimit
