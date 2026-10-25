/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.Inputs
public import Critical2DKPZ.JointConvergence.HeatStartLogConvergence
public import Critical2DKPZ.JointConvergence.HeatStartLogFieldAssembly
public import Critical2DKPZ.SHF.Positivity.BoundedPairingConvergence
public import Critical2DKPZ.SHF.Positivity.HeatPairingEhrhard

/-! # Fixed-width heat-start convergence at every critical SHF

Bounded heat-pairing convergence and positivity yield the joint logarithm
convergence `HeatStartLogAt` and its spatially tested form `HeatStartLogFieldAt`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter ProbabilityTheory

universe u

namespace Critical2DKPZ.Assembly

open Critical2DKPZ.LocalSobolev

/-- Joint convergence of heat-start logarithms at fixed positive widths, from
bounded pairing convergence and positivity. -/
theorem heatStartLogAt_of_isCriticalSHF (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) : HeatStartLogAt ϑ P Z :=
  fun T h₀ k s δ x hs =>
    JointConvergence.heatStart_log_tendsto_of ϑ P Z hZ
      (fun hs hst hδ x g =>
        SHF.Positivity.isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hs hst hδ x g)
      (fun k s t δ x g h =>
        SHF.Positivity.isCriticalSHF_heat_bounded_pairing_joint ϑ P Z hZ k s t δ x g h)
      (fun s t δ x h₀ hs hst hδ =>
        ⟨(SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType ϑ P Z hZ s t δ x h₀ hs hst
            hδ).1,
          (SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType ϑ P Z hZ s t δ x h₀ hs hst
            hδ).2.1⟩)
      T h₀ k s δ x hs

/-- Spatially tested heat-start logarithm convergence at fixed positive widths,
from bounded pairing convergence and positivity. -/
theorem heatStartLogFieldAt_of_isCriticalSHF (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) : HeatStartLogFieldAt ϑ P Z :=
  fun T k h₀ s δ φ hs =>
    JointConvergence.heatStart_logField_tendsto_of ϑ P Z hZ
      (fun hs hst hδ x g =>
        SHF.Positivity.isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hs hst hδ x g)
      (fun k s t δ x g h =>
        SHF.Positivity.isCriticalSHF_heat_bounded_pairing_joint ϑ P Z hZ k s t δ x g h)
      (fun s t δ x h₀ hs hst hδ =>
        ⟨(SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType ϑ P Z hZ s t δ x h₀ hs hst
            hδ).1,
          (SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType ϑ P Z hZ s t δ x h₀ hs hst
            hδ).2.1⟩)
      T k h₀ s δ φ hs

end Critical2DKPZ.Assembly

end

end
