/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.EndpointMomentIntegration
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-! # Endpoint pairings of volume-equivalent tests

Absolute continuity of the first endpoint moment measure gives almost-sure equality of
endpoint pairings for volume-equivalent tests.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Volume-equivalent endpoint tests have equal pairings almost surely when the first tuple mean is absolutely continuous. -/
theorem ae_integral_congr_of_endpointTuple_mean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Ω → Measure (Plane × Plane)) (hCm : Measurable C)
    (hClf : ∀ ω, IsLocallyFiniteMeasure (C ω))
    (ν : Measure (Configuration 1 × Configuration 1))
    (hmean : P.bind (fun ω => endpointTupleMeasure (fun _ : Fin 1 => C ω)) = ν)
    (hAC : ν ≪ volume) (F G : Plane × Plane → ℝ) (hFG : F =ᵐ[volume] G) :
    (fun ω => ∫ p, F p ∂C ω) =ᵐ[P] fun ω => ∫ p, G p ∂C ω := by
  let e := MeasurableEquiv.piUnique (fun _ : Fin 1 => Plane)
  have he : MeasurePreserving e (volume : Measure (Configuration 1)) (volume : Measure Plane) :=
    volume_preserving_piUnique (fun _ : Fin 1 => Plane)
  have hp := (he.prod he).quasiMeasurePreserving.ae hFG
  have hdef : (default : Fin 1) = 0 := Subsingleton.elim _ _
  have hp' : (fun q : Configuration 1 × Configuration 1 => F (q.1 0, q.2 0)) =ᵐ[volume.prod volume]
      fun q => G (q.1 0, q.2 0) := by
    filter_upwards [hp] with q hq
    simpa only [e, MeasurableEquiv.piUnique, Equiv.piUnique, MeasurableEquiv.coe_mk,
      Equiv.coe_fn_mk, hdef, Prod.map] using hq
  have hH : (fun q : Configuration 1 × Configuration 1 => F (q.1 0, q.2 0)) =ᵐ[ν]
      fun q => G (q.1 0, q.2 0) := by
    apply hAC.ae_eq
    simpa only [Measure.volume_eq_prod] using hp'
  let κ : Kernel Ω (Configuration 1 × Configuration 1) :=
    ⟨fun ω => endpointTupleMeasure (fun _ : Fin 1 => C ω),
      measurable_endpointTupleMeasure (fun _ => C) (fun _ => hCm) (fun _ => hClf)⟩
  have hκmean : κ ∘ₘ P = ν := by
    simpa only [κ, Kernel.coe_mk] using hmean
  have hHcomp : ∀ᵐ q ∂(κ ∘ₘ P), F (q.1 0, q.2 0) = G (q.1 0, q.2 0) := by
    rw [hκmean]
    exact hH
  have hrows := Measure.ae_ae_of_ae_comp hHcomp
  filter_upwards [hrows] with ω hω
  let : IsLocallyFiniteMeasure (C ω) := hClf ω
  have hInt := integral_congr_ae hω
  have hF := integral_endpointTupleMeasure_prod (fun _ : Fin 1 => C ω) (fun _ => F)
  have hG := integral_endpointTupleMeasure_prod (fun _ : Fin 1 => C ω) (fun _ => G)
  simp only [Fin.prod_univ_one] at hF hG
  exact hF.symm.trans (hInt.trans hG)

end Critical2DKPZ.SHF.Tsai

end
