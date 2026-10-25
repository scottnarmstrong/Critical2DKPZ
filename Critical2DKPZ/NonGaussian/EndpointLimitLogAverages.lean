/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.EndpointBounds
public import Critical2DKPZ.NonGaussian.EndpointLimitCentering
import Mathlib.Tactic

/-! # Integrability and centering of the logarithmic endpoint fields -/

@[expose] public noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.JointConvergence Critical2DKPZ.SHF.Positivity
open Critical2DKPZ.LocalSobolev
open scoped BoundedContinuousFunction

namespace Critical2DKPZ.NonGaussian

/-- A spatially tested heat-start logarithm is integrable jointly in the
spatial point and the environment. -/
theorem integrable_endpoint_log_field (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) {r t : ℝ} (hr : 0 < r) (hrt : r < t)
    (ψ : TestFn) (h₀ : Plane →ᵇ ℝ) :
    Integrable (fun q : Plane × Ω => ψ q.1 * Real.log (shfPairing Z r t
      (fun y => heatKernel r (y - q.1)) (fun y => Real.exp (h₀ y)) q.2)) (volume.prod P) := by
  have hlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Z r t ω) :=
    (hZ.2.1 r t hr.le hrt).mono fun ω hω => hω.1
  have hG := aemeasurable_log_heatPairing_joint P (Z r t) (hZ.1 r t hr.le hrt)
    hlocal r hr (fun y => Real.exp (h₀ y))
    (Real.continuous_exp.comp h₀.continuous).measurable (fun y => (Real.exp_pos _).le)
  have hsec (x : Plane) : AEStronglyMeasurable (fun ω => Real.log (shfPairing Z r t
      (fun y => heatKernel r (y - x)) (fun y => Real.exp (h₀ y)) ω)) P :=
    (hsym.2.2.2.2.2.2 r t r x h₀ hr.le hrt hr).2.1.aestronglyMeasurable
  obtain ⟨M, hM, hSq⟩ := shf_heatStartLogField_square_bound ϑ P Z hZ
    (isCriticalSHF_heat_bounded_pairing ϑ P Z hZ)
    (isCriticalSHF_heat_bounded_pairing_joint ϑ P Z hZ)
    (fun s t δ x h₀ hs hst hδ =>
      ⟨(hsym.2.2.2.2.2.2 s t δ x h₀ hs hst hδ).1,
        (hsym.2.2.2.2.2.2 s t δ x h₀ hs hst hδ).2.1⟩)
    t h₀ hr.le hrt hr
  exact integrable_test_mul_joint P hG hsec hM hSq ψ

/-- Centering at each spatial point and then averaging agrees with centering
the spatial average, for the heat-start logarithmic fields. -/
theorem avgLogField_exp_eq_centered_average (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) {r t : ℝ} (hr : 0 < r) (hrt : r < t)
    (ψ : TestFn) (h₀ : Plane →ᵇ ℝ) :
    avgLogField P Z r t ψ (fun y => Real.exp (h₀ y)) =ᵐ[P]
      fun ω => (∫ x, ψ x * Real.log (shfPairing Z r t
          (fun y => heatKernel r (y - x)) (fun y => Real.exp (h₀ y)) ω)) -
        ∫ ω', (∫ x, ψ x * Real.log (shfPairing Z r t
          (fun y => heatKernel r (y - x)) (fun y => Real.exp (h₀ y)) ω')) ∂P := by
  let F : Plane × Ω → ℝ := fun q => ψ q.1 * Real.log (shfPairing Z r t
    (fun y => heatKernel r (y - q.1)) (fun y => Real.exp (h₀ y)) q.2)
  have hi : Integrable F (volume.prod P) := integrable_endpoint_log_field ϑ P Z hZ hsym hr hrt ψ h₀
  have heq : avgLogField P Z r t ψ (fun y => Real.exp (h₀ y)) =
      fun ω => ∫ x, (F (x, ω) - ∫ ω', F (x, ω') ∂P) := by
    funext ω
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only [avgLogField, F]
      rw [integral_const_mul]
      ring
  rw [heq]
  exact integral_centered_field_eq_centered_integral volume P hi

end Critical2DKPZ.NonGaussian
