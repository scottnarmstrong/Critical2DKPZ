/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.Inputs
import Critical2DKPZ.JointConvergence.KPZRegularizedReversal
import Critical2DKPZ.JointConvergence.LogHeatFieldMeasurability
import Critical2DKPZ.SHF.Symmetries.DenseTransportHelpers

/-! # Measurability of regularized KPZ test pairings -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

namespace Critical2DKPZ.LocalSobolev

/-- A forward regularized field has an a.e. measurable test-function pairing. The proof writes it
as the integral of a log heat pairing against the reversed SHF measure. -/
theorem aemeasurable_integral_kpzRegularized_of (ϑ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn) :
    AEMeasurable (fun ω => ∫ x, φ x * kpzRegularized P Z t δ h₀ x ω) P := by
  classical
  let W : ℝ → ℝ → Ω → Measure (Plane × Plane) :=
    fun s t' ω => (Z (t - t') (t - s) ω).map Prod.swap
  let μ : Ω → Measure (Plane × Plane) := fun ω => (Z 0 (t - δ) ω).map Prod.swap
  have hμ : Measurable μ :=
    (Measure.measurable_map Prod.swap measurable_swap).comp
      (hZ.1 0 (t - δ) le_rfl (by linarith))
  have hsource : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Z 0 (t - δ) ω) :=
    (hZ.2.1 0 (t - δ) le_rfl (by linarith)).mono fun ω hω => hω.1
  have hlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
    simpa [μ, Homeomorph.prodComm] using
      Critical2DKPZ.SHF.Symmetries.ae_locallyFinite_map_homeomorph
        (Homeomorph.prodComm Plane Plane) P
        (fun ω => Z 0 (t - δ) ω) hsource
  let c : ℝ := ∫ ω', Real.log
    (shfPairing W δ t (fun y => heatKernel δ y) (fun _ => 1) ω') ∂P
  let g : Plane → ℝ := fun y => Real.exp (h₀ y)
  have hg : Measurable g := (Real.continuous_exp.comp h₀.continuous).measurable
  have hgn : ∀ y, 0 ≤ g y := fun y => (Real.exp_pos _).le
  have hameas := JointConvergence.aemeasurable_integral_log_heatPairing
    P μ hμ hlocal δ c hδ g φ hg hgn φ.continuous.measurable
  have hpoint (ω : Ω) (x : Plane) :
      kpzRegularized P Z t δ h₀ x ω =
        Real.log (∫ p, heatKernel δ (p.1 - x) * g p.2 ∂μ ω) - c := by
    have hrev := JointConvergence.kpzRegularized_eq_kpzRegularizedReversed_of_reverseMeasure
      P Z t t δ h₀ x ω
    rw [hrev]
    simp [kpzRegularizedReversed, W, μ, c, g, shfPairing]
  have hEq : (fun ω => ∫ x, φ x * kpzRegularized P Z t δ h₀ x ω) =
      fun ω => ∫ x, φ x *
        (Real.log (∫ p, heatKernel δ (p.1 - x) * g p.2 ∂μ ω) - c) := by
    funext ω
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change φ x * kpzRegularized P Z t δ h₀ x ω = _
      rw [hpoint ω x]
  rw [hEq]
  exact hameas

end Critical2DKPZ.LocalSobolev

end
