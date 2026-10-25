/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.Response.TildeH
public import Critical2DKPZ.Extensions.Response.CutoffGood
public import Critical2DKPZ.Extensions.Definitions.ResponseCutoff
public import Critical2DKPZ.Assembly.Final
import Critical2DKPZ.JointConvergence.LogHeatFieldMeasurability
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Measurability and centring for terminally smoothed KPZ responses -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped BoundedContinuousFunction ENNReal Topology
namespace Critical2DKPZ.Extensions.Response

/-- Endpoint swapping preserves local finiteness. -/
theorem locallyFinite_map_prodSwap {μ : Measure (Plane × Plane)}
    (hμ : IsLocallyFiniteMeasure μ) : IsLocallyFiniteMeasure (μ.map Prod.swap) := by
  let : IsLocallyFiniteMeasure μ := hμ
  exact SHF.Symmetries.locallyFinite_map_homeomorph (Homeomorph.prodComm Plane Plane) μ

/-- The heat-end logarithm is jointly measurable in spatial centre and realization. -/
theorem aemeasurable_log_cutoffPairing_joint (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (g : Plane → ℝ)
    (hg : Measurable g) (hgn : ∀ y, 0 ≤ g y) :
    AEMeasurable (fun q : Plane × Ω => Real.log (shfPairing Z 0 t g
      (fun y => heatKernel r (y - q.1)) q.2)) (volume.prod P) := by
  let S : Ω → Measure (Plane × Plane) := fun ω => (Z 0 t ω).map Prod.swap
  have hS : Measurable S :=
    (Measure.measurable_map Prod.swap measurable_swap).comp (hZ.1 0 t le_rfl ht)
  have hlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (S ω) := by
    filter_upwards [hZ.2.1 0 t le_rfl ht] with ω hω
    exact locallyFinite_map_prodSwap hω.1
  have hm := JointConvergence.aemeasurable_log_heatPairing_joint P S hS hlocal r hr g hg hgn
  refine hm.congr (Eventually.of_forall fun q => ?_)
  have hk : Measurable (fun p : Plane × Plane => heatKernel r (p.1 - q.1) * g p.2) :=
    ((measurable_heatKernel r).comp (measurable_fst.sub_const q.1)).mul (hg.comp measurable_snd)
  have heq : (∫ p, heatKernel r (p.1 - q.1) * g p.2 ∂S q.2) =
      shfPairing Z 0 t g (fun y => heatKernel r (y - q.1)) q.2 := by
    have hi := integral_map (μ := Z 0 t q.2) measurable_swap.aemeasurable hk.aestronglyMeasurable
    simpa only [S, shfPairing, Prod.swap, mul_comm] using hi
  exact congrArg Real.log heq


/-- Every fixed cutoff response is almost everywhere measurable. The product integral
argument applies directly to the two jointly measurable logarithms. -/
theorem aemeasurable_responseCutoff (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r)
    (h v : Plane →ᵇ ℝ) (ψ : TestFn) (q : ℝ) :
    AEMeasurable (fun ω => responseCutoff Z t r h v ψ ω q) P := by
  have hq := aemeasurable_log_cutoffPairing_joint ϑ P Z hZ ht hr
    (fun y => Real.exp (h y + q * v y)) (by fun_prop) (fun y => (Real.exp_pos _).le)
  have h0 := aemeasurable_log_cutoffPairing_joint ϑ P Z hZ ht hr
    (fun y => Real.exp (h y)) (by fun_prop) (fun y => (Real.exp_pos _).le)
  have hψ : AEStronglyMeasurable (fun p : Plane × Ω => ψ p.1) (volume.prod P) :=
    (ψ.continuous.measurable.comp measurable_fst).aestronglyMeasurable
  exact (hψ.mul (hq.aestronglyMeasurable.sub h0.aestronglyMeasurable)).prod_swap.integral_prod_right'.aemeasurable


/-- Tested logarithms for every bounded initial profile are integrable on one event.
In particular this event works for all real response parameters simultaneously. -/
theorem ae_integrable_testFn_mul_log_cutoffPairing (ϑ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (ψ : TestFn) :
    ∀ᵐ ω ∂P, ∀ h : Plane →ᵇ ℝ,
      Integrable (fun x => ψ x * Real.log (shfPairing Z 0 t
        (fun y => Real.exp (h y)) (fun y => heatKernel r (y - x)) ω)) := by
  filter_upwards [ae_integrable_heat_end ϑ P Z hZ ht (by positivity : 0 < 2 * r) 0,
    ae_heat_end_pos ϑ P Z hZ ht hr] with ω hint hpos
  have hint' : Integrable (fun p : Plane × Plane => heatKernel (2 * r) p.2) (Z 0 t ω) := by
    simpa only [sub_zero] using hint
  have hpos' : 0 < ∫ p, heatKernel r p.2 ∂(Z 0 t ω) := by
    simpa only [shfPairing, one_mul] using hpos
  intro h
  exact integrable_testFn_mul_log_pairing hr hint' hpos'
    (Real.continuous_exp.comp h.continuous) (exp_profile_bound h) (fun y => Real.exp_pos _) ψ

/-- Algebraic cancellation of the common centring, with the integrability conditions
needed for Bochner integral subtraction stated explicitly. -/
theorem responseCutoff_eq_sub_spatialCentered_of_integrable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t r : ℝ)
    (h v : Plane →ᵇ ℝ) (ψ : TestFn) (ω : Ω) (q : ℝ)
    (hq : Integrable (fun x => ψ x * Real.log (shfPairing Z 0 t
      (fun y => Real.exp (h y + q * v y)) (fun y => heatKernel r (y - x)) ω)))
    (h0 : Integrable (fun x => ψ x * Real.log (shfPairing Z 0 t
      (fun y => Real.exp (h y)) (fun y => heatKernel r (y - x)) ω))) :
    responseCutoff Z t r h v ψ ω q =
      spatialCenteredPairing P Z t r (h + q • v) ψ ω - spatialCenteredPairing P Z t r h ψ ω := by
  let c := ∫ ω', Real.log (shfPairing Z 0 t (fun _ => 1) (heatKernel r) ω') ∂P
  have hc : Integrable (fun x => ψ x * c) :=
    (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).mul_const c
  have hprofile : (fun y => Real.exp ((h + q • v) y)) = fun y => Real.exp (h y + q * v y) := by
    funext y
    simp
  simp only [responseCutoff, spatialCenteredPairing, hprofile, mul_sub]
  rw [integral_sub hq h0, integral_sub hq hc, integral_sub h0 hc]
  ring

end Critical2DKPZ.Extensions.Response
