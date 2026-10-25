/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.Response.SpatialIdentification
public import Critical2DKPZ.Extensions.Response.CutoffMeasurable
import Mathlib.Tactic

/-! # Centring cancellation and the fixed-parameter response limit

The full-measure integrability event works for every bounded initial profile,
so centring cancellation holds simultaneously for every real parameter.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped BoundedContinuousFunction Topology
namespace Critical2DKPZ.Extensions.Response

/-- The two initial profiles have identical centring. Cancellation holds for
all real response parameters on one full-probability event. -/
theorem responseCutoff_eq_sub_spatialCentered (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (t : ℝ) (ht : 0 < t) (r : ℝ) (hr : 0 < r)
    (h v : Plane →ᵇ ℝ) (ψ : TestFn) :
    ∀ᵐ ω ∂P, ∀ q : ℝ, responseCutoff Z t r h v ψ ω q =
      spatialCenteredPairing P Z t r (h + q • v) ψ ω - spatialCenteredPairing P Z t r h ψ ω := by
  filter_upwards [ae_integrable_testFn_mul_log_cutoffPairing ϑ P Z hZ ht hr ψ] with ω hi
  intro q
  apply responseCutoff_eq_sub_spatialCentered_of_integrable P Z t r h v ψ ω q _ (hi h)
  have hprofile : (fun y => Real.exp ((h + q • v) y)) = fun y => Real.exp (h y + q * v y) := by
    funext y
    simp
  simpa only [hprofile] using hi (h + q • v)

/-- For every fixed real parameter the cutoff response converges in probability
to the difference of the tested critical KPZ fields. -/
theorem responseCutoff_tendstoInMeasure (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) (h v : Plane →ᵇ ℝ) (ψ : TestFn) (q : ℝ) :
    TendstoInMeasure P (fun r ω => responseCutoff Z t r h v ψ ω q) (𝓝[>] 0)
      (fun ω => H t (h + q • v) ω ψ - H t h ω ψ) := by
  have hsub := tendstoInMeasure_sub P
    (spatial_centered_pairing_tendstoInMeasure ϑ P Z hZ H hH t ht (h + q • v) ψ)
    (spatial_centered_pairing_tendstoInMeasure ϑ P Z hZ H hH t ht h ψ)
  have heq : ∀ᶠ r : ℝ in 𝓝[>] 0,
      (fun ω => spatialCenteredPairing P Z t r (h + q • v) ψ ω - spatialCenteredPairing P Z t r h ψ ω) =ᵐ[P]
        (fun ω => responseCutoff Z t r h v ψ ω q) := by
    have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
    filter_upwards [hpos] with r hr
    exact (responseCutoff_eq_sub_spatialCentered ϑ P Z hZ t ht r hr h v ψ).mono fun ω hω => (hω q).symm
  exact TendstoInMeasure.congr' heq Filter.EventuallyEq.rfl hsub

end Critical2DKPZ.Extensions.Response
