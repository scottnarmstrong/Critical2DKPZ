/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.Response.TimeContinuity
import Mathlib.Tactic

/-! # Scalar spatial identification for critical KPZ fields

The time-`t` spatial smoothing is the temporal regularization at `t + r`.
Uniform approximation and time continuity identify its tested limit. This
proves the scalar consequence of BCC Corollary 6.2 used in the response theorem.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped BoundedContinuousFunction ENNReal Topology
namespace Critical2DKPZ.Extensions.Response

/-- Temporal approximation remains valid along the shifted time `t + r`. -/
theorem tendsto_eLpNorm_shifted_approximation (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) (h : Plane →ᵇ ℝ) (ψ : TestFn) :
    Tendsto (fun r => eLpNorm (fun ω =>
      (∫ x, ψ x * kpzRegularized P Z (t + r) r h x ω) - H (t + r) h ω ψ) 2 P)
      (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_zero_of_real_bounds
  intro ε hε
  obtain ⟨d, hd, hb⟩ := kpzRegularized_uniform_L2_rate ϑ P Z hZ H hH h ψ ht
    (show t ≤ t + 1 by linarith) ε hε
  have hrpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  have hrd : ∀ᶠ r : ℝ in 𝓝[>] 0, r < d := nhdsWithin_le_nhds (Iio_mem_nhds hd)
  have hrone : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 := nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  filter_upwards [hrpos, hrd, hrone] with r hr hrd hrone
  exact hb r hr hrd (t + r) (by linarith) (by linarith)

/-- The tested spatially smoothed field converges in L¹ to any critical KPZ version. -/
theorem tendsto_eLpNorm_spatialCenteredPairing (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) (h : Plane →ᵇ ℝ) (ψ : TestFn) :
    Tendsto (fun r => eLpNorm (fun ω => spatialCenteredPairing P Z t r h ψ ω - H t h ω ψ) 1 P)
      (𝓝[>] 0) (𝓝 0) := by
  have happrox : Tendsto (fun r => eLpNorm (fun ω =>
      (∫ x, ψ x * kpzRegularized P Z (t + r) r h x ω) - H (t + r) h ω ψ) 1 P) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_eLpNorm_shifted_approximation ϑ P Z hZ H hH t ht h ψ)
      (fun _ => zero_le) (fun _ => eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))
  have hshift₀ : Tendsto (fun r : ℝ => t + r) (𝓝 (0 : ℝ)) (𝓝 t) := by
    have hc : Continuous (fun r : ℝ => t + r) := continuous_const.add continuous_id
    simpa only [add_zero] using hc.tendsto (0 : ℝ)
  have hshift : Tendsto (fun r : ℝ => t + r) (𝓝[>] 0) (𝓝 t) :=
    hshift₀.mono_left nhdsWithin_le_nhds
  have htime := (tendsto_eLpNorm_H_time ϑ P Z hZ H hH t ht h ψ).comp hshift
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [add_zero] using happrox.add htime) (fun _ => zero_le) ?_
  intro r
  dsimp only [Function.comp_def]
  rw [show (fun ω => spatialCenteredPairing P Z t r h ψ ω - H t h ω ψ) =
      (fun ω => ((∫ x, ψ x * kpzRegularized P Z (t + r) r h x ω) - H (t + r) h ω ψ) +
        (H (t + r) h ω ψ - H t h ω ψ)) by
    funext ω
    rw [spatialCenteredPairing_eq_integral_kpzRegularized]
    ring]
  exact eLpNorm_add_le (by norm_num)

/-- Scalar spatial identification: smoothing the position at time `t` gives the
same tested critical KPZ field as temporal regularization in the small-width limit. -/
theorem spatial_centered_pairing_tendstoInMeasure (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) (h : Plane →ᵇ ℝ) (ψ : TestFn) :
    TendstoInMeasure P (fun r ω => spatialCenteredPairing P Z t r h ψ ω)
      (𝓝[>] 0) (fun ω => H t h ω ψ) := by
  exact tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0)
    (tendsto_eLpNorm_spatialCenteredPairing ϑ P Z hZ H hH t ht h ψ)

end Critical2DKPZ.Extensions.Response
