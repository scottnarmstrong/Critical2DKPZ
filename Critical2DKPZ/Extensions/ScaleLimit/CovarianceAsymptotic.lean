/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.KernelClock

/-! # Uniform diagonal covariance asymptotics for arbitrary critical KPZ fields -/

public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The covariance asymptotic is uniform over all smaller second widths. -/
theorem covariance_diagonal_asymptotic (ϑ : ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) (φ ψ : TestFn)
    (hφ : ∀ u, 0 ≤ φ u) (hψ : ∀ v, 0 ≤ ψ v)
    (hφmass : (∫ u, φ u) = 1) (hψmass : (∫ v, ψ v) = 1) (x : Plane)
    {η : ℝ} (hη : 0 < η) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a ∈ Set.Ioc (0 : ℝ) a₀, ∀ b ∈ Set.Ioc (0 : ℝ) a,
      |cov[fun ω => H t 0 ω (φ.dilate a x), fun ω => H t 0 ω (ψ.dilate b x); P] /
        Real.log (Real.log a⁻¹) - 1| ≤ η := by
  obtain ⟨C, _hpos, hloc, _hcont, hcov, hlim⟩ :=
    exists_covariance_dilate_representation ϑ P Z hZ H hH t ht
  obtain ⟨a₀, ha₀, hbound⟩ := kernel_clock_diagonal_asymptotic C hloc hlim
    φ ψ hφ hψ hφmass hψmass hη
  refine ⟨a₀, ha₀, ?_⟩
  intro a ha b hb
  have hρ : b / a ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hb.1.le ha.1.le, (div_le_one ha.1).mpr hb.2⟩
  have hid : a * (b / a) = b := by field_simp [ha.1.ne']
  have heq : (∫ u, ∫ v, φ u * ψ v * C (a • (u - (b / a) • v))) =
      ∫ u, ∫ v, φ u * ψ v * C (a • u - b • v) := by
    apply integral_congr_ae
    filter_upwards [] with u
    apply integral_congr_ae
    filter_upwards [] with v
    rw [smul_sub, smul_smul, hid]
  rw [hcov φ ψ a b x ha.1 hb.1]
  simpa only [heq] using hbound a ha (b / a) hρ

end Critical2DKPZ.Extensions.ScaleLimit
