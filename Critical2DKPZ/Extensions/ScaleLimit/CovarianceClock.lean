/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.Centring
public import Critical2DKPZ.Extensions.ScaleLimit.PathApi
import Critical2DKPZ.Provider.CriticalKPZCovarianceKernel
import Critical2DKPZ.SmallScales.DeterministicComparison
import Critical2DKPZ.Spectral.BochnerSchwartz

/-!
# Covariance on the doubly logarithmic scale

The change of variables and uniform density estimates used in Proposition 5.1.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped Topology BoundedContinuousFunction ENNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Change variables in both tests of a locally square-integrable kernel. -/
theorem integral_dilate_pair (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (φ ψ : TestFn) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : Plane) :
    (∫ p : Plane × Plane, φ.dilate a x p.1 * ψ.dilate b x p.2 * C (p.1 - p.2)) =
      ∫ u, ∫ v, φ u * ψ v * C (a • u - b • v) := by
  have hint : Integrable (fun p : Plane × Plane =>
      φ.dilate a x p.1 * ψ.dilate b x p.2 * C (p.1 - p.2)) (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using
      Spectral.integrable_testFnProduct_kernel C hC (φ.dilate a x) (ψ.dilate b x)
  calc
    _ = ∫ y, ∫ z, φ.dilate a x y * ψ.dilate b x z * C (y - z) := by
      rw [Measure.volume_eq_prod]
      exact integral_prod _ hint
    _ = ∫ y, φ.dilate a x y * (∫ z, ψ.dilate b x z * C (y - z)) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with z
      exact mul_assoc _ _ _
    _ = ∫ u, φ u * (∫ z, ψ.dilate b x z * C (x + a • u - z)) :=
      SmallScales.integral_testFn_dilate_mul φ ha x _
    _ = ∫ u, ∫ v, φ u * ψ v * C (a • u - b • v) := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [SmallScales.integral_testFn_dilate_mul ψ hb x, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with v
      have heq : x + a • u - (x + b • v) = a • u - b • v := by abel
      rw [heq, mul_assoc]

/-- The covariance kernel represents all pairs of dilated tests in fixed coordinates. -/
theorem exists_covariance_dilate_representation (ϑ : ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) :
    ∃ C : Plane → ℝ, (∀ z, 0 ≤ C z) ∧
      (∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K)) ∧
      ContinuousOn C {0}ᶜ ∧
      (∀ (φ ψ : TestFn) (a b : ℝ) (x : Plane), 0 < a → 0 < b →
        cov[fun ω => H t 0 ω (φ.dilate a x), fun ω => H t 0 ω (ψ.dilate b x); P] =
          ∫ u, ∫ v, φ u * ψ v * C (a • u - b • v)) ∧
      Tendsto (fun z => C z / Real.log (Real.log ‖z‖⁻¹))
        (nhdsWithin 0 {0}ᶜ) (𝓝 1) := by
  obtain ⟨C, hpos, _hrad, hloc, hcont, hcov, hlim⟩ :=
    Critical2DKPZ.Provider.criticalKPZ_covarianceKernel ϑ P Z hZ H hH t ht
  refine ⟨C, hpos, hloc, hcont, ?_, hlim⟩
  intro φ ψ a b x ha hb
  rw [hcov]
  exact integral_dilate_pair C hloc φ ψ ha hb x

/-- Density of `U - ρV` when the independent variables have densities `φ, ψ`. -/
def subDensity (φ ψ : TestFn) (ρ : ℝ) (w : Plane) : ℝ :=
  ∫ v, φ (w + ρ • v) * ψ v

/-- The translated product defining the difference density is integrable. -/
theorem integrable_subDensity_integrand (φ ψ : TestFn) (ρ : ℝ) (w : Plane) :
    Integrable (fun v => φ (w + ρ • v) * ψ v) := by
  have hf : Continuous (fun v : Plane => φ (w + ρ • v) * ψ v) := by
    exact (φ.continuous.comp (continuous_const.add ((continuous_const : Continuous (fun _ : Plane => ρ)).smul
      (continuous_id : Continuous (fun v : Plane => v))))).mul ψ.continuous
  have hs : HasCompactSupport (fun v : Plane => φ (w + ρ • v) * ψ v) :=
    ψ.hasCompactSupport.mul_left
  exact hf.integrable_of_hasCompactSupport hs

/-- Difference densities are nonnegative for nonnegative tests. -/
theorem subDensity_nonneg (φ ψ : TestFn)
    (hφ : ∀ u, 0 ≤ φ u) (hψ : ∀ v, 0 ≤ ψ v) (ρ : ℝ) (w : Plane) :
    0 ≤ subDensity φ ψ ρ w :=
  integral_nonneg fun v => mul_nonneg (hφ _) (hψ v)

/-- The density is bounded independently of the relative width. -/
theorem density_sub_bound (φ ψ : TestFn) (hψ : ∀ v, 0 ≤ ψ v) (ρ : ℝ) (w : Plane) :
    subDensity φ ψ ρ w ≤ ‖(φ : Plane →ᵇ ℝ)‖ * (∫ v, ψ v) := by
  rw [subDensity, ← integral_const_mul]
  apply integral_mono (integrable_subDensity_integrand φ ψ ρ w)
    ((ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).const_mul _)
  intro v
  apply mul_le_mul_of_nonneg_right _ (hψ v)
  calc
    φ (w + ρ • v) ≤ ‖φ (w + ρ • v)‖ := le_abs_self _
    _ ≤ ‖(φ : Plane →ᵇ ℝ)‖ := BoundedContinuousFunction.norm_coe_le_norm (φ : Plane →ᵇ ℝ) (w + ρ • v)

/-- Relative widths in `[0,1]` give difference densities supported in one fixed ball. -/
theorem exists_subDensity_support_radius (φ ψ : TestFn) :
    ∃ K : ℝ, 0 < K ∧ ∀ ρ ∈ Set.Icc (0 : ℝ) 1, ∀ w : Plane,
      K < ‖w‖ → subDensity φ ψ ρ w = 0 := by
  obtain ⟨R, hR, hφ⟩ := φ.hasCompactSupport.isCompact.isBounded.exists_pos_norm_lt
  obtain ⟨S, hS, hψ⟩ := ψ.hasCompactSupport.isCompact.isBounded.exists_pos_norm_lt
  refine ⟨R + S, add_pos hR hS, ?_⟩
  intro ρ hρ w hw
  apply integral_eq_zero_of_ae
  filter_upwards [] with v
  by_cases hv : ψ v = 0
  · exact mul_eq_zero_of_right _ hv
  · have hvS : ‖v‖ < S := hψ _ (subset_tsupport ψ hv)
    have hz : φ (w + ρ • v) = 0 := by
      by_contra hz
      have hzR : ‖w + ρ • v‖ < R := hφ _ (subset_tsupport φ hz)
      have hn : ‖ρ • v‖ ≤ ‖v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ.1]
        exact mul_le_of_le_one_left (norm_nonneg _) hρ.2
      have htriangle : ‖w‖ ≤ ‖w + ρ • v‖ + ‖ρ • v‖ := by
        simpa only [add_sub_cancel_right] using norm_sub_le (w + ρ • v) (ρ • v)
      have hbound : ‖w‖ < R + S :=
        htriangle.trans_lt (add_lt_add hzR (hn.trans_lt hvS))
      exact (not_lt_of_ge hw.le) hbound
    exact mul_eq_zero_of_left hz _

end Critical2DKPZ.Extensions.ScaleLimit
