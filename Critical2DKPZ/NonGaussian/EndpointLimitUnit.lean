/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.EndpointLimitLogBridge
import Mathlib.Tactic

/-! # Concentration for unit-bounded compact endpoint tests -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.LocalSobolev
open scoped BoundedContinuousFunction CompactlySupported Distributions ENNReal Topology

universe u

namespace Critical2DKPZ.NonGaussian

/-- Vanishing logarithmic perturbations imply concentration of averaged endpoint pairings against compact terminal tests bounded in absolute value by one. -/
theorem endpointPairing_average_concentrates_unit_of_log_perturbation
    (hPerturb : ∀ (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (_hZ : IsCriticalSHF ϑ P Z)
      (_hsym : ShfSymmetriesAt ϑ P Z) (_hC12 : ToyJointAt ϑ P Z) (_hHeatStartLogInput : HeatStartLogAt ϑ P Z) (_hHeatStartLogFieldInput : HeatStartLogFieldAt ϑ P Z)
      (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (_hH : IsCriticalKPZ P Z H) {t : ℝ} (_ht : 0 < t)
      (ψ : TestFn) (_hψ : ∀ x, 0 ≤ ψ x) (_hψ₁ : ∫ x, ψ x = 1)
      (_hG : ∃ (m : ℝ) (v : NNReal), P.map (fun ω => H t 0 ω ψ) = gaussianReal m v)
      (f : Plane →ᵇ ℝ) {c : ℝ} (_hc : 0 < c) (_hf : ∀ y, c ≤ f y) (p : ℝ≥0∞) (_hp : p ≠ ⊤),
      Tendsto (fun r => eLpNorm (fun ω => avgLogField P Z r t ψ f ω -
          avgLogField P Z r t ψ (fun _ => 1) ω) p P) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
    (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hC12 : ToyJointAt ϑ P Z) (hHeatStartLogInput : HeatStartLogAt ϑ P Z) (hHeatStartLogFieldInput : HeatStartLogFieldAt ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H) {t : ℝ} (ht : 0 < t)
    (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x) (hψ₁ : ∫ x, ψ x = 1)
    (hG : ∃ (m : ℝ) (v : NNReal), P.map (fun ω => H t 0 ω ψ) = gaussianReal m v)
    (φ : C_c(Plane, ℝ)) (hφ : ∀ y, |φ y| ≤ 1) :
    Tendsto (fun r => ∫ ω, |(∫ x, ψ x * endpointPairing Z r t x φ ω) -
        ∫ ω', (∫ x, ψ x * endpointPairing Z r t x φ ω') ∂P| ∂P) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  let ρ : Measure Plane := volume.withDensity (fun x => ENNReal.ofReal (ψ x))
  let : IsProbabilityMeasure ρ := by
    constructor
    change volume.withDensity (fun x => ENNReal.ofReal (ψ x)) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal
        (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport)
        (Filter.Eventually.of_forall hψ), hψ₁, ENNReal.ofReal_one]
  let K (r : ℝ) (hv : 0 < r ∧ r < t) :=
    endpointMeasureKernel (Z r t) (hZ.1 r t hv.1.le hv.2) r hv.1
  let X : ℝ → Ω → ℝ := fun r ω => ∫ x, ψ x * endpointPairing Z r t x φ ω
  let Y : ℝ → ℝ → Ω → ℝ := fun e r =>
    if hv : 0 < r ∧ r < t then endpointKernelLogApprox (K r hv) ρ e φ else fun _ => 0
  have hpos : ∀ᶠ r in l, 0 < r := self_mem_nhdsWithin
  have hlt : ∀ᶠ r in l, r < t := (gt_mem_nhds ht).filter_mono nhdsWithin_le_nhds
  have hvalid : ∀ᶠ r in l, 0 < r ∧ r < t := Filter.Eventually.and hpos hlt
  have hY (e r : ℝ) (hv : 0 < r ∧ r < t) :
      Y e r = endpointKernelLogApprox (K r hv) ρ e φ := dite_eq_left hv
  have hA (r : ℝ) (hv : 0 < r ∧ r < t) :
      endpointKernelAverage (K r hv) ρ φ =ᵐ[P] X r :=
    endpointKernelAverage_eq_endpointPairing_ae ϑ P Z hZ hv.1 hv.2 ψ hψ φ
  have hlin (r : ℝ) (hv : 0 < r ∧ r < t) (e : ℝ) (he : 0 < e) (hehalf : e ≤ 1 / 2) :=
    endpoint_kernel_log_linearization P ρ (K r hv)
      (endpointMeasureKernel_mass_le_one (Z r t) (hZ.1 r t hv.1.le hv.2) r hv.1)
      φ hφ he hehalf
  have hXi : ∀ᶠ r in l, Integrable (X r) P := by
    filter_upwards [hvalid] with r hv
    exact (hlin r hv (1 / 4) (by norm_num) (by norm_num)).1.congr (hA r hv)
  have hYi (e : ℝ) (he : 0 < e) (hehalf : e ≤ 1 / 2) :
      ∀ᶠ r in l, Integrable (Y e r) P := by
    filter_upwards [hvalid] with r hv
    rw [hY e r hv]
    exact (hlin r hv e he hehalf).2.1
  have happ (e : ℝ) (he : 0 < e) (hehalf : e ≤ 1 / 2) :
      ∀ᶠ r in l, ∀ᵐ ω ∂P, |X r ω - Y e r ω| ≤ 2 * e := by
    filter_upwards [hvalid] with r hv
    rw [hY e r hv]
    filter_upwards [hA r hv] with ω hω
    change endpointKernelAverage (K r hv) ρ φ ω = X r ω at hω
    rw [← hω]
    exact (hlin r hv e he hehalf).2.2 ω
  have hYconc (e : ℝ) (he : 0 < e) (hehalf : e ≤ 1 / 2) :
      Tendsto (fun r => ∫ ω, |Y e r ω - ∫ ω', Y e r ω' ∂P| ∂P) l (𝓝 0) := by
    let f : Plane →ᵇ ℝ := 1 + e • ofCompactSupport φ φ.continuous φ.hasCompactSupport
    have hf (y : Plane) : 1 / 2 ≤ f y := by
      have hlo := mul_le_mul_of_nonneg_left (abs_le.mp (hφ y)).1 he.le
      change 1 / 2 ≤ 1 + e * φ y
      linarith only [hlo, hehalf]
    let L : ℝ → Ω → ℝ := fun r ω => avgLogField P Z r t ψ f ω -
      avgLogField P Z r t ψ (fun _ => 1) ω
    have hn : Tendsto (fun r => eLpNorm (L r) 1 P) l (𝓝 0) :=
      hPerturb ϑ P Z hZ hsym hC12 hHeatStartLogInput hHeatStartLogFieldInput H hH ht ψ hψ hψ₁ hG f
        (by norm_num : (0 : ℝ) < 1 / 2) hf 1 (by norm_num)
    have hs := (tendsto_integral_abs_of_eLpNorm_one P l L hn).const_mul e⁻¹
    simp only [mul_zero] at hs
    apply hs.congr'
    filter_upwards [hvalid] with r hv
    have hb := endpointKernelLogApprox_centered_eq_avgLogField
      ϑ P Z hZ hsym hv.1 hv.2 ψ hψ φ hφ he hehalf
    change (fun ω => endpointKernelLogApprox (K r hv) ρ e φ ω -
      ∫ ω', endpointKernelLogApprox (K r hv) ρ e φ ω' ∂P) =ᵐ[P]
        fun ω => e⁻¹ * L r ω at hb
    have heq : (∫ ω, |Y e r ω - ∫ ω', Y e r ω' ∂P| ∂P) =
        e⁻¹ * ∫ ω, |L r ω| ∂P := by
      simp_rw [hY e r hv]
      calc
        _ = ∫ ω, |e⁻¹ * L r ω| ∂P :=
          integral_congr_ae (hb.mono fun ω hω => congrArg abs hω)
        _ = e⁻¹ * ∫ ω, |L r ω| ∂P := by
          simp_rw [abs_mul, abs_of_pos (inv_pos.mpr he)]
          exact integral_const_mul _ _
    exact heq.symm
  exact tendsto_integral_abs_centered_of_approximations P l X Y hXi hYi happ hYconc

end Critical2DKPZ.NonGaussian
