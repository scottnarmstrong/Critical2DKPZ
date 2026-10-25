/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.EndpointLimitLogAverages
public import Critical2DKPZ.NonGaussian.EndpointLimitLinearization
public import Critical2DKPZ.NonGaussian.EndpointLimitProfiles
public import Critical2DKPZ.NonGaussian.EndpointLimitPointwise
import Mathlib.Tactic

/-! # Relating endpoint logarithmic approximations to centered log fields -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.JointConvergence Critical2DKPZ.LocalSobolev
open scoped BoundedContinuousFunction CompactlySupported

namespace Critical2DKPZ.NonGaussian

/-- The measurable endpoint-kernel average agrees almost surely with the spatially averaged
endpoint pairing. -/
theorem endpointKernelAverage_eq_endpointPairing_ae
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {r t : ℝ} (hr : 0 < r) (hrt : r < t) (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x)
    (φ : C_c(Plane, ℝ)) :
    endpointKernelAverage (endpointMeasureKernel (Z r t) (hZ.1 r t hr.le hrt) r hr)
      (volume.withDensity (fun x => ENNReal.ofReal (ψ x))) φ =ᵐ[P]
      fun ω => ∫ x, ψ x * endpointPairing Z r t x φ ω := by
  filter_upwards [(hZ.2.1 r t hr.le hrt).mono fun ω hω => hω.1] with ω hω
  change (∫ x, (∫ y, φ y ∂endpointMeasureKernel (Z r t) (hZ.1 r t hr.le hrt) r hr (x, ω))
    ∂volume.withDensity (fun x => ENNReal.ofReal (ψ x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul ψ.continuous.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change (ENNReal.ofReal (ψ x)).toReal • (∫ y, φ y ∂endpointMeasureKernel (Z r t)
      (hZ.1 r t hr.le hrt) r hr (x, ω)) = _
    rw [ENNReal.toReal_ofReal (hψ x), smul_eq_mul,
      endpointMeasureKernel_apply_of_isLocallyFinite (Z r t) (hZ.1 r t hr.le hrt) r hr x ω hω,
      ← endpointPairing_eq_integral_endpointTerminalMeasure Z hr t x φ φ.continuous.stronglyMeasurable ω]

/-- The centered logarithmic endpoint approximation equals the scaled difference
of the separately centered perturbed and flat-terminal logarithmic fields. -/
theorem endpointKernelLogApprox_centered_eq_avgLogField
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) {r t : ℝ} (hr : 0 < r) (hrt : r < t)
    (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x)
    (φ : C_c(Plane, ℝ)) (hφ : ∀ y, |φ y| ≤ 1) {e : ℝ} (he : 0 < e) (hehalf : e ≤ 1 / 2) :
    let K := endpointMeasureKernel (Z r t) (hZ.1 r t hr.le hrt) r hr
    let ρ := volume.withDensity (fun x => ENNReal.ofReal (ψ x))
    (fun ω => endpointKernelLogApprox K ρ e φ ω -
      ∫ ω', endpointKernelLogApprox K ρ e φ ω' ∂P) =ᵐ[P]
      fun ω => e⁻¹ * (avgLogField P Z r t ψ (fun y => 1 + e * φ y) ω -
        avgLogField P Z r t ψ (fun _ => 1) ω) := by
  let K := endpointMeasureKernel (Z r t) (hZ.1 r t hr.le hrt) r hr
  let ρ : Measure Plane := volume.withDensity (fun x => ENNReal.ofReal (ψ x))
  let f : Plane →ᵇ ℝ := 1 + e • ofCompactSupport φ φ.continuous φ.hasCompactSupport
  have hf (y : Plane) : 1 / 2 ≤ f y := by
    have hlow := mul_le_mul_of_nonneg_left (abs_le.mp (hφ y)).1 he.le
    change 1 / 2 ≤ 1 + e * φ y
    linarith only [hlow, hehalf]
  obtain ⟨h₀, hexp⟩ := exists_bounded_log_profile f (by norm_num : (0 : ℝ) < 1 / 2) hf
  let Ff : Plane × Ω → ℝ := fun q => ψ q.1 * Real.log
    (shfPairing Z r t (fun y => heatKernel r (y - q.1)) f q.2)
  let F1 : Plane × Ω → ℝ := fun q => ψ q.1 * Real.log
    (shfPairing Z r t (fun y => heatKernel r (y - q.1)) (fun _ => 1) q.2)
  let a : Plane × Ω → ℝ := fun q => ∫ y, φ y ∂K q
  let H : Plane × Ω → ℝ := fun q => Real.log (1 + e * a q)
  have hFfi : Integrable Ff (volume.prod P) := by
    simpa only [hexp] using integrable_endpoint_log_field ϑ P Z hZ hsym hr hrt ψ h₀
  have hF1i : Integrable F1 (volume.prod P) := by
    simpa using integrable_endpoint_log_field ϑ P Z hZ hsym hr hrt ψ 0
  have ham : StronglyMeasurable a := φ.continuous.stronglyMeasurable.integral_kernel
  have habound (q : Plane × Ω) : |a q| ≤ 1 := by
    have hreal : (K q).real Set.univ ≤ 1 := ENNReal.toReal_le_of_le_ofReal (by norm_num)
      (by simpa only [ENNReal.ofReal_one] using
        endpointMeasureKernel_mass_le_one (Z r t) (hZ.1 r t hr.le hrt) r hr q)
    have hnorm : ∀ᵐ y ∂K q, ‖φ y‖ ≤ 1 :=
      Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hφ y
    simpa only [Real.norm_eq_abs, one_mul] using
      (norm_integral_le_of_norm_le_const hnorm).trans (by simpa only [one_mul] using hreal)
  have hHm : Measurable H := Real.measurable_log.comp
    (measurable_const.add (measurable_const.mul ham.measurable))
  have hHbound (q : Plane × Ω) : |H q| ≤ e * (2 * e + 1) := by
    have herr : |e⁻¹ * H q - a q| ≤ 2 * e :=
      abs_inv_mul_log_one_add_sub_le he hehalf (habound q)
    have htri := abs_sub_le (e⁻¹ * H q) (a q) 0
    simp only [sub_zero] at htri
    have hscaled : |e⁻¹ * H q| ≤ 2 * e + 1 :=
      htri.trans (add_le_add herr (habound q))
    calc
      _ = |e * (e⁻¹ * H q)| := by congr 1; field_simp
      _ = e * |e⁻¹ * H q| := by rw [abs_mul, abs_of_pos he]
      _ ≤ e * (2 * e + 1) := mul_le_mul_of_nonneg_left hscaled he.le
  have hHi : Integrable (fun q : Plane × Ω => ψ q.1 * H q) (volume.prod P) :=
    integrable_test_mul_bounded_joint P hHm.aemeasurable (by positivity) hHbound ψ
  let D : Plane × Ω → ℝ := Ff - F1
  have hDi : Integrable D (volume.prod P) := hFfi.sub hF1i
  have hlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Z r t ω) :=
    (hZ.2.1 r t hr.le hrt).mono fun ω hω => hω.1
  have hsec (x : Plane) : (fun ω => D (x, ω)) =ᵐ[P] fun ω => ψ x * H (x, ω) := by
    have hpos : ∀ᵐ ω ∂P, 0 < ∫ p, heatKernel r (p.1 - x) ∂Z r t ω := by
      simpa [shfPairing] using (hsym.2.2.2.2.2.2 r t r x 0 hr.le hrt hr).1
    filter_upwards [hlocal, hpos] with ω hω hp
    have hlog := log_heat_pairing_perturbation_eq (Z r t ω) hr x φ hφ he hehalf hp
    change ψ x * Real.log (shfPairing Z r t (fun y => heatKernel r (y - x)) f ω) -
      ψ x * Real.log (shfPairing Z r t (fun y => heatKernel r (y - x)) (fun _ => 1) ω) =
        ψ x * Real.log (1 + e * ∫ y, φ y ∂endpointMeasureKernel (Z r t)
          (hZ.1 r t hr.le hrt) r hr (x, ω))
    rw [endpointMeasureKernel_apply_of_isLocallyFinite (Z r t) (hZ.1 r t hr.le hrt) r hr x ω hω]
    change ψ x * Real.log (∫ p, heatKernel r (p.1 - x) * (1 + e * φ p.2) ∂Z r t ω) -
      ψ x * Real.log (∫ p, heatKernel r (p.1 - x) * 1 ∂Z r t ω) = _
    simp only [mul_one]
    rw [← mul_sub, hlog]
  have hDH := ae_eq_prod_of_integrable_sections volume P hDi hHi hsec
  have hslice := integral_spatial_congr_ae volume P hDH
  let Uf : Ω → ℝ := fun ω => ∫ x, Ff (x, ω)
  let U1 : Ω → ℝ := fun ω => ∫ x, F1 (x, ω)
  let V : Ω → ℝ := fun ω => ∫ x, ψ x * H (x, ω)
  have hUF : Integrable Uf P := hFfi.integral_prod_right
  have hU1 : Integrable U1 P := hF1i.integral_prod_right
  have hUD : (fun ω => Uf ω - U1 ω) =ᵐ[P] V := by
    have hsf := ((integrable_prod_iff' hFfi.aestronglyMeasurable).mp hFfi).1
    have hs1 := ((integrable_prod_iff' hF1i.aestronglyMeasurable).mp hF1i).1
    filter_upwards [hsf, hs1, hslice] with ω hωf hω1 hωH
    change (∫ x, Ff (x, ω)) - (∫ x, F1 (x, ω)) = _
    rw [← integral_sub hωf hω1]
    exact hωH
  have hmean : (∫ ω, Uf ω ∂P) - (∫ ω, U1 ω ∂P) = ∫ ω, V ω ∂P :=
    (integral_sub hUF hU1).symm.trans (integral_congr_ae hUD)
  have hAvgf : avgLogField P Z r t ψ f =ᵐ[P] fun ω => Uf ω - ∫ ω', Uf ω' ∂P := by
    simpa only [hexp] using avgLogField_exp_eq_centered_average ϑ P Z hZ hsym hr hrt ψ h₀
  have hAvg1 : avgLogField P Z r t ψ (fun _ => 1) =ᵐ[P] fun ω => U1 ω - ∫ ω', U1 ω' ∂P := by
    simpa using avgLogField_exp_eq_centered_average ϑ P Z hZ hsym hr hrt ψ 0
  have hlogcenter : (fun ω => avgLogField P Z r t ψ f ω -
      avgLogField P Z r t ψ (fun _ => 1) ω) =ᵐ[P] fun ω => V ω - ∫ ω', V ω' ∂P := by
    filter_upwards [hAvgf, hAvg1, hUD] with ω hωf hω1 hωD
    change avgLogField P Z r t ψ f ω - avgLogField P Z r t ψ (fun _ => 1) ω = _
    rw [hωf, hω1]
    change Uf ω - U1 ω = V ω at hωD
    linarith only [hωD, hmean]
  have hY (ω : Ω) : endpointKernelLogApprox K ρ e φ ω = e⁻¹ * V ω := by
    change (∫ x, e⁻¹ * H (x, ω) ∂volume.withDensity (fun x => ENNReal.ofReal (ψ x))) = _
    rw [integral_withDensity_eq_integral_toReal_smul ψ.continuous.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    calc
      _ = ∫ x, e⁻¹ * (ψ x * H (x, ω)) := integral_congr_ae
        (Filter.Eventually.of_forall fun x => by
          change (ENNReal.ofReal (ψ x)).toReal • (e⁻¹ * H (x, ω)) = _
          rw [ENNReal.toReal_ofReal (hψ x), smul_eq_mul]
          ring)
      _ = _ := integral_const_mul _ _
  have hmeanY : (∫ ω, endpointKernelLogApprox K ρ e φ ω ∂P) = e⁻¹ * ∫ ω, V ω ∂P := by
    simp_rw [hY]
    exact integral_const_mul _ _
  filter_upwards [hlogcenter] with ω hω
  change endpointKernelLogApprox K ρ e φ ω -
    (∫ ω', endpointKernelLogApprox K ρ e φ ω' ∂P) = _
  rw [hY, hmeanY]
  change avgLogField P Z r t ψ f ω - avgLogField P Z r t ψ (fun _ => 1) ω =
    V ω - ∫ ω', V ω' ∂P at hω
  change e⁻¹ * V ω - e⁻¹ * (∫ ω', V ω' ∂P) =
    e⁻¹ * (avgLogField P Z r t ψ f ω - avgLogField P Z r t ψ (fun _ => 1) ω)
  rw [hω]
  ring

end Critical2DKPZ.NonGaussian
