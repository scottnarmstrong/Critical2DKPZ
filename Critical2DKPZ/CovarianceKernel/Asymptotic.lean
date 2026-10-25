/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Spectral.FourierConvention
public import Critical2DKPZ.Spectral.FourierMeasurePairing
public import Critical2DKPZ.Definitions.TestFnDilate
public import Critical2DKPZ.Analysis.Sobolev.CompactMollifier
public import Critical2DKPZ.SmallScales.Inputs
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Fourier scaling facts for the KPZ covariance kernel -/

@[expose] public section

noncomputable section

open MeasureTheory
open ProbabilityTheory
open Filter
open Module
open scoped BoundedContinuousFunction ComplexConjugate RealInnerProductSpace Topology

namespace Critical2DKPZ.CovarianceKernel

/-- The Fourier transform of a centered test-function dilation is evaluated at the scaled
frequency. -/
theorem fourierKPZ_dilate_center (φ : TestFn) {ε : ℝ} (hε : 0 < ε) (ξ : Plane) :
    Spectral.fourierKPZ (φ.dilate ε 0) ξ = Spectral.fourierKPZ φ (ε • ξ) := by
  rw [Spectral.fourierKPZ, Spectral.fourierKPZ]
  let G : Plane → ℂ := fun x =>
    Complex.exp (-(Complex.I * (inner ℝ x (ε • ξ) : ℝ))) * (φ x : ℂ)
  have hdim : finrank ℝ Plane = 2 := by simp [Plane]
  have hchange := Measure.integral_comp_smul (μ := (volume : Measure Plane)) G ε⁻¹
  rw [hdim] at hchange
  have hscale : |((ε⁻¹) ^ 2)⁻¹| = ε ^ 2 := by
    rw [inv_pow, inv_inv, abs_of_pos (pow_pos hε 2)]
  rw [hscale] at hchange
  have hchange' : (∫ x : Plane, G (ε⁻¹ • x)) =
      Complex.ofReal (ε ^ 2) * ∫ x : Plane, G x := by
    calc
      (∫ x : Plane, G (ε⁻¹ • x)) = ε ^ 2 • ∫ x : Plane, G x := hchange
      _ = Complex.ofReal (ε ^ 2) * ∫ x : Plane, G x := by
        rw [RCLike.real_smul_eq_coe_mul]
        rfl
  have hphase (x : Plane) : inner ℝ (ε⁻¹ • x) (ε • ξ) = inner ℝ x ξ := by
    rw [real_inner_smul_left, real_inner_smul_right]
    field_simp
  have hphase' (x : Plane) : inner ℝ x ξ = inner ℝ (ε⁻¹ • x) (ε • ξ) := by
    exact (hphase x).symm
  have hcancel : (ε⁻¹) ^ 2 * ε ^ 2 = 1 := by
    field_simp
  have hrewrite :
      (∫ x : Plane, Complex.exp (-(Complex.I * (inner ℝ x ξ : ℝ))) *
          (((ε⁻¹) ^ 2 * φ (ε⁻¹ • x) : ℝ) : ℂ)) =
        (ε⁻¹) ^ 2 * ∫ x : Plane, G (ε⁻¹ • x) := by
    calc
      _ = ∫ x : Plane, (ε⁻¹) ^ 2 *
          (Complex.exp (-(Complex.I * (inner ℝ x ξ : ℝ))) * (φ (ε⁻¹ • x) : ℂ)) := by
            apply integral_congr_ae
            filter_upwards [] with x
            push_cast
            ring
      _ = (ε⁻¹) ^ 2 * ∫ x : Plane,
          Complex.exp (-(Complex.I * (inner ℝ x ξ : ℝ))) * (φ (ε⁻¹ • x) : ℂ) :=
            integral_const_mul _ _
      _ = (ε⁻¹) ^ 2 * ∫ x : Plane, G (ε⁻¹ • x) := by
            congr 1
            apply integral_congr_ae
            filter_upwards [] with x
            simp only [G]
            rw [hphase' x]
  simp only [TestFn.dilate, sub_zero]
  change (∫ x : Plane, Complex.exp (-(Complex.I * (inner ℝ x ξ : ℝ))) *
      (((ε⁻¹) ^ 2 * φ (ε⁻¹ • x) : ℝ) : ℂ)) =
    ∫ x : Plane, Complex.exp (-(Complex.I * (inner ℝ x (ε • ξ) : ℝ))) * (φ x : ℂ)
  rw [hrewrite, hchange']
  calc
    _ = (Complex.ofReal ((ε⁻¹) ^ 2) * Complex.ofReal (ε ^ 2)) *
        ∫ x : Plane, G x := by
          rw [← Complex.ofReal_pow]
          ac_rfl
    _ = Complex.ofReal ((ε⁻¹) ^ 2 * ε ^ 2) * ∫ x : Plane, G x := by
          rw [← Complex.ofReal_mul]
    _ = ∫ x : Plane, G x := by rw [hcancel]; simp
    _ = ∫ x : Plane, Complex.exp (-(Complex.I * (inner ℝ x (ε • ξ) : ℝ))) * (φ x : ℂ) := rfl

/-- The paper-normalized Fourier transform of the canonical unit-mass bump equals one at the
origin. -/
theorem fourierKPZ_unitMassTestFn_zero :
    Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn 0 = 1 := by
  unfold Spectral.fourierKPZ
  calc
    _ = ∫ x : Plane, (Analysis.Sobolev.unitMassTestFn x : ℂ) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [inner_zero_right, Complex.ofReal_zero, mul_zero, neg_zero,
        Complex.exp_zero, one_mul]
    _ = ∫ x : Plane, Analysis.Sobolev.unitMassTestFn x := _root_.integral_complex_ofReal
    _ = 1 := by rw [Analysis.Sobolev.integral_unitMassTestFn]; exact Complex.ofReal_one

/-- The paper-normalized Fourier transform of a test function is continuous in frequency. -/
theorem continuous_fourierKPZ (φ : TestFn) :
    Continuous (Spectral.fourierKPZ φ) := by
  have h : (Spectral.fourierKPZSchwartz φ : Plane → ℂ) = Spectral.fourierKPZ φ := by
    funext ξ
    exact Spectral.fourierKPZSchwartz_apply φ ξ
  rw [← h]
  exact (Spectral.fourierKPZSchwartz φ).continuous

/-- A Schwartz seminorm gives quadratic decay of the paper-normalized Fourier transform outside
the unit ball. The constant depends only on the fixed test function. -/
theorem exists_fourierKPZ_quadratic_decay (φ : TestFn) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : Plane, 1 ≤ ‖ξ‖ →
      ‖Spectral.fourierKPZ φ ξ‖ ≤ C / ‖ξ‖ ^ 2 := by
  let F := Spectral.fourierKPZSchwartz φ
  let C : ℝ := (SchwartzMap.seminorm ℝ 2 0) F + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hpoint (ξ : Plane) :
      ‖ξ‖ ^ 2 * ‖Spectral.fourierKPZ φ ξ‖ ≤ (SchwartzMap.seminorm ℝ 2 0) F := by
    simpa only [F, Spectral.fourierKPZSchwartz_apply] using
      (SchwartzMap.norm_pow_mul_le_seminorm ℝ F 2 ξ)
  refine ⟨C, hC, fun ξ _ => ?_⟩
  have hmul : ‖ξ‖ ^ 2 * ‖Spectral.fourierKPZ φ ξ‖ ≤ C := by
    dsimp [C]
    exact (hpoint ξ).trans (le_add_of_nonneg_right (by norm_num))
  have hden : 0 < ‖ξ‖ ^ 2 := by positivity
  apply (le_div_iff₀ hden).2
  simpa only [mul_comm] using hmul

/-- The squared Fourier magnitude of the unit-mass bump stays bounded away from zero near the
origin. -/
theorem exists_unitMass_fourier_lower_near_zero :
    ∃ c : ℝ, 0 < c ∧ ∀ ξ : Plane, ‖ξ‖ ≤ c →
      (1 / 4 : ℝ) ≤ ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn ξ‖ ^ 2 := by
  let F := Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn
  have hcont : Continuous F := continuous_fourierKPZ Analysis.Sobolev.unitMassTestFn
  have hF0 : F 0 = 1 := fourierKPZ_unitMassTestFn_zero
  have hnear : Metric.ball (1 : ℂ) (1 / 2) ∈ 𝓝 (F 0) := by
    rw [hF0]
    exact Metric.ball_mem_nhds _ (by norm_num)
  have hev : ∀ᶠ ξ in 𝓝 (0 : Plane), F ξ ∈ Metric.ball (1 : ℂ) (1 / 2) :=
    hcont.continuousAt.preimage_mem_nhds hnear
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨r / 2, by positivity, fun ξ hξ => ?_⟩
  have hξball : ξ ∈ Metric.ball (0 : Plane) r := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hdist := hsub hξball
  have hnormdist : ‖1 - F ξ‖ < 1 / 2 := by
    simpa [dist_eq_norm, norm_sub_rev] using hdist
  have hnorm : 1 / 2 ≤ ‖F ξ‖ := by
    have htriangle := norm_add_le (1 - F ξ) (F ξ)
    have heq : (1 - F ξ) + F ξ = 1 := by ring
    rw [heq, norm_one] at htriangle
    linarith
  nlinarith [sq_nonneg (‖F ξ‖ - (1 / 2 : ℝ))]

/-- For `0 < η < 1`, the squared magnitude of the unit-mass Fourier profile is at least
`(1 - η) ^ 2` on a sufficiently small frequency ball. -/
theorem exists_unitMass_fourier_lower_near_zero_of (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ ξ : Plane, ‖ξ‖ ≤ c →
      (1 - η) ^ 2 ≤ ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn ξ‖ ^ 2 := by
  let F := Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn
  have hcont : Continuous F := continuous_fourierKPZ Analysis.Sobolev.unitMassTestFn
  have hF0 : F 0 = 1 := fourierKPZ_unitMassTestFn_zero
  have hnear : Metric.ball (1 : ℂ) η ∈ 𝓝 (F 0) := by
    rw [hF0]
    exact Metric.ball_mem_nhds _ hη
  have hev : ∀ᶠ ξ in 𝓝 (0 : Plane), F ξ ∈ Metric.ball (1 : ℂ) η :=
    hcont.continuousAt.preimage_mem_nhds hnear
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨r / 2, by positivity, fun ξ hξ => ?_⟩
  have hξball : ξ ∈ Metric.ball (0 : Plane) r := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hdist := hsub hξball
  have hnormdist : ‖1 - F ξ‖ < η := by
    simpa [dist_eq_norm, norm_sub_rev] using hdist
  have hnorm : 1 - η ≤ ‖F ξ‖ := by
    have htriangle := norm_add_le (1 - F ξ) (F ξ)
    have heq : (1 - F ξ) + F ξ = 1 := by ring
    rw [heq, norm_one] at htriangle
    linarith
  exact (sq_le_sq₀ (sub_nonneg.mpr hη1.le) (norm_nonneg _)).2 hnorm

/-- The spectral covariance representation identifies a test function's Fourier energy with its field variance. This identity uses the stated Bochner integrals without asserting spectral integrability. -/
theorem integral_fourierEnergy_eq_variance_of {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (t : ℝ)
    (ν : Measure Plane) (hν : ∀ f g : TestFn,
      cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P] =
        ∫ ξ, (Spectral.fourierKPZ f ξ * conj (Spectral.fourierKPZ g ξ)).re ∂ν)
    (φ : TestFn) (hmem : MemLp (fun ω => H t 0 ω φ) 2 P) :
    (∫ ξ, ‖Spectral.fourierKPZ φ ξ‖ ^ 2 ∂ν) = Var[fun ω => H t 0 ω φ; P] := by
  calc
    (∫ ξ, ‖Spectral.fourierKPZ φ ξ‖ ^ 2 ∂ν) =
        ∫ ξ, (Spectral.fourierKPZ φ ξ * conj (Spectral.fourierKPZ φ ξ)).re ∂ν := by
          apply integral_congr_ae
          filter_upwards [] with ξ
          rw [Complex.mul_conj']
          rw [← Complex.ofReal_pow, Complex.ofReal_re]
    _ = cov[fun ω => H t 0 ω φ, fun ω => H t 0 ω φ; P] := (hν φ φ).symm
    _ = Var[fun ω => H t 0 ω φ; P] :=
          ProbabilityTheory.covariance_self hmem.aemeasurable

end Critical2DKPZ.CovarianceKernel

end
