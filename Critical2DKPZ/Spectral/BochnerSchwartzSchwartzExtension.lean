/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Spectral.BochnerSchwartzInterface
public import Critical2DKPZ.Spectral.BochnerSchwartzSquareCone
public import Critical2DKPZ.Spectral.ScaledLocalizers
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! # Extending the Riesz representation to Schwartz tests -/

@[expose] public section

noncomputable section

open MeasureTheory
open Filter
open TopologicalSpace
open scoped FourierTransform SchwartzMap Topology

set_option linter.style.haveILetI false

namespace Critical2DKPZ.Spectral

/-- The Fourier transforms of scaled cutoffs of a fixed real Schwartz function form a bounded
family in complex Schwartz space. -/
theorem fourier_scaledCutoffSchwartz_isVonNBounded (f : SchwartzMap Plane ℝ) :
    Bornology.IsVonNBounded ℝ (Set.range fun n : ℕ =>
      (SchwartzMap.fourierTransformCLM ℂ).restrictScalars ℝ
        (realSchwartzToComplex (scaledCutoffSchwartz n f))) := by
  let e : SchwartzMap Plane ℝ →L[ℝ] SchwartzMap Plane ℂ :=
    SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM
  let F : SchwartzMap Plane ℂ →L[ℝ] SchwartzMap Plane ℂ :=
    (SchwartzMap.fourierTransformCLM ℂ).restrictScalars ℝ
  have hb := (scaledCutoffSchwartz_isVonNBounded f).image (F.comp e)
  rw [← Set.range_comp] at hb
  change Bornology.IsVonNBounded ℝ
    (Set.range fun n : ℕ => F (e (scaledCutoffSchwartz n f)))
  exact hb

/-- Every fixed Schwartz seminorm of the transformed cutoff family is bounded uniformly in the
cutoff scale. -/
theorem exists_fourier_scaledCutoffSchwartz_seminorm_bound (f : SchwartzMap Plane ℝ)
    (k m : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ,
      SchwartzMap.seminorm ℝ k m
        ((SchwartzMap.fourierTransformCLM ℂ).restrictScalars ℝ
          (realSchwartzToComplex (scaledCutoffSchwartz n f))) < B := by
  have hb := (schwartz_withSeminorms ℝ Plane ℂ).isVonNBounded_iff_seminorm_bounded.mp
    (fourier_scaledCutoffSchwartz_isVonNBounded f)
  obtain ⟨B, hB, hbound⟩ := hb (k, m)
  refine ⟨B, hB, fun n => ?_⟩
  exact hbound _ ⟨n, rfl⟩

/-- The Fourier transforms of the compact cutoffs converge pointwise to the Fourier transform of
the original Schwartz function. -/
theorem tendsto_fourier_scaledCutoffSchwartz_apply (f : SchwartzMap Plane ℝ)
    (ξ : Plane) :
    Tendsto (fun n : ℕ =>
      ((SchwartzMap.fourierTransformCLM ℂ).restrictScalars ℝ
        (realSchwartzToComplex (scaledCutoffSchwartz n f))) ξ) atTop
      (𝓝 ((𝓕 (realSchwartzToComplex f)) ξ)) := by
  let G : ℕ → Plane → ℂ := fun n y =>
    Complex.exp ((↑(-2 * Real.pi * inner ℝ y ξ) : ℂ) * Complex.I) *
      realSchwartzToComplex (scaledCutoffSchwartz n f) y
  let bound : Plane → ℝ := fun y => |f y|
  have hbound : Integrable bound volume := by
    simpa only [bound, Real.norm_eq_abs] using f.integrable.norm
  have hfourier (g : SchwartzMap Plane ℂ) :
      ((SchwartzMap.fourierTransformCLM ℂ g) ξ) =
        ∫ y : Plane,
          Complex.exp ((↑(-2 * Real.pi * inner ℝ y ξ) : ℂ) * Complex.I) * g y := by
    rw [SchwartzMap.fourierTransformCLM_apply, SchwartzMap.fourier_coe]
    rw [Real.fourier_eq']
    simp only [smul_eq_mul]
  have hmeas (n : ℕ) : AEStronglyMeasurable (G n) volume := by
    have hcont : Continuous (G n) := by
      dsimp [G]
      fun_prop
    exact hcont.measurable.aestronglyMeasurable
  have hdom (n : ℕ) : ∀ᵐ y : Plane ∂volume, ‖G n y‖ ≤ bound y := by
    filter_upwards [] with y
    dsimp [G, bound]
    have hχnonneg : 0 ≤ scaledLocalizer n y := by
      rw [scaledLocalizer_apply]
      exact Critical2DKPZ.localizer_nonneg 0 _
    have hχle : scaledLocalizer n y ≤ 1 := by
      rw [scaledLocalizer_apply]
      exact Critical2DKPZ.localizer_le_one 0 _
    have hreal : |scaledLocalizer n y * f y| ≤ |f y| := by
      rw [abs_mul, abs_of_nonneg hχnonneg]
      calc
        scaledLocalizer n y * |f y| ≤ 1 * |f y| :=
          mul_le_mul_of_nonneg_right hχle (abs_nonneg _)
        _ = |f y| := by rw [one_mul]
    simpa [norm_mul, Complex.norm_exp, realSchwartzToComplex_apply,
      scaledCutoffSchwartz_apply, Complex.norm_real, Real.norm_eq_abs] using hreal
  have hpoint (y : Plane) :
      Tendsto (fun n : ℕ => G n y) atTop
        (𝓝 (Complex.exp ((↑(-2 * Real.pi * inner ℝ y ξ) : ℂ) * Complex.I) *
          realSchwartzToComplex f y)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_scaledLocalizer_eq_one y] with n hn
    simp only [G, realSchwartzToComplex_apply, scaledCutoffSchwartz_apply, hn,
      Complex.ofReal_mul, Complex.ofReal_one, one_mul]
  have hIntTendsto := tendsto_integral_of_dominated_convergence bound hmeas hbound hdom
    (ae_of_all _ hpoint)
  have hsource :
      ∫ y : Plane,
        Complex.exp ((↑(-2 * Real.pi * inner ℝ y ξ) : ℂ) * Complex.I) *
          realSchwartzToComplex f y = (𝓕 (realSchwartzToComplex f)) ξ := by
    symm
    exact hfourier (realSchwartzToComplex f)
  have htarget : ∀ n,
      ∫ y : Plane, G n y =
        ((SchwartzMap.fourierTransformCLM ℂ).restrictScalars ℝ
          (realSchwartzToComplex (scaledCutoffSchwartz n f))) ξ := by
    intro n
    exact (hfourier (realSchwartzToComplex (scaledCutoffSchwartz n f))).symm
  simpa only [htarget, hsource] using hIntTendsto

/-- Two Schwartz seminorm bounds control one polynomially weighted pointwise norm. -/
theorem one_add_norm_pow_mul_norm_le_of_seminorm_bounds
    (g : SchwartzMap Plane ℂ) (k : ℕ) (B0 Bk : ℝ)
    (h0 : SchwartzMap.seminorm ℝ 0 0 g ≤ B0)
    (hk : SchwartzMap.seminorm ℝ k 0 g ≤ Bk) (x : Plane) :
    (1 + ‖x‖) ^ k * ‖g x‖ ≤ 2 ^ (k - 1) * (B0 + Bk) := by
  have hpoly : (1 + ‖x‖) ^ k ≤ 2 ^ (k - 1) * (1 + ‖x‖ ^ k) := by
    simpa only [one_pow] using
      add_pow_le (a := (1 : ℝ)) (b := ‖x‖) (by norm_num) (norm_nonneg x) k
  have h0x : ‖g x‖ ≤ B0 :=
    (SchwartzMap.norm_le_seminorm ℝ g x).trans h0
  have hkx : ‖x‖ ^ k * ‖g x‖ ≤ Bk :=
    (SchwartzMap.norm_pow_mul_le_seminorm ℝ g k x).trans hk
  calc
    (1 + ‖x‖) ^ k * ‖g x‖ ≤
        2 ^ (k - 1) * (1 + ‖x‖ ^ k) * ‖g x‖ :=
      mul_le_mul_of_nonneg_right hpoly (norm_nonneg _)
    _ = 2 ^ (k - 1) * (‖g x‖ + ‖x‖ ^ k * ‖g x‖) := by ring
    _ ≤ 2 ^ (k - 1) * (B0 + Bk) := by
      exact mul_le_mul_of_nonneg_left (add_le_add h0x hkx) (by positivity)

/-- The kernel integral of the Fourier transforms of compact cutoffs converges to the Schwartz
Fourier pairing. -/
theorem tendsto_kernel_mul_fourier_scaledCutoff (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (f : SchwartzMap Plane ℝ) :
    Tendsto (fun n : ℕ => ∫ x : Plane, (C x : ℂ) *
      ((SchwartzMap.fourierTransformCLM ℂ).restrictScalars ℝ
        (realSchwartzToComplex (scaledCutoffSchwartz n f))) x) atTop
      (𝓝 (∫ x : Plane, (C x : ℂ) * (𝓕 (realSchwartzToComplex f)) x)) := by
  obtain ⟨N, hweight⟩ :=
    exists_integrable_polynomial_decay_mul_abs_of_ball_growth C hC hgrowth
  obtain ⟨B0, hB0, hseminorm0⟩ :=
    exists_fourier_scaledCutoffSchwartz_seminorm_bound f 0 0
  obtain ⟨BN, hBN, hseminormN⟩ :=
    exists_fourier_scaledCutoffSchwartz_seminorm_bound f N 0
  let B : ℝ := 2 ^ (N - 1) * (B0 + BN)
  have hB : 0 < B := by dsimp [B]; positivity
  let G : ℕ → SchwartzMap Plane ℂ := fun n =>
    (SchwartzMap.fourierTransformCLM ℂ).restrictScalars ℝ
      (realSchwartzToComplex (scaledCutoffSchwartz n f))
  let F : ℕ → Plane → ℂ := fun n x => (C x : ℂ) * G n x
  let bound : Plane → ℝ := fun x => B *
    ((1 + ‖x‖) ^ (-(N : ℝ)) * |C x|)
  have hbound : Integrable bound volume := by
    dsimp [bound]
    simpa only [mul_assoc] using hweight.const_mul B
  have hmeas (n : ℕ) : AEStronglyMeasurable (F n) volume :=
    (integrable_kernel_mul_schwartz C hC hgrowth (G n)).aestronglyMeasurable
  have hpointwise_decay (n : ℕ) (x : Plane) :
      ‖G n x‖ ≤ B * (1 + ‖x‖) ^ (-(N : ℝ)) := by
    have h0 : SchwartzMap.seminorm ℝ 0 0 (G n) ≤ B0 := (hseminorm0 n).le
    have hN : SchwartzMap.seminorm ℝ N 0 (G n) ≤ BN := (hseminormN n).le
    have hpoly := one_add_norm_pow_mul_norm_le_of_seminorm_bounds (G n) N B0 BN h0 hN x
    have hw : 0 < 1 + ‖x‖ := by positivity
    rw [Real.rpow_neg (le_of_lt hw), Real.rpow_natCast]
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    dsimp [B]
    nlinarith [hpoly]
  have hdom (n : ℕ) : ∀ᵐ x : Plane ∂volume, ‖F n x‖ ≤ bound x := by
    filter_upwards [] with x
    dsimp [F, bound]
    rw [Complex.norm_mul, Complex.norm_real]
    calc
      |C x| * ‖G n x‖ ≤ |C x| *
          (B * (1 + ‖x‖) ^ (-(N : ℝ))) :=
        mul_le_mul_of_nonneg_left (hpointwise_decay n x) (abs_nonneg _)
      _ = B * ((1 + ‖x‖) ^ (-(N : ℝ)) * |C x|) := by ring
  have hpoint (x : Plane) :
      Tendsto (fun n : ℕ => F n x) atTop
        (𝓝 ((C x : ℂ) * (𝓕 (realSchwartzToComplex f)) x)) := by
    simpa only [F, G, SchwartzMap.fourierTransformCLM_apply] using
      (tendsto_const_nhds.mul (tendsto_fourier_scaledCutoffSchwartz_apply f x))
  have hconv := tendsto_integral_of_dominated_convergence bound hmeas hbound hdom
    (ae_of_all _ hpoint)
  simpa only [F, G] using hconv

/-- The Riesz representation identity for a real Schwartz test follows from the compact-test
identity. -/
theorem fourierCccRieszMeasure_integral_schwartz (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ φ : TestFn, 0 ≤ ∫ p : Plane × Plane,
      φ p.1 * φ p.2 * C (p.1 - p.2))
    (f : SchwartzMap Plane ℝ) :
    (∫ x : Plane, f x ∂fourierCccRieszMeasure C hC hgrowth heven hpos) =
      ((𝓕 (kernelTemperedDistribution C hC hgrowth))
        (realSchwartzToComplex f)).re := by
  let μ := fourierCccRieszMeasure C hC hgrowth heven hpos
  have hμgrowth := fourierCccRieszMeasure_polynomial_ball_growth C hC hgrowth heven hpos
  letI : IsLocallyFiniteMeasure μ :=
    fourierCccRieszMeasure_isLocallyFinite C hC hgrowth heven hpos
  letI : μ.HasTemperateGrowth := measure_hasTemperateGrowth_of_polynomial_ball_growth μ hμgrowth
  have hleft : Tendsto
      (fun n : ℕ => ∫ x : Plane, scaledCutoffTestFn n f x ∂μ) atTop
      (𝓝 (∫ x : Plane, f x ∂μ)) :=
    tendsto_integral_scaledCutoffTestFn μ f
  have hright := tendsto_kernel_mul_fourier_scaledCutoff C hC hgrowth f
  let G : ℕ → SchwartzMap Plane ℂ := fun n =>
    (SchwartzMap.fourierTransformCLM ℂ).restrictScalars ℝ
      (realSchwartzToComplex (scaledCutoffSchwartz n f))
  let K : ℕ → ℂ := fun n => ∫ x : Plane, (C x : ℂ) * G n x
  have htest (n : ℕ) : testFnToSchwartzMap (scaledCutoffTestFn n f) =
      realSchwartzToComplex (scaledCutoffSchwartz n f) := by
    ext x
    simp [testFnToSchwartzMap_apply, realSchwartzToComplex_apply,
      scaledCutoffTestFn_apply, scaledCutoffSchwartz_apply]
  have hseq (n : ℕ) :
      (∫ x : Plane, scaledCutoffTestFn n f x ∂μ) = (K n).re := by
    rw [fourierCccRieszMeasure_integral_testFn C hC hgrowth heven hpos
      (scaledCutoffTestFn n f)]
    change ((𝓕 (kernelTemperedDistribution C hC hgrowth))
      (testFnToSchwartzMap (scaledCutoffTestFn n f))).re = (K n).re
    rw [htest n, fourier_kernelTemperedDistribution_apply_schwartz]
    congr 1
  have hrightRe : Tendsto (fun n : ℕ => (K n).re) atTop
      (𝓝 ((∫ x : Plane, (C x : ℂ) *
        (𝓕 (realSchwartzToComplex f)) x).re)) := by
    change Tendsto (fun n : ℕ => Complex.re (∫ x : Plane, (C x : ℂ) * G n x))
      atTop (𝓝 (Complex.re (∫ x : Plane, (C x : ℂ) *
        (𝓕 (realSchwartzToComplex f)) x)))
    exact Complex.continuous_re.continuousAt.tendsto.comp hright
  have hleft' : Tendsto (fun n : ℕ => (K n).re) atTop
      (𝓝 (∫ x : Plane, f x ∂μ)) := by
    apply hleft.congr'
    exact Eventually.of_forall fun n => hseq n
  have hlimit := tendsto_nhds_unique hleft' hrightRe
  rw [fourier_kernelTemperedDistribution_apply_schwartz C hC hgrowth
    (realSchwartzToComplex f)]
  simpa [μ] using hlimit

end Critical2DKPZ.Spectral

end
