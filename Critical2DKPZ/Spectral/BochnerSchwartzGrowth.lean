/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Spectral.BochnerSchwartzRiesz
public import Critical2DKPZ.Spectral.FourierMeasurePairing
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Polynomial growth of the Bochner–Schwartz measure -/

@[expose] public section

noncomputable section

open MeasureTheory
open Set
open scoped FourierTransform

namespace Critical2DKPZ.Spectral

/-- A smooth nonnegative cutoff which is one on the closed ball of radius `R` and is supported
in the closed ball of radius `2R`. -/
def spectralBallCutoff (R : ℝ) (hR : 0 < R) : TestFn := by
  let b : ContDiffBump (0 : Plane) := ⟨R, 2 * R, hR, by linarith⟩
  exact {
    toFun := b
    contDiff' := b.contDiff
    hasCompactSupport' := b.hasCompactSupport
    tsupport_subset' := subset_univ _ }

/-- The spectral ball cutoff is nonnegative. -/
theorem spectralBallCutoff_nonneg (R : ℝ) (hR : 0 < R) (x : Plane) :
    0 ≤ spectralBallCutoff R hR x := by
  simp only [spectralBallCutoff]
  exact (⟨R, 2 * R, hR, by linarith⟩ : ContDiffBump (0 : Plane)).nonneg

/-- The spectral ball cutoff equals one on the indicated ball. -/
theorem spectralBallCutoff_eq_one (R : ℝ) (hR : 0 < R) {x : Plane}
    (hx : x ∈ Metric.closedBall 0 R) : spectralBallCutoff R hR x = 1 := by
  simp only [spectralBallCutoff]
  exact (⟨R, 2 * R, hR, by linarith⟩ : ContDiffBump (0 : Plane)).one_of_mem_closedBall hx

private theorem spectralBallCutoff_apply_scaled (R : ℝ) (hR : 0 < R) (x : Plane) :
    spectralBallCutoff R hR x = Critical2DKPZ.localizer 0 (R⁻¹ • x) := by
  simp [spectralBallCutoff, Critical2DKPZ.localizer, Critical2DKPZ.localizerBump,
    ContDiffBump.apply, hR.ne']

/-- The paper's Fourier transform of a scaled cutoff obeys the planar scaling law. -/
theorem fourierKPZ_spectralBallCutoff (R : ℝ) (hR : 0 < R) (ξ : Plane) :
    fourierKPZ (spectralBallCutoff R hR : Plane → ℝ) ξ =
      R ^ 2 * fourierKPZ (Critical2DKPZ.localizer 0 : Plane → ℝ) (R • ξ) := by
  let G : Plane → ℂ := fun y =>
    Complex.exp (-(Complex.I * (inner ℝ y (R • ξ) : ℝ))) *
      (Critical2DKPZ.localizer 0 y : ℂ)
  have hchange := Measure.integral_comp_inv_smul (μ := volume) G R
  have hdim : Module.finrank ℝ Plane = 2 := by simp [Plane]
  simp only [hdim, abs_of_pos (pow_pos hR 2), Complex.real_smul] at hchange
  unfold fourierKPZ
  have hleft :
      (∫ x : Plane,
        Complex.exp (-(Complex.I * (inner ℝ x ξ : ℝ))) *
          ((spectralBallCutoff R hR x : ℝ) : ℂ)) =
        ∫ x : Plane, G (R⁻¹ • x) := by
    apply integral_congr_ae
    filter_upwards [] with x
    simp [G, spectralBallCutoff_apply_scaled, inner_smul_left, inner_smul_right, hR.ne']
  rw [hleft, hchange]
  simp only [G]
  rw [Complex.ofReal_pow]

private theorem mathlibFourier_testFn_eq_fourierKPZ (f : TestFn) (ξ : Plane) :
    (𝓕 (testFnToSchwartzMap f)) ξ =
      fourierKPZ (f : Plane → ℝ) ((2 * Real.pi) • ξ) := by
  have hfreq : angularFrequencyEquiv ((2 * Real.pi) • ξ) = ξ := by
    change (2 * Real.pi)⁻¹ • ((2 * Real.pi) • ξ) = ξ
    rw [smul_smul, inv_mul_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), one_smul]
  have h := fourierKPZSchwartz_apply f ((2 * Real.pi) • ξ)
  change (𝓕 (testFnToSchwartzMap f))
      (angularFrequencyEquiv ((2 * Real.pi) • ξ)) = _ at h
  rw [hfreq] at h
  exact h

private theorem mathlibFourier_spectralBallCutoff (R : ℝ) (hR : 0 < R) (ξ : Plane) :
    (𝓕 (testFnToSchwartzMap (spectralBallCutoff R hR))) ξ =
      (R ^ 2 : ℂ) * (𝓕 (testFnToSchwartzMap (Critical2DKPZ.localizer 0))) (R • ξ) := by
  calc
    (𝓕 (testFnToSchwartzMap (spectralBallCutoff R hR))) ξ =
        fourierKPZ (spectralBallCutoff R hR : Plane → ℝ) ((2 * Real.pi) • ξ) :=
      mathlibFourier_testFn_eq_fourierKPZ _ _
    _ = (R ^ 2 : ℂ) * fourierKPZ (Critical2DKPZ.localizer 0 : Plane → ℝ)
          (R • ((2 * Real.pi) • ξ)) := by
      rw [fourierKPZ_spectralBallCutoff]
    _ = (R ^ 2 : ℂ) * fourierKPZ (Critical2DKPZ.localizer 0 : Plane → ℝ)
          ((2 * Real.pi) • (R • ξ)) := by
      congr 2
      rw [smul_smul, smul_smul, mul_comm]
    _ = (R ^ 2 : ℂ) * (𝓕 (testFnToSchwartzMap (Critical2DKPZ.localizer 0))) (R • ξ) := by
      rw [← mathlibFourier_testFn_eq_fourierKPZ]

/-- Positivity and the polynomial integral bound on `C` force polynomial ball growth of its
Fourier-side Riesz measure. -/
theorem fourierCccRieszMeasure_polynomial_ball_growth (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (∫ z in Metric.closedBall 0 R, |C z|) ≤ A * R ^ k)
    (heven : (fun z : Plane => C (-z)) =ᵐ[volume] C)
    (hpos : ∀ φ : TestFn, 0 ≤ ∫ p : Plane × Plane,
      φ p.1 * φ p.2 * C (p.1 - p.2)) :
    ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      (fourierCccRieszMeasure C hC hgrowth heven hpos
        (Metric.closedBall 0 R)).toReal ≤ A * R ^ k := by
  obtain ⟨n, hw⟩ := exists_integrable_polynomial_decay_mul_abs_of_ball_growth C hC hgrowth
  let w : Plane → ℝ := fun x => (1 + ‖x‖) ^ (-(n : ℝ))
  let f₀ : TestFn := Critical2DKPZ.localizer 0
  let F₀ : SchwartzMap Plane ℂ := 𝓕 (testFnToSchwartzMap f₀)
  let D : ℝ := 2 ^ n * ((Finset.Iic (n, 0)).sup
    (fun m => SchwartzMap.seminorm ℂ m.1 m.2)) F₀
  let W : ℝ := ∫ x : Plane, w x * |C x|
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hW : 0 ≤ W := by
    dsimp [W]
    apply integral_nonneg
    intro x
    exact mul_nonneg (by positivity) (abs_nonneg _)
  have hFdecay (ξ : Plane) :
      (1 + ‖ξ‖) ^ n * ‖F₀ ξ‖ ≤ D := by
    simpa only [F₀, D, norm_iteratedFDeriv_zero] using
      (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
        (m := (n, 0)) (k := n) (n := 0) le_rfl le_rfl F₀ ξ)
  have hscaledFourier (R : ℝ) (hR : 1 ≤ R) (x : Plane) :
      ‖(𝓕 (testFnToSchwartzMap (spectralBallCutoff R
        (lt_of_lt_of_le zero_lt_one hR)))) x‖ ≤ R ^ 2 * (D * w x) := by
    let hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
    let qR := spectralBallCutoff R hRpos
    have hnorm : ‖R • x‖ = R * ‖x‖ := by
      rw [norm_smul, Real.norm_of_nonneg hRpos.le]
    have hbase : 1 + ‖x‖ ≤ 1 + ‖R • x‖ := by
      rw [hnorm]
      nlinarith [mul_nonneg (sub_nonneg.mpr hR) (norm_nonneg x)]
    have hpow : (1 + ‖x‖) ^ n ≤ (1 + ‖R • x‖) ^ n :=
      pow_le_pow_left₀ (by positivity) hbase n
    have hdecay : ‖F₀ (R • x)‖ ≤ D * w x := by
      have hdiv : ‖F₀ (R • x)‖ ≤ D / (1 + ‖x‖) ^ n := by
        apply (le_div_iff₀ (by positivity)).2
        calc
          ‖F₀ (R • x)‖ * (1 + ‖x‖) ^ n ≤
              ‖F₀ (R • x)‖ * (1 + ‖R • x‖) ^ n :=
            mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
          _ ≤ D := by
            simpa only [mul_comm] using hFdecay (R • x)
      calc
        ‖F₀ (R • x)‖ ≤ D / (1 + ‖x‖) ^ n := hdiv
        _ = D * w x := by
          change D / (1 + ‖x‖) ^ n = D * (1 + ‖x‖) ^ (-(n : ℝ))
          rw [div_eq_mul_inv, Real.rpow_neg (by positivity), Real.rpow_natCast]
    calc
      ‖(𝓕 (testFnToSchwartzMap qR)) x‖ =
          R ^ 2 * ‖F₀ (R • x)‖ := by
        calc
          ‖(𝓕 (testFnToSchwartzMap qR)) x‖ =
              ‖(R ^ 2 : ℂ) * (𝓕 (testFnToSchwartzMap f₀)) (R • x)‖ := by
            rw [mathlibFourier_spectralBallCutoff]
          _ = ‖(R ^ 2 : ℂ)‖ * ‖(𝓕 (testFnToSchwartzMap f₀)) (R • x)‖ := norm_mul _ _
          _ = R ^ 2 * ‖F₀ (R • x)‖ := by
            simp [F₀, Complex.norm_real]
      _ ≤ R ^ 2 * (D * w x) :=
        mul_le_mul_of_nonneg_left hdecay (sq_nonneg R)
  have hweight : Integrable (fun x : Plane => w x * |C x|) volume := by
    simpa only [w] using hw
  have hCsm : AEStronglyMeasurable (fun x : Plane => (C x : ℂ)) volume :=
    Complex.ofRealCLM.continuous.comp_aestronglyMeasurable
      (locallyIntegrable_of_compactMemLp_two C hC).aestronglyMeasurable
  have hvalueBound (R : ℝ) (hR : 1 ≤ R) :
      |fourierTestLinearMap C hC hgrowth
        (spectralBallCutoff R (lt_of_lt_of_le zero_lt_one hR))| ≤
        (R ^ 2 * D) * W := by
    let qR : TestFn := spectralBallCutoff R (lt_of_lt_of_le zero_lt_one hR)
    let FR : Plane → ℂ := fun x => (𝓕 (testFnToSchwartzMap qR)) x
    let B : ℝ := R ^ 2 * D
    have hB : 0 ≤ B := mul_nonneg (sq_nonneg R) hD
    have hFRsm : AEStronglyMeasurable FR volume := by
      exact (𝓕 (testFnToSchwartzMap qR)).continuous.measurable.aestronglyMeasurable
    have hprodSm : AEStronglyMeasurable (fun x : Plane => (C x : ℂ) * FR x) volume :=
      hCsm.mul hFRsm
    have hmajor : Integrable (fun x : Plane => B * (w x * |C x|)) volume :=
      hweight.const_mul B
    have hprod : Integrable (fun x : Plane => (C x : ℂ) * FR x) volume := by
      apply hmajor.mono' hprodSm
      filter_upwards [] with x
      change ‖(C x : ℂ) * FR x‖ ≤ B * (w x * |C x|)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc
        |C x| * ‖FR x‖ ≤ |C x| * (R ^ 2 * D * w x) :=
          mul_le_mul_of_nonneg_left (by simpa [FR, mul_assoc] using hscaledFourier R hR x)
            (abs_nonneg _)
        _ = B * (w x * |C x|) := by dsimp [B]; ring
    have hformula :
        fourierTestLinearMap C hC hgrowth qR =
          (∫ x : Plane, (C x : ℂ) * FR x).re := by
      change ((𝓕 (kernelTemperedDistribution C hC hgrowth))
        (testFnToSchwartzMap qR)).re = _
      rw [fourier_kernelTemperedDistribution_apply_schwartz]
    have hnormIntegral :
        (∫ x : Plane, ‖(C x : ℂ) * FR x‖) ≤ B * W := by
      calc
        (∫ x : Plane, ‖(C x : ℂ) * FR x‖) ≤
            ∫ x : Plane, B * (w x * |C x|) := by
          apply integral_mono_ae hprod.norm hmajor
          filter_upwards [] with x
          change ‖(C x : ℂ) * FR x‖ ≤ B * (w x * |C x|)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          calc
            |C x| * ‖FR x‖ ≤ |C x| * (R ^ 2 * D * w x) :=
              mul_le_mul_of_nonneg_left (by simpa [FR, mul_assoc] using hscaledFourier R hR x)
                (abs_nonneg _)
            _ = B * (w x * |C x|) := by dsimp [B]; ring
        _ = B * W := by simp [B, W, integral_const_mul]
    calc
      |fourierTestLinearMap C hC hgrowth qR| =
          |(∫ x : Plane, (C x : ℂ) * FR x).re| := by rw [hformula]
      _ ≤ ‖∫ x : Plane, (C x : ℂ) * FR x‖ :=
        RCLike.abs_re_le_norm (∫ x : Plane, (C x : ℂ) * FR x)
      _ ≤ ∫ x : Plane, ‖(C x : ℂ) * FR x‖ :=
        norm_integral_le_integral_norm (f := fun x : Plane => (C x : ℂ) * FR x)
      _ ≤ B * W := hnormIntegral
      _ = (R ^ 2 * D) * W := rfl
  refine ⟨D * W, 2, ?_⟩
  intro R hR
  let hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let qR : TestFn := spectralBallCutoff R hRpos
  let Λ := fourierCccPositiveLinearMap C hC hgrowth heven hpos
  let ν := fourierCccRieszMeasure C hC hgrowth heven hpos
  have hmeasure : ν (Metric.closedBall 0 R) ≤
      ENNReal.ofReal (Λ (testFnToCcc qR)) := by
    change RealRMK.rieszMeasure Λ (Metric.closedBall 0 R) ≤
      ENNReal.ofReal (Λ (testFnToCcc qR))
    exact RealRMK.rieszMeasure_le_of_eq_one Λ
      (fun x => spectralBallCutoff_nonneg R hRpos x)
      (isCompact_closedBall 0 R)
      (fun x hx => by
        rw [testFnToCcc_apply]
        exact spectralBallCutoff_eq_one R hRpos hx)
  have hvalue : Λ (testFnToCcc qR) = fourierTestLinearMap C hC hgrowth qR := by
    change fourierCccValue C hC hgrowth (testFnToCcc qR) = _
    exact fourierCccValue_testFn C hC hgrowth heven hpos qR
  rw [hvalue] at hmeasure
  have hnonneg : 0 ≤ fourierTestLinearMap C hC hgrowth qR :=
    fourierTestLinearMap_nonneg C hC hgrowth heven hpos qR
      (spectralBallCutoff_nonneg R hRpos)
  have hreal := ENNReal.toReal_le_of_le_ofReal hnonneg hmeasure
  calc
    (ν (Metric.closedBall 0 R)).toReal ≤ fourierTestLinearMap C hC hgrowth qR := hreal
    _ ≤ |fourierTestLinearMap C hC hgrowth qR| := le_abs_self _
    _ ≤ (R ^ 2 * D) * W := hvalueBound R hR
    _ = (D * W) * R ^ 2 := by ring

end Critical2DKPZ.Spectral

end
