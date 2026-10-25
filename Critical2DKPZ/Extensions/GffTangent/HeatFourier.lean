/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Spectral.FourierConvention
public import Critical2DKPZ.Analysis.Sobolev.GaussianPairing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Critical2DKPZ.Analysis.Heat.Moments
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Heat pairings in angular Fourier coordinates

Fixed positive times require only integrable real functions. We use the main
library's Gaussian Fourier inversion and an integrable product majorant.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace

namespace Critical2DKPZ.Extensions.GffTangent

open Analysis.Sobolev Spectral

/-- Heat smoothing in the variance convention of the note. -/
def heatSmooth (s : ℝ) (f : Plane → ℝ) (x : Plane) : ℝ :=
  ∫ y : Plane, heatKernel s (x - y) * f y

/-- The two project Fourier integrals agree for any real input. -/
theorem fourierKPZ_eq_angularFourierIntegral_fun (f : Plane → ℝ) (ξ : Plane) :
    fourierKPZ f ξ = angularFourierIntegral f ξ := by
  unfold fourierKPZ angularFourierIntegral
  apply integral_congr_ae
  filter_upwards [] with x
  congr 2
  rw [real_inner_comm x ξ]
  push_cast
  ring

/-- The complex heat pairing obtained from Gaussian Fourier inversion. -/
theorem inner_heatSemigroup_eq_fourier_complex {f g : Plane → ℝ}
    (hf : Integrable f) (hg : Integrable g) {s : ℝ} (hs : 0 < s) :
    (((2 * Real.pi)⁻¹ ^ 2 : ℝ) : ℂ) *
      (∫ ξ : Plane, (Real.exp (-s * ‖ξ‖ ^ 2) : ℂ) * angularFourierIntegral g ξ *
        conj (angularFourierIntegral f ξ)) =
      ∫ y : Plane, (f y : ℂ) *
        ∫ x : Plane, (heatKernel (2 * s) (y - x) : ℂ) * (g x : ℂ) := by
  let H : Plane → Plane → ℂ := fun ξ y =>
    Complex.exp ((inner ℝ ξ y : ℝ) * Complex.I) *
      ((Real.exp (-s * ‖ξ‖ ^ 2) : ℂ) * (f y : ℂ)) * angularFourierIntegral g ξ
  have hb := ((integrable_gaussian_multiplier hs).ofReal (𝕜 := ℂ)).mul_prod
    (hf.ofReal (𝕜 := ℂ))
  have hphase : Continuous (fun p : Plane × Plane =>
      Complex.exp ((inner ℝ p.1 p.2 : ℝ) * Complex.I)) := by fun_prop
  have hF := continuous_angularFourierIntegral hg
  have hH : Integrable (Function.uncurry H) (volume.prod volume) := by
    apply (hb.norm.mul_const (∫ x : Plane, ‖g x‖)).mono'
      ((hphase.aestronglyMeasurable.mul hb.aestronglyMeasurable).mul
        (hF.comp continuous_fst).aestronglyMeasurable)
    filter_upwards [] with p
    change ‖Complex.exp ((inner ℝ p.1 p.2 : ℝ) * Complex.I) *
      ((Real.exp (-s * ‖p.1‖ ^ 2) : ℂ) * (f p.2 : ℂ)) * angularFourierIntegral g p.1‖ ≤ _
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact mul_le_mul_of_nonneg_left (norm_angularFourierIntegral_le g p.1)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have he (ξ : Plane) : (Real.exp (-s * ‖ξ‖ ^ 2) : ℂ) * angularFourierIntegral g ξ *
      conj (angularFourierIntegral f ξ) = ∫ y : Plane, H ξ y := by
    rw [conj_angularFourierIntegral, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp only [H]
    ring
  simp_rw [he]
  rw [integral_integral_swap hH, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  have hi : (∫ ξ : Plane, H ξ y) = (f y : ℂ) *
      ∫ ξ : Plane, (Real.exp (-s * ‖ξ‖ ^ 2) : ℂ) *
        Complex.exp ((inner ℝ ξ y : ℝ) * Complex.I) * angularFourierIntegral g ξ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ξ
    dsimp only [H]
    ring
  rw [hi, mul_left_comm, integral_gaussian_angularFourier hs hg]

/-- Absolute integrability of the complex spectral pairing at positive time. -/
theorem integrable_heat_fourier_pairing_complex {f g : Plane → ℝ}
    (hf : Integrable f) (hg : Integrable g) {s : ℝ} (hs : 0 < s) :
    Integrable (fun ξ : Plane => (Real.exp (-s * ‖ξ‖ ^ 2) : ℂ) *
      angularFourierIntegral g ξ * conj (angularFourierIntegral f ξ)) := by
  have hf' := continuous_angularFourierIntegral hf
  have hg' := continuous_angularFourierIntegral hg
  have hm : Continuous (fun ξ : Plane => (Real.exp (-s * ‖ξ‖ ^ 2) : ℂ) *
      angularFourierIntegral g ξ * conj (angularFourierIntegral f ξ)) := by fun_prop
  apply ((integrable_gaussian_multiplier hs).mul_const
    ((∫ x : Plane, ‖g x‖) * ∫ x : Plane, ‖f x‖)).mono' hm.aestronglyMeasurable
  filter_upwards [] with ξ
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_conj, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (norm_angularFourierIntegral_le g ξ) (norm_angularFourierIntegral_le f ξ)
      (norm_nonneg _) (integral_nonneg fun x => norm_nonneg (g x))) (Real.exp_nonneg _)


/-- Angular-convention heat Plancherel. It holds for all integrable real inputs,
and hence for the bounded integrable inputs needed by the mollifier argument. -/
theorem inner_heatSemigroup_eq_fourier {f g : Plane → ℝ}
    (hf : Integrable f) (hg : Integrable g) {s : ℝ} (hs : 0 < s) :
    (∫ x : Plane, f x * heatSmooth (2 * s) g x) =
      (2 * Real.pi)⁻¹ ^ 2 * ∫ ξ : Plane,
        (fourierKPZ f ξ * conj (fourierKPZ g ξ)).re * Real.exp (-s * ‖ξ‖ ^ 2) := by
  have h := congrArg Complex.re (inner_heatSemigroup_eq_fourier_complex hf hg hs)
  simp_rw [heatSmooth, fourierKPZ_eq_angularFourierIntegral_fun]
  have hp (ξ : Plane) :
      ((Real.exp (-s * ‖ξ‖ ^ 2) : ℂ) * angularFourierIntegral g ξ *
        conj (angularFourierIntegral f ξ)).re =
      (angularFourierIntegral f ξ * conj (angularFourierIntegral g ξ)).re *
        Real.exp (-s * ‖ξ‖ ^ 2) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im]
    ring
  have hsp : (∫ y : Plane, (f y : ℂ) *
      ∫ x : Plane, (heatKernel (2 * s) (y - x) : ℂ) * (g x : ℂ)) =
      Complex.ofReal (∫ y : Plane, f y * ∫ x : Plane, heatKernel (2 * s) (y - x) * g x) := by
    simp only [← Complex.ofReal_mul, integral_complex_ofReal]
  rw [hsp] at h
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  have hre : (∫ ξ : Plane, (Real.exp (-s * ‖ξ‖ ^ 2) : ℂ) * angularFourierIntegral g ξ *
      conj (angularFourierIntegral f ξ)).re = ∫ ξ : Plane,
      ((Real.exp (-s * ‖ξ‖ ^ 2) : ℂ) * angularFourierIntegral g ξ *
        conj (angularFourierIntegral f ξ)).re := by
    exact (integral_re (integrable_heat_fourier_pairing_complex hf hg hs)).symm
  rw [hre] at h
  simp_rw [hp] at h
  exact h.symm


/-- Cancellation at frequency zero gives a linear Fourier bound from the first moment. -/
theorem norm_fourierKPZ_le_of_integral_zero {f : Plane → ℝ} (hf : Integrable f)
    (hzero : (∫ x : Plane, f x) = 0)
    (hmoment : Integrable (fun x : Plane => ‖x‖ * |f x|)) (ξ : Plane) :
    ‖fourierKPZ f ξ‖ ≤ ‖ξ‖ * ∫ x : Plane, ‖x‖ * |f x| := by
  rw [fourierKPZ_eq_angularFourierIntegral_fun]
  have hphase : Integrable (fun x : Plane =>
      Complex.exp ((-inner ℝ ξ x : ℝ) * Complex.I) * (f x : ℂ)) := by
    apply (hf.ofReal (𝕜 := ℂ)).bdd_mul
    · exact (by fun_prop : Continuous (fun x : Plane =>
        Complex.exp ((-inner ℝ ξ x : ℝ) * Complex.I))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x =>
        (Complex.norm_exp_ofReal_mul_I (-inner ℝ ξ x)).le
  have heq : angularFourierIntegral f ξ = ∫ x : Plane,
      (Complex.exp ((-inner ℝ ξ x : ℝ) * Complex.I) - 1) * (f x : ℂ) := by
    have hzeroC : (∫ x : Plane, (f x : ℂ)) = 0 := by
      rw [integral_complex_ofReal, hzero, Complex.ofReal_zero]
    calc
      _ = (∫ x : Plane, Complex.exp ((-inner ℝ ξ x : ℝ) * Complex.I) * (f x : ℂ)) -
          ∫ x : Plane, (f x : ℂ) := by rw [hzeroC, sub_zero]; rfl
      _ = ∫ x : Plane, Complex.exp ((-inner ℝ ξ x : ℝ) * Complex.I) * (f x : ℂ) -
          (f x : ℂ) := (integral_sub hphase (hf.ofReal (𝕜 := ℂ))).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
  rw [heq, ← integral_const_mul]
  apply norm_integral_le_of_norm_le (hmoment.const_mul ‖ξ‖)
  filter_upwards [] with x
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have he : ‖Complex.exp ((-inner ℝ ξ x : ℝ) * Complex.I) - 1‖ ≤ ‖inner ℝ ξ x‖ := by
    simpa only [mul_comm, norm_neg] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := -inner ℝ ξ x))
  calc
    _ ≤ (‖ξ‖ * ‖x‖) * |f x| :=
      mul_le_mul_of_nonneg_right (he.trans (norm_inner_le_norm ξ x)) (abs_nonneg _)
    _ = _ := mul_assoc _ _ _

/-- Plancherel gives absolute integrability of the squared Fourier norm. -/
theorem integrable_norm_fourierKPZ_sq {f : Plane → ℝ}
    (hf : Integrable f) (hf2 : MemLp f 2 volume) :
    Integrable (fun ξ : Plane => ‖fourierKPZ f ξ‖ ^ 2) := by
  simp_rw [fourierKPZ_eq_angularFourierIntegral_fun]
  refine ⟨((continuous_angularFourierIntegral hf).norm.pow 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ξ => sq_nonneg _)]
  have hr : (∫⁻ x : Plane, ENNReal.ofReal (f x ^ 2)) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => sq_nonneg _)).mp
      hf2.integrable_sq.hasFiniteIntegral
  have h := (lintegral_angularFourier_norm_sq hf hf2).trans_lt hr
  exact ENNReal.lt_top_of_mul_ne_top_right h.ne (by positivity)

/-- A mean-zero `L¹ ∩ L²` pair with finite first moments has an absolutely
integrable inverse-Laplacian Fourier pairing. -/
theorem integrable_fourierKPZ_pairing_div_norm_sq {f g : Plane → ℝ}
    (hf : Integrable f) (hg : Integrable g) (hf2 : MemLp f 2 volume) (hg2 : MemLp g 2 volume)
    (hfzero : (∫ x : Plane, f x) = 0) (hgzero : (∫ x : Plane, g x) = 0)
    (hfm : Integrable (fun x : Plane => ‖x‖ * |f x|))
    (hgm : Integrable (fun x : Plane => ‖x‖ * |g x|)) :
    Integrable (fun ξ : Plane => (fourierKPZ f ξ * conj (fourierKPZ g ξ)).re / ‖ξ‖ ^ 2) := by
  let M := (∫ x : Plane, ‖x‖ * |f x|) * ∫ x : Plane, ‖x‖ * |g x|
  have hM : 0 ≤ M := mul_nonneg (integral_nonneg fun x => mul_nonneg (norm_nonneg _) (abs_nonneg _))
    (integral_nonneg fun x => mul_nonneg (norm_nonneg _) (abs_nonneg _))
  have hlocal : Integrable ((Metric.ball (0 : Plane) 1).indicator (fun _ => M)) := by
    exact (integrableOn_const (show volume (Metric.ball (0 : Plane) 1) < ⊤ from measure_ball_lt_top).ne).integrable_indicator
      Metric.isOpen_ball.measurableSet
  have hglobal := (integrable_norm_fourierKPZ_sq hf hf2).add (integrable_norm_fourierKPZ_sq hg hg2)
  have hF : Continuous (fourierKPZ f) := by
    change Continuous (fun ξ => fourierKPZ f ξ)
    simp_rw [fourierKPZ_eq_angularFourierIntegral_fun]
    exact continuous_angularFourierIntegral hf
  have hG : Continuous (fourierKPZ g) := by
    change Continuous (fun ξ => fourierKPZ g ξ)
    simp_rw [fourierKPZ_eq_angularFourierIntegral_fun]
    exact continuous_angularFourierIntegral hg
  apply (hlocal.add hglobal).mono'
    ((Complex.continuous_re.comp (hF.mul (Complex.continuous_conj.comp hG))).measurable.div (continuous_norm.pow 2).measurable).aestronglyMeasurable
  filter_upwards [] with ξ
  have hp : |(fourierKPZ f ξ * conj (fourierKPZ g ξ)).re| ≤
      ‖fourierKPZ f ξ‖ * ‖fourierKPZ g ξ‖ := by
    simpa only [norm_mul, Complex.norm_conj] using
      Complex.abs_re_le_norm (fourierKPZ f ξ * conj (fourierKPZ g ξ))
  change ‖(fourierKPZ f ξ * conj (fourierKPZ g ξ)).re / ‖ξ‖ ^ 2‖ ≤
    (Metric.ball (0 : Plane) 1).indicator (fun _ => M) ξ +
      (‖fourierKPZ f ξ‖ ^ 2 + ‖fourierKPZ g ξ‖ ^ 2)
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg ‖ξ‖)]
  by_cases hsmall : ξ ∈ Metric.ball (0 : Plane) 1
  · rw [Set.indicator_of_mem hsmall]
    have hlow : ‖fourierKPZ f ξ‖ * ‖fourierKPZ g ξ‖ ≤ ‖ξ‖ ^ 2 * M := by
      have h := mul_le_mul (norm_fourierKPZ_le_of_integral_zero hf hfzero hfm ξ)
        (norm_fourierKPZ_le_of_integral_zero hg hgzero hgm ξ) (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (integral_nonneg fun x => mul_nonneg (norm_nonneg _) (abs_nonneg _)))
      dsimp only [M]
      convert h using 1
      ring
    have hq : |(fourierKPZ f ξ * conj (fourierKPZ g ξ)).re| / ‖ξ‖ ^ 2 ≤ M := by
      by_cases hz : ξ = 0
      · subst ξ; simpa only [norm_zero, zero_pow two_ne_zero, div_zero] using hM
      · exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hz))).mpr (hp.trans (hlow.trans_eq (mul_comm _ _)))
    exact hq.trans (le_add_of_nonneg_right (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  · rw [Set.indicator_of_notMem hsmall, zero_add]
    have hnorm : 1 ≤ ‖ξ‖ := le_of_not_gt (fun h => hsmall (mem_ball_zero_iff.mpr h))
    have hsquare : 1 ≤ ‖ξ‖ ^ 2 := one_le_pow₀ hnorm
    have hprod : ‖fourierKPZ f ξ‖ * ‖fourierKPZ g ξ‖ ≤
        ‖fourierKPZ f ξ‖ ^ 2 + ‖fourierKPZ g ξ‖ ^ 2 := by
      nlinarith only [sq_nonneg (‖fourierKPZ f ξ‖ - ‖fourierKPZ g ξ‖), sq_nonneg ‖fourierKPZ f ξ‖,
        sq_nonneg ‖fourierKPZ g ξ‖]
    exact (div_le_self (abs_nonneg _) hsquare).trans (hp.trans hprod)

/-- Integration of a positive-time Fourier multiplier, with absolute convergence
in the product of frequency and time. -/
theorem integrable_fourier_time_kernel (k : Plane → ℝ) (hk : Measurable k)
    (hq : Integrable (fun ξ : Plane => k ξ / ‖ξ‖ ^ 2)) :
    Integrable (fun p : Plane × ℝ => k p.1 * Real.exp (-p.2 * ‖p.1‖ ^ 2))
      (volume.prod (volume.restrict (Set.Ioi 0))) ∧
    (∫ s in Set.Ioi (0 : ℝ), ∫ ξ : Plane, k ξ * Real.exp (-s * ‖ξ‖ ^ 2)) =
      ∫ ξ : Plane, k ξ / ‖ξ‖ ^ 2 := by
  have he (ξ : Plane) (hξ : ξ ≠ 0) :
      IntegrableOn (fun s : ℝ => Real.exp (-s * ‖ξ‖ ^ 2)) (Set.Ioi 0) ∧
      (∫ s in Set.Ioi (0 : ℝ), Real.exp (-s * ‖ξ‖ ^ 2)) = (‖ξ‖ ^ 2)⁻¹ := by
    have hn : -‖ξ‖ ^ 2 < 0 := neg_neg_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hξ))
    have hefun : (fun t : ℝ => Real.exp (-t * ‖ξ‖ ^ 2)) =
        (fun t : ℝ => Real.exp ((-‖ξ‖ ^ 2) * t)) := by
      funext t
      congr 1
      ring
    rw [hefun]
    constructor
    · exact integrableOn_exp_mul_Ioi hn 0
    · rw [integral_exp_mul_Ioi hn 0]
      simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div]
  have hne : ∀ᵐ ξ : Plane ∂volume, ξ ≠ 0 := by
    rw [ae_iff]
    simp only [not_not, Set.ofPred_eq_eq_singleton, measure_singleton]
  have hmeas : AEStronglyMeasurable (fun p : Plane × ℝ => k p.1 * Real.exp (-p.2 * ‖p.1‖ ^ 2))
      (volume.prod (volume.restrict (Set.Ioi 0))) := by
    apply Measurable.aestronglyMeasurable
    exact (hk.comp measurable_fst).mul (by fun_prop)
  have hjoint : Integrable (fun p : Plane × ℝ => k p.1 * Real.exp (-p.2 * ‖p.1‖ ^ 2))
      (volume.prod (volume.restrict (Set.Ioi 0))) := by
    apply (integrable_prod_iff hmeas).mpr
    constructor
    · filter_upwards [hne] with ξ hξ
      exact (he ξ hξ).1.const_mul (k ξ)
    · apply hq.norm.congr
      filter_upwards [hne] with ξ hξ
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg ‖ξ‖)]
      simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
        MeasureTheory.integral_const_mul, (he ξ hξ).2, div_eq_mul_inv]
  refine ⟨hjoint, ?_⟩
  have hswap : Integrable (Function.uncurry (fun s : ℝ => fun ξ : Plane =>
      k ξ * Real.exp (-s * ‖ξ‖ ^ 2))) ((volume.restrict (Set.Ioi 0)).prod volume) := hjoint.swap
  rw [integral_integral_swap hswap]
  apply integral_congr_ae
  filter_upwards [hne] with ξ hξ
  rw [MeasureTheory.integral_const_mul, (he ξ hξ).2, div_eq_mul_inv]

/-- The positive-time heat pairing is absolutely integrable, and its time
integral is the inverse-Laplacian Fourier pairing. -/
theorem integral_inner_heatSemigroup_eq_fourier {f g : Plane → ℝ}
    (hf : Integrable f) (hg : Integrable g) (hf2 : MemLp f 2 volume) (hg2 : MemLp g 2 volume)
    (hfzero : (∫ x : Plane, f x) = 0) (hgzero : (∫ x : Plane, g x) = 0)
    (hfm : Integrable (fun x : Plane => ‖x‖ * |f x|))
    (hgm : Integrable (fun x : Plane => ‖x‖ * |g x|)) :
    IntegrableOn (fun s : ℝ => ∫ x : Plane, f x * heatSmooth (2 * s) g x) (Set.Ioi 0) ∧
    (∫ s in Set.Ioi (0 : ℝ), ∫ x : Plane, f x * heatSmooth (2 * s) g x) =
      (2 * Real.pi)⁻¹ ^ 2 * ∫ ξ : Plane,
        (fourierKPZ f ξ * conj (fourierKPZ g ξ)).re / ‖ξ‖ ^ 2 := by
  have hF : Continuous (fun ξ => fourierKPZ f ξ) := by
    simp_rw [fourierKPZ_eq_angularFourierIntegral_fun]
    exact continuous_angularFourierIntegral hf
  have hG : Continuous (fun ξ => fourierKPZ g ξ) := by
    simp_rw [fourierKPZ_eq_angularFourierIntegral_fun]
    exact continuous_angularFourierIntegral hg
  have hq := integrable_fourierKPZ_pairing_div_norm_sq hf hg hf2 hg2 hfzero hgzero hfm hgm
  obtain ⟨hj, heq⟩ := integrable_fourier_time_kernel
    (fun ξ => (fourierKPZ f ξ * conj (fourierKPZ g ξ)).re)
    (Complex.continuous_re.comp (hF.mul (Complex.continuous_conj.comp hG))).measurable hq
  constructor
  · apply (hj.swap.integral_prod_left.const_mul ((2 * Real.pi)⁻¹ ^ 2)).congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact (inner_heatSemigroup_eq_fourier hf hg hs).symm
  · calc
      _ = ∫ s in Set.Ioi (0 : ℝ), (2 * Real.pi)⁻¹ ^ 2 * ∫ ξ : Plane,
          (fourierKPZ f ξ * conj (fourierKPZ g ξ)).re * Real.exp (-s * ‖ξ‖ ^ 2) :=
        setIntegral_congr_fun measurableSet_Ioi fun s hs => inner_heatSemigroup_eq_fourier hf hg hs
      _ = _ := by rw [MeasureTheory.integral_const_mul, heq]






/-- The convolution defining heat smoothing is an honest absolutely convergent
integral for integrable inputs at positive times. -/
theorem integrable_heatSmooth_integrand {g : Plane → ℝ} (hg : Integrable g)
    {s : ℝ} (hs : 0 < s) (x : Plane) :
    Integrable (fun y : Plane => heatKernel s (x - y) * g y) := by
  apply hg.bdd_mul
  · exact ((continuous_heatKernel s).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg hs.le _)]
    exact heatKernel_le_at_zero hs.le _

/-- At fixed positive time the spatial heat pairing is absolutely integrable.
This supplies the finiteness assertion for both quantitative heat bounds. -/
theorem integrable_inner_heatSemigroup {f g : Plane → ℝ}
    (hf : Integrable f) (hg : Integrable g) {s : ℝ} (hs : 0 < s) :
    Integrable (fun x : Plane => f x * heatSmooth (2 * s) g x) := by
  have hs' : 0 < 2 * s := mul_pos two_pos hs
  let C : ℝ := (2 * Real.pi * (2 * s))⁻¹
  have hm : AEStronglyMeasurable (fun p : Plane × Plane =>
      heatKernel (2 * s) (p.1 - p.2) * g p.2) (volume.prod volume) :=
    (((continuous_heatKernel (2 * s)).comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable).mul
      hg.aestronglyMeasurable.comp_snd
  have hheat : AEStronglyMeasurable (heatSmooth (2 * s) g) volume := hm.integral_prod_right'
  have hb (x : Plane) : ‖heatSmooth (2 * s) g x‖ ≤ C * ∫ y : Plane, ‖g y‖ := by
    rw [heatSmooth, ← MeasureTheory.integral_const_mul]
    apply norm_integral_le_of_norm_le (hg.norm.const_mul C)
    filter_upwards [] with y
    rw [norm_mul, Real.norm_eq_abs (heatKernel _ _),
      abs_of_nonneg (heatKernel_nonneg hs'.le _)]
    exact mul_le_mul_of_nonneg_right (heatKernel_le_at_zero hs'.le _) (norm_nonneg _)
  apply (hf.norm.mul_const (C * ∫ y : Plane, ‖g y‖)).mono'
    (hf.aestronglyMeasurable.mul hheat)
  filter_upwards [] with x
  change ‖f x * heatSmooth (2 * s) g x‖ ≤ ‖f x‖ * (C * ∫ y : Plane, ‖g y‖)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)


end Critical2DKPZ.Extensions.GffTangent

end

end
