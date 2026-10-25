/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.LogKernel
public import Critical2DKPZ.Extensions.GffTangent.HeatFourier
import Critical2DKPZ.Analysis.Heat.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Heat and Fourier representations of the logarithmic covariance

All time and spatial interchanges below carry product-integrability proofs.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ComplexConjugate

namespace Critical2DKPZ.Extensions.GffTangent

/-- The diagonal has zero product Lebesgue measure. -/
theorem ae_sub_ne_zero : ∀ᵐ p : Plane × Plane ∂(volume.prod volume), p.1 - p.2 ≠ 0 := by
  rw [ae_iff]
  simp only [not_not, sub_eq_zero]
  apply (Measure.measure_prod_null (isClosed_eq continuous_fst continuous_snd).measurableSet).mpr
  filter_upwards [] with x
  have heq : Prod.mk x ⁻¹' {p : Plane × Plane | p.1 = p.2} = {x} := by
    ext y
    simp only [mem_preimage, mem_ofPred_eq, mem_singleton_iff, eq_comm]
  rw [heq, measure_singleton]
  rfl

/-- Product absolute convergence for a finite heat-time interval. -/
theorem integrable_truncated_heat_pairing (f g : TestFn) (T : ℝ) (hT : 0 < T) :
    Integrable (fun p : (Plane × Plane) × ℝ =>
      f p.1.1 * g p.1.2 * heatKernel (2 * p.2) (p.1.1 - p.1.2))
      ((volume.prod volume).prod (volume.restrict (Ioc 0 T))) := by
  obtain ⟨C, hC, hCb⟩ := integral_heatKernel_two_mul_le T hT
  have hf : Integrable (f : Plane → ℝ) := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hg : Integrable (g : Plane → ℝ) := g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  have hfg := hf.mul_prod hg
  have hlog := integrable_log_kernel_mul f g
  have hm : AEStronglyMeasurable (fun p : (Plane × Plane) × ℝ =>
      f p.1.1 * g p.1.2 * heatKernel (2 * p.2) (p.1.1 - p.1.2))
      ((volume.prod volume).prod (volume.restrict (Ioc 0 T))) := by
    apply Measurable.aestronglyMeasurable
    unfold heatKernel
    fun_prop
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [ae_sub_ne_zero] with p hp
    exact (integral_heatKernel_two_mul T (p.1 - p.2) hT hp).1.const_mul (f p.1 * g p.2)
  · apply ((hfg.norm.add hlog.norm).const_mul C).mono' hm.norm.integral_prod_right'
    filter_upwards [ae_sub_ne_zero] with p hp
    have hnorm : (∫ s in Ioc (0 : ℝ) T,
        ‖f p.1 * g p.2 * heatKernel (2 * s) (p.1 - p.2)‖) =
        |f p.1 * g p.2| * ∫ s in Ioc (0 : ℝ) T, heatKernel (2 * s) (p.1 - p.2) := by
      rw [← MeasureTheory.integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      dsimp only
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg (by linarith only [hs.1]) _)]
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun s => norm_nonneg _), hnorm]
    have hb := mul_le_mul_of_nonneg_left (hCb T hT le_rfl (p.1 - p.2) hp) (abs_nonneg (f p.1 * g p.2))
    convert hb using 1
    simp only [Real.norm_eq_abs, abs_mul, Pi.add_apply]
    ring

/-- Fubini for the truncated heat pairing, retaining the spatial product integral. -/
theorem integral_truncated_heat_pairing (f g : TestFn) (T : ℝ) (hT : 0 < T) :
    (∫ s in Ioc (0 : ℝ) T, ∫ x : Plane, f x * heatSmooth (2 * s) g x) =
      ∫ p : Plane × Plane, f p.1 * g p.2 *
        (∫ s in Ioc (0 : ℝ) T, heatKernel (2 * s) (p.1 - p.2)) ∂(volume.prod volume) := by
  have hj := integrable_truncated_heat_pairing f g T hT
  have hslices := hj.prod_left_ae
  have heq : (∫ s in Ioc (0 : ℝ) T, ∫ p : Plane × Plane,
      f p.1 * g p.2 * heatKernel (2 * s) (p.1 - p.2) ∂(volume.prod volume)) =
      ∫ s in Ioc (0 : ℝ) T, ∫ x : Plane, f x * heatSmooth (2 * s) g x := by
    apply integral_congr_ae
    filter_upwards [hslices] with s hs
    rw [integral_prod _ hs]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [heatSmooth, ← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    ring
  rw [← heq]
  have hswap : Integrable (Function.uncurry (fun s : ℝ => fun p : Plane × Plane =>
      f p.1 * g p.2 * heatKernel (2 * s) (p.1 - p.2)))
      ((volume.restrict (Ioc 0 T)).prod (volume.prod volume)) := hj.swap
  rw [integral_integral_swap hswap]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [MeasureTheory.integral_const_mul]

/-- The finite-time heat pairing approaches the logarithmic covariance at rate
`1/T`. Compact support makes the exponential-integral remainder uniform. -/
theorem logCovariance_truncated_error (f g : TestFn)
    (hfzero : (∫ x : Plane, f x) = 0) :
    ∃ R : ℝ, 0 < R ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 0 < T → R ^ 2 ≤ T →
      |4 * Real.pi * (∫ s in Ioc (0 : ℝ) T, ∫ x : Plane, f x * heatSmooth (2 * s) g x) -
        2 * logCovariance f g| ≤ K / T := by
  obtain ⟨c, hc⟩ := integral_heatKernel_two_mul_expansion
  obtain ⟨R, hRpos, hR⟩ :=
    (f.hasCompactSupport.isCompact.union g.hasCompactSupport.isCompact).isBounded.exists_pos_norm_lt
  have hf : Integrable (f : Plane → ℝ) := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hg : Integrable (g : Plane → ℝ) := g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  have hfg := hf.mul_prod hg
  let M := ∫ p : Plane × Plane, |f p.1 * g p.2| ∂(volume.prod volume)
  have hM : 0 ≤ M := integral_nonneg fun p => abs_nonneg _
  refine ⟨R, hRpos, M * R ^ 2, mul_nonneg hM (sq_nonneg R), ?_⟩
  intro T hT hRT
  let F : Plane × Plane → ℝ := fun p => f p.1 * g p.2 *
    (4 * Real.pi * (∫ s in Ioc (0 : ℝ) T, heatKernel (2 * s) (p.1 - p.2)) -
      (c + Real.log (4 * T) - 2 * Real.log ‖p.1 - p.2‖))
  have hbound : ∀ᵐ p : Plane × Plane ∂(volume.prod volume),
      ‖F p‖ ≤ R ^ 2 / T * |f p.1 * g p.2| := by
    filter_upwards [ae_sub_ne_zero] with p hp
    by_cases hfp : f p.1 = 0
    · simp only [F, hfp, zero_mul, abs_zero, mul_zero, norm_zero, le_refl]
    by_cases hgp : g p.2 = 0
    · simp only [F, hgp, mul_zero, zero_mul, abs_zero, norm_zero, le_refl]
    have h1 : ‖p.1‖ < R := hR p.1 (Or.inl (subset_tsupport _ (Function.mem_support.mpr hfp)))
    have h2 : ‖p.2‖ < R := hR p.2 (Or.inr (subset_tsupport _ (Function.mem_support.mpr hgp)))
    have hnorm : ‖p.1 - p.2‖ ≤ 2 * R := (norm_sub_le _ _).trans (by linarith only [h1, h2])
    have hsquare : ‖p.1 - p.2‖ ^ 2 ≤ 4 * R ^ 2 := by
      have h := (sq_le_sq₀ (norm_nonneg (p.1 - p.2)) (by positivity : 0 ≤ 2 * R)).mpr hnorm
      nlinarith only [h]
    have h4 : ‖p.1 - p.2‖ ^ 2 ≤ 4 * T := hsquare.trans (by linarith only [hRT])
    have he := hc T hT (p.1 - p.2) hp h4
    have hdiv : ‖p.1 - p.2‖ ^ 2 / (4 * T) ≤ R ^ 2 / T := by
      apply (div_le_div_iff₀ (by positivity : 0 < 4 * T) hT).mpr
      nlinarith only [hsquare, hT]
    dsimp only [F]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (he.trans hdiv) (abs_nonneg _)).trans_eq (mul_comm _ _)
  have htrunc : Integrable (fun p : Plane × Plane => f p.1 * g p.2 *
      (∫ s in Ioc (0 : ℝ) T, heatKernel (2 * s) (p.1 - p.2))) (volume.prod volume) := by
    have ht := (integrable_truncated_heat_pairing f g T hT).integral_prod_left
    simpa only [MeasureTheory.integral_const_mul] using ht
  have hlog := integrable_log_kernel_mul f g
  have hFint : Integrable F (volume.prod volume) := by
    convert ((htrunc.const_mul (4 * Real.pi)).sub (hfg.const_mul (c + Real.log (4 * T)))).add
      (hlog.const_mul 2) using 1
    ext p
    dsimp only [F, Pi.add_apply, Pi.sub_apply]
    ring
  have hmass : (∫ p : Plane × Plane, f p.1 * g p.2 ∂(volume.prod volume)) = 0 := by
    rw [integral_prod_mul, hfzero, zero_mul]
  have hFIntegral : (∫ p : Plane × Plane, F p ∂(volume.prod volume)) =
      4 * Real.pi * (∫ s in Ioc (0 : ℝ) T, ∫ x : Plane, f x * heatSmooth (2 * s) g x) -
        2 * logCovariance f g := by
    have heqfun : F = (fun p => 4 * Real.pi * (f p.1 * g p.2 *
          (∫ s in Ioc (0 : ℝ) T, heatKernel (2 * s) (p.1 - p.2)))) -
        (fun p => (c + Real.log (4 * T)) * (f p.1 * g p.2)) +
        (fun p => 2 * (f p.1 * g p.2 * Real.log ‖p.1 - p.2‖)) := by
      funext p
      dsimp only [F, Pi.add_apply, Pi.sub_apply]
      ring
    rw [heqfun]
    simp only [Pi.add_apply, Pi.sub_apply]
    have hsum := integral_add
      ((htrunc.const_mul (4 * Real.pi)).sub (hfg.const_mul (c + Real.log (4 * T))))
      (hlog.const_mul 2)
    have hsub := integral_sub (htrunc.const_mul (4 * Real.pi))
      (hfg.const_mul (c + Real.log (4 * T)))
    simp only [Pi.sub_apply] at hsum hsub
    rw [hsum, hsub]
    simp only [MeasureTheory.integral_const_mul, hmass, mul_zero, sub_zero]
    rw [← integral_truncated_heat_pairing f g T hT]
    rw [logCovariance, ← integral_prod _ hlog]
    ring
  have hn := norm_integral_le_of_norm_le (hfg.norm.const_mul (R ^ 2 / T)) hbound
  rw [hFIntegral, Real.norm_eq_abs] at hn
  convert hn using 1
  simp only [MeasureTheory.integral_const_mul, Real.norm_eq_abs, M]
  ring

/-- A compactly supported smooth test has a finite absolute first moment. -/
theorem integrable_firstMoment_testFn (f : TestFn) :
    Integrable (fun x : Plane => ‖x‖ * |f x|) := by
  have h : Integrable (fun x : Plane => ‖x‖ * ‖f x‖) (volume : Measure Plane) :=
    (continuous_norm.mul f.continuous.norm).integrable_of_hasCompactSupport
      f.hasCompactSupport.norm.mul_left
  simpa only [Real.norm_eq_abs] using h

/-- The time--Fourier identity specialized to smooth compactly supported tests. -/
theorem integral_inner_heatSemigroup_testFn (f g : TestFn)
    (hfzero : (∫ x : Plane, f x) = 0) (hgzero : (∫ x : Plane, g x) = 0) :
    IntegrableOn (fun s : ℝ => ∫ x : Plane, f x * heatSmooth (2 * s) g x) (Ioi 0) ∧
    (∫ s in Ioi (0 : ℝ), ∫ x : Plane, f x * heatSmooth (2 * s) g x) =
      (2 * Real.pi)⁻¹ ^ 2 * ∫ ξ : Plane,
        (Spectral.fourierKPZ f ξ * conj (Spectral.fourierKPZ g ξ)).re / ‖ξ‖ ^ 2 :=
  integral_inner_heatSemigroup_eq_fourier
    (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)
    (g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport)
    (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport)
    (g.continuous.memLp_of_hasCompactSupport g.hasCompactSupport)
    hfzero hgzero (integrable_firstMoment_testFn f) (integrable_firstMoment_testFn g)

/-- The heat representation of the logarithmic covariance. -/
theorem logCovariance_eq_two_pi_integral (f g : TestFn)
    (hfzero : (∫ x : Plane, f x) = 0) (hgzero : (∫ x : Plane, g x) = 0) :
    logCovariance f g = 2 * Real.pi *
      ∫ s in Ioi (0 : ℝ), ∫ x : Plane, f x * heatSmooth (2 * s) g x := by
  obtain ⟨R, _, K, _, hb⟩ := logCovariance_truncated_error f g hfzero
  have htime := (integral_inner_heatSemigroup_testFn f g hfzero hgzero).1
  have ht : Filter.Tendsto (fun T : ℝ =>
      ∫ s in Ioc (0 : ℝ) T, ∫ x : Plane, f x * heatSmooth (2 * s) g x)
      Filter.atTop (nhds (∫ s in Ioi (0 : ℝ), ∫ x : Plane, f x * heatSmooth (2 * s) g x)) := by
    apply (intervalIntegral_tendsto_integral_Ioi 0 htime Filter.tendsto_id).congr'
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
    rw [id_eq, intervalIntegral.integral_of_le hT]
  have herror : Filter.Tendsto (fun T : ℝ =>
      |4 * Real.pi * (∫ s in Ioc (0 : ℝ) T, ∫ x : Plane, f x * heatSmooth (2 * s) g x) -
        2 * logCovariance f g|) Filter.atTop (nhds 0) := by
    have hKlim : Filter.Tendsto (fun T : ℝ => K / T) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop Filter.tendsto_id
    apply squeeze_zero' (Filter.Eventually.of_forall fun T => abs_nonneg _) ?_ hKlim
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ), Filter.eventually_ge_atTop (R ^ 2)] with T hT hRT
    exact hb T hT hRT
  have heq := abs_eq_zero.mp (tendsto_nhds_unique
    (((ht.const_mul (4 * Real.pi)).sub_const (2 * logCovariance f g)).abs) herror)
  linarith only [heq]

/-- Fourier representation in the angular convention of the note. -/
theorem logCovariance_eq_fourier (f g : TestFn)
    (hfzero : (∫ x : Plane, f x) = 0) (hgzero : (∫ x : Plane, g x) = 0) :
    logCovariance f g = (2 * Real.pi)⁻¹ * ∫ ξ : Plane,
      (Spectral.fourierKPZ f ξ * conj (Spectral.fourierKPZ g ξ)).re / ‖ξ‖ ^ 2 := by
  rw [logCovariance_eq_two_pi_integral f g hfzero hgzero,
    (integral_inner_heatSemigroup_testFn f g hfzero hgzero).2]
  have hc : (2 * Real.pi) * ((2 * Real.pi)⁻¹ ^ 2) = (2 * Real.pi)⁻¹ := by field_simp
  rw [← mul_assoc, hc]

/-- The Fourier normalization used in the linear GFF limit. -/
theorem four_pi_integral_eq_two_logCovariance (f g : TestFn)
    (hfzero : (∫ x : Plane, f x) = 0) (hgzero : (∫ x : Plane, g x) = 0) :
    4 * Real.pi * (∫ s in Ioi (0 : ℝ), ∫ x : Plane, f x * heatSmooth (2 * s) g x) =
      2 * logCovariance f g := by
  rw [logCovariance_eq_two_pi_integral f g hfzero hgzero]
  ring

/-- The logarithmic covariance as a bilinear form on real test functions. -/
def logCovarianceBilin : TestFn →ₗ[ℝ] TestFn →ₗ[ℝ] ℝ where
  toFun f :=
    { toFun := logCovariance f
      map_add' g h := logCovariance_add_right f g h
      map_smul' a g := logCovariance_smul_right a f g }
  map_add' f h := by
    ext g
    exact logCovariance_add_left f g h
  map_smul' a f := by
    ext g
    exact logCovariance_smul_left a f g

@[simp] theorem logCovarianceBilin_apply (f g : TestFn) :
    logCovarianceBilin f g = logCovariance f g := rfl

/-- The logarithmic quadratic form is nonnegative on zero-mass tests. -/
theorem logCovariance_self_nonneg (f : TestFn) (hfzero : (∫ x : Plane, f x) = 0) :
    0 ≤ logCovariance f f := by
  rw [logCovariance_eq_fourier f f hfzero hfzero]
  apply mul_nonneg (by positivity)
  apply integral_nonneg
  intro ξ
  change 0 ≤ (Spectral.fourierKPZ f ξ * conj (Spectral.fourierKPZ f ξ)).re / ‖ξ‖ ^ 2
  rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The logarithmic covariance matrix is positive semidefinite, also for empty,
repeated, and zero tests. -/
theorem posSemidef_logCovariance {n : ℕ} (f : Fin n → TestFn)
    (hfzero : ∀ i, (∫ x : Plane, f i x) = 0) :
    (Matrix.of fun i j => logCovariance (f i) (f j)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    exact logCovariance_symm (f j) (f i)
  · intro z
    let h : TestFn := ∑ i, z i • f i
    have hi (i : Fin n) : Integrable (fun x : Plane => z i * f i x) :=
      ((f i).continuous.integrable_of_hasCompactSupport (f i).hasCompactSupport).const_mul (z i)
    have hzero : (∫ x : Plane, h x) = 0 := by
      have heqfun : (fun x : Plane => h x) = fun x => ∑ i, z i * f i x := by
        funext x
        simp only [h, sum_apply, smul_apply, smul_eq_mul]
      rw [heqfun, integral_finsetSum _ fun i _ => hi i]
      simp only [MeasureTheory.integral_const_mul, hfzero, mul_zero, Finset.sum_const_zero]
    have heq : logCovariance h h = ∑ i, ∑ j, z i * logCovariance (f i) (f j) * z j := by
      change logCovarianceBilin h h = _
      simp only [h, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [logCovarianceBilin_apply]
      rw [logCovariance_symm (f j) (f i)]
      ring
    have hn := logCovariance_self_nonneg h hzero
    rw [heq] at hn
    simpa only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial, Finset.mul_sum,
      mul_assoc] using hn

end Critical2DKPZ.Extensions.GffTangent

end

end
