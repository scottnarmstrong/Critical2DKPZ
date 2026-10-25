/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.LinearCovariance
public import Critical2DKPZ.Extensions.GffTangent.LogKernelIdentities
public import Critical2DKPZ.Extensions.GffTangent.FlowMartingale
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonCovariance
public import Critical2DKPZ.Extensions.GffTangent.GaussianSplitting
public import Critical2DKPZ.Extensions.GffTangent.FiniteGaussian
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Moving-horizon linear covariance limits

Dominated convergence for the integrated collision primitive supplies the
covariance limit at subexponential growing horizons.
-/

public noncomputable section

open MeasureTheory Set Filter
open scoped Topology ComplexConjugate RealInnerProductSpace CompactlySupported

namespace Critical2DKPZ.Extensions.GffTangent

open Spectral Analysis.Sobolev

/-- Subtracting a fixed positive time does not change the subexponential
logarithmic scale of a horizon tending to infinity. -/
theorem tendsto_log_sub_div_self {T : ℝ → ℝ}
    (hT : Tendsto T atTop atTop)
    (hlog : Tendsto (fun l => Real.log (T l) / l) atTop (𝓝 0)) (s : ℝ) :
    Tendsto (fun l => Real.log (T l - s) / l) atTop (𝓝 0) := by
  have hTinverse : Tendsto (fun l => (T l)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hT
  have hratio : Tendsto (fun l => 1 - s * (T l)⁻¹) atTop (𝓝 1) := by
    simpa only [mul_zero, sub_zero] using
      tendsto_const_nhds.sub (tendsto_const_nhds.mul hTinverse)
  have hlogratio : Tendsto (fun l => Real.log (1 - s * (T l)⁻¹)) atTop (𝓝 0) := by
    simpa only [Real.log_one, Function.comp_def] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp hratio
  have hinvl : Tendsto (fun l : ℝ => l⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hsmall : Tendsto
      (fun l => Real.log (1 - s * (T l)⁻¹) / l) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hlogratio.mul hinvl
  have heq : ∀ᶠ l : ℝ in atTop,
      Real.log (T l - s) / l =
        Real.log (T l) / l + Real.log (1 - s * (T l)⁻¹) / l := by
    filter_upwards [hT.eventually_gt_atTop (max 0 s + 1)] with l hl
    have hTpos : 0 < T l := lt_of_le_of_lt (le_max_left 0 s) (by linarith)
    have hfac : 0 < 1 - s * (T l)⁻¹ := by
      have hsT : s / T l < 1 := (div_lt_one hTpos).2 (by
        linarith [le_max_right 0 s])
      simpa only [div_eq_mul_inv] using sub_pos.mpr hsT
    rw [show T l - s = T l * (1 - s * (T l)⁻¹) by field_simp [hTpos.ne'],
      Real.log_mul hTpos.ne' hfac.ne']
    ring
  have hsum : Tendsto (fun l => Real.log (T l) / l +
      Real.log (1 - s * (T l)⁻¹) / l) atTop (𝓝 0) := by
    simpa only [add_zero] using hlog.add hsmall
  exact hsum.congr' (heq.mono fun _ h => h.symm)

/-- Weighted dominated convergence for the moving collision primitive. -/
theorem tendsto_integral_mul_uFun_moving_horizon
    (H : ℝ → ℝ) (hH : IntegrableOn H (Ioi 0))
    (T : ℝ → ℝ) (hT : Tendsto T atTop atTop)
    (hlog : Tendsto (fun l => Real.log (T l) / l) atTop (𝓝 0)) :
    Tendsto (fun l =>
      l * ∫ s in Ioc 0 (T l), H s * uFun l (T l - s)) atTop
      (𝓝 (∫ s in Ioi 0, H s)) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℝ → ℝ → ℝ := fun l s =>
    (Iio (T l)).indicator (fun s => H s * (l * uFun l (T l - s))) s

  have hevent : ∀ᶠ l : ℝ in atTop,
      0 < l ∧ 0 < T l ∧ Real.log (T l) / l < 1 / 2 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hT.eventually_gt_atTop 0,
      hlog.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with l hl hTl hsmall
    exact ⟨hl, hTl, hsmall⟩

  have hFmeas : ∀ᶠ l : ℝ in atTop, AEStronglyMeasurable (F l) μ := by
    filter_upwards [hevent] with l hl
    apply AEStronglyMeasurable.indicator
    · exact hH.1.mul
        (((measurable_uFun.comp (measurable_const.prodMk
          (measurable_const.sub measurable_id))).const_mul l).aestronglyMeasurable)
    · exact measurableSet_Iio

  have hbound : ∀ᶠ l : ℝ in atTop, ∀ᵐ s ∂μ, ‖F l s‖ ≤ 2 * |H s| := by
    filter_upwards [hevent] with l hl
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    by_cases hsT : s < T l
    · have hsub : 0 < T l - s := sub_pos.mpr hsT
      have hmono : uFun l (T l - s) ≤ uFun l (T l) :=
        uFun_mono hsub (sub_le_self _ hs.le)
      have hloglt : Real.log (T l) < l := by
        have := hl.2.2
        exact (div_lt_one hl.1).mp (this.trans (by norm_num))
      have hU := uFun_pos_le hl.2.1 hloglt
      have hlogsub : Real.log (T l - s) < l := by
        have hlogle : Real.log (T l - s) ≤ Real.log (T l) :=
          Real.strictMonoOn_log.monotoneOn
            (mem_Ioi.mpr hsub) (mem_Ioi.mpr hl.2.1) (sub_le_self _ hs.le)
        exact hlogle.trans_lt hloglt
      have hUsub := uFun_pos_le hsub hlogsub
      have hnonneg : 0 ≤ l * uFun l (T l - s) :=
        mul_nonneg hl.1.le hUsub.1.le
      have htwo : l * uFun l (T l - s) ≤ 2 := by
        calc
          l * uFun l (T l - s) ≤ l * uFun l (T l) :=
            mul_le_mul_of_nonneg_left hmono hl.1.le
          _ ≤ l * (1 / (l - Real.log (T l))) :=
            mul_le_mul_of_nonneg_left hU.2 hl.1.le
          _ ≤ 2 := by
            rw [mul_one_div]
            apply (div_le_iff₀ (by linarith [hloglt])).2
            have := hl.2.2
            nlinarith [((div_lt_iff₀ hl.1).1 this)]
      change ‖(Iio (T l)).indicator (fun s => H s * (l * uFun l (T l - s))) s‖ ≤ _
      rw [Set.indicator_of_mem (show s ∈ Iio (T l) from hsT), norm_mul, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hnonneg]
      simpa only [mul_comm] using
        (mul_le_mul_of_nonneg_left htwo (abs_nonneg (H s)))
    · change ‖(Iio (T l)).indicator (fun s => H s * (l * uFun l (T l - s))) s‖ ≤ _
      rw [Set.indicator_of_notMem (show s ∉ Iio (T l) from hsT), norm_zero]
      exact mul_nonneg (by norm_num) (abs_nonneg _)

  have hpoint : ∀ᵐ s ∂μ, Tendsto (fun l => F l s) atTop (𝓝 (H s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hsubT : Tendsto (fun l => T l - s) atTop atTop := by
      simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-s) hT
    have hsubpos : ∀ l, 0 < max 1 (T l - s) := fun l => lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hsublog : Tendsto
        (fun l => Real.log (max 1 (T l - s)) / l) atTop (𝓝 0) := by
      have heq : ∀ᶠ l : ℝ in atTop, max 1 (T l - s) = T l - s :=
        (hsubT.eventually_gt_atTop 1).mono fun l hl => max_eq_right hl.le
      exact (tendsto_log_sub_div_self hT hlog s).congr'
        (heq.mono fun l hl => by
          change Real.log (T l - s) / l = Real.log (max 1 (T l - s)) / l
          rw [hl])
    have hU := tendsto_mul_uFun (fun l => max 1 (T l - s)) hsubpos hsublog
    have heq : ∀ᶠ l : ℝ in atTop,
        F l s = H s * (l * uFun l (max 1 (T l - s))) := by
      filter_upwards [hsubT.eventually_gt_atTop 1] with l hl
      have hsT : s < T l := by linarith
      rw [show max 1 (T l - s) = T l - s from max_eq_right hl.le]
      exact Set.indicator_of_mem (mem_Iio.mpr hsT) _
    have hmul : Tendsto (fun l => H s * (l * uFun l (max 1 (T l - s))))
        atTop (𝓝 (H s)) := by
      simpa only [mul_one] using hU.const_mul (H s)
    exact hmul.congr' (heq.mono fun _ h => h.symm)

  have hDCT : Tendsto (fun l => ∫ s, F l s ∂μ) atTop (𝓝 (∫ s, H s ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (bound := fun s => 2 * |H s|)
    · exact hFmeas
    · exact hbound
    · simpa only [Real.norm_eq_abs] using hH.norm.const_mul 2
    · exact hpoint

  apply hDCT.congr'
  filter_upwards [hevent] with l hl
  rw [show (∫ s, F l s ∂μ) =
      ∫ s in Ioo 0 (T l), H s * (l * uFun l (T l - s)) by
    change (∫ s, (Iio (T l)).indicator
      (fun s => H s * (l * uFun l (T l - s))) s ∂volume.restrict (Ioi 0)) = _
    rw [integral_indicator measurableSet_Iio,
      Measure.restrict_restrict measurableSet_Iio]
    rw [show Iio (T l) ∩ Ioi (0 : ℝ) = Ioo 0 (T l) by
      ext s
      simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo, and_comm]],
    ← integral_Ioc_eq_integral_Ioo]
  calc
    (∫ s in Ioc 0 (T l), H s * (l * uFun l (T l - s))) =
        ∫ s in Ioc 0 (T l), l * (H s * uFun l (T l - s)) := by
      apply integral_congr_ae
      filter_upwards [] with s
      ring
    _ = l * ∫ s in Ioc 0 (T l), H s * uFun l (T l - s) :=
      integral_const_mul _ _


/-- The rescaled covariance at a subexponential growing horizon converges to
its logarithmic value, with the normalization of the GFF tangent field. -/
theorem covariance_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : ∀ l, IsCriticalSHF (-l) P (Z l))
    (f g : TestFn) (hfzero : (∫ x : Plane, f x) = 0)
    (hgzero : (∫ x : Plane, g x) = 0)
    (T : ℝ → ℝ) (hT : Tendsto T atTop atTop)
    (hlog : Tendsto (fun l => Real.log (T l) / l) atTop (𝓝 0)) :
    Tendsto (fun l => l * ProbabilityTheory.covariance
      (shfPairing (Z l) 0 (T l) f (fun _ => 1))
      (shfPairing (Z l) 0 (T l) g (fun _ => 1)) P)
      atTop (𝓝 (2 * logCovariance f g)) := by
  have hf : Integrable (f : Plane → ℝ) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hg : Integrable (g : Plane → ℝ) :=
    g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  obtain ⟨Cf, hCf⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
  obtain ⟨Cg, hCg⟩ := g.hasCompactSupport.exists_bound_of_continuous g.continuous
  have hfbd : ∀ x, |f x| ≤ Cf := by
    simpa only [Real.norm_eq_abs] using hCf
  have hgbd : ∀ x, |g x| ≤ Cg := by
    simpa only [Real.norm_eq_abs] using hCg
  have hlim := (tendsto_integral_mul_uFun_moving_horizon
    (fun s => ∫ x : Plane, f x * heatSmooth (2 * s) g x)
    (integral_inner_heatSemigroup_testFn f g hfzero hgzero).1 T hT hlog).const_mul
      (4 * Real.pi)
  rw [four_pi_integral_eq_two_logCovariance f g hfzero hgzero] at hlim
  apply hlim.congr'
  filter_upwards [hT.eventually_gt_atTop 0] with l hl
  rw [covariance_shfPairing_start l P (Z l) (hZ l) (le_refl 0) hl
    f.continuous.measurable g.continuous.measurable hf hg hfbd hgbd]
  simp only [sub_zero]
  ring


/-- The rescaled square of the martingale tail converges to the heat-energy
tail beyond the fixed horizon. -/
theorem tendsto_variance_increment_tail
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : ∀ l, IsCriticalSHF (-l) P (Z l))
    (f : TestFn) (hfzero : (∫ x : Plane, f x) = 0)
    {T₀ : ℝ} (hT₀ : 0 < T₀)
    (T : ℝ → ℝ) (hT : Tendsto T atTop atTop)
    (hlog : Tendsto (fun l => Real.log (T l) / l) atTop (𝓝 0)) :
    Tendsto (fun l => l * ∫ ω,
      (shfPairing (Z l) 0 (T l) f (fun _ => 1) ω -
        shfPairing (Z l) 0 T₀ f (fun _ => 1) ω) ^ 2 ∂P) atTop
      (𝓝 (4 * Real.pi * ∫ s in Ioi T₀,
        ∫ x : Plane, f x * heatSmooth (2 * s) f x)) := by
  let fc : C_c(Plane, ℝ) := ⟨⟨(f : Plane → ℝ), f.continuous⟩, f.hasCompactSupport⟩
  have hfc : (fc : Plane → ℝ) = (f : Plane → ℝ) := rfl
  have hf : Integrable (f : Plane → ℝ) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  obtain ⟨C, hC⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
  have hfbd : ∀ x, |f x| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC
  let H : ℝ → ℝ := fun s => ∫ x : Plane, f x * heatSmooth (2 * s) f x
  have hHint : IntegrableOn H (Ioi 0) :=
    (integral_inner_heatSemigroup_testFn f f hfzero hfzero).1

  have hfullCov := covariance_limit P Z hZ f f hfzero hfzero T hT hlog
  have hfixedCov := covariance_fixed_horizon_limit P Z hZ hT₀ f f hfzero hfzero

  have hfullVar : Tendsto (fun l => l * ProbabilityTheory.variance
      (shfPairing (Z l) 0 (T l) f (fun _ => 1)) P)
      atTop (𝓝 (2 * logCovariance f f)) := by
    apply hfullCov.congr'
    filter_upwards [hT.eventually_gt_atTop 0] with l hTl
    have hm : MemLp (shfPairing (Z l) 0 (T l) f (fun _ => 1)) 2 P :=
      memLp_two_shfPairing_one l P (Z l) (hZ l) (by norm_num) hTl
        f.continuous.measurable hf hfbd
    rw [ProbabilityTheory.covariance_self hm.aemeasurable]

  have hfixedVar : Tendsto (fun l => l * ProbabilityTheory.variance
      (shfPairing (Z l) 0 T₀ f (fun _ => 1)) P) atTop
      (𝓝 (4 * Real.pi * ∫ s in Ioc 0 T₀, H s)) := by
    apply hfixedCov.congr'
    filter_upwards [] with l
    have hm : MemLp (shfPairing (Z l) 0 T₀ f (fun _ => 1)) 2 P :=
      memLp_two_shfPairing_one l P (Z l) (hZ l) (by norm_num) hT₀
        f.continuous.measurable hf hfbd
    rw [ProbabilityTheory.covariance_self hm.aemeasurable]

  have hdiff : Tendsto (fun l =>
      l * ProbabilityTheory.variance
          (shfPairing (Z l) 0 (T l) f (fun _ => 1)) P -
      l * ProbabilityTheory.variance
          (shfPairing (Z l) 0 T₀ f (fun _ => 1)) P) atTop
      (𝓝 (2 * logCovariance f f -
        4 * Real.pi * ∫ s in Ioc 0 T₀, H s)) :=
    hfullVar.sub hfixedVar

  have hincrement : Tendsto (fun l => l * ∫ ω,
      (shfPairing (Z l) 0 (T l) fc (fun _ => 1) ω -
        shfPairing (Z l) 0 T₀ fc (fun _ => 1) ω) ^ 2 ∂P) atTop
      (𝓝 (2 * logCovariance f f -
        4 * Real.pi * ∫ s in Ioc 0 T₀, H s)) := by
    apply hdiff.congr'
    filter_upwards [hT.eventually_gt_atTop T₀] with l hTl
    rw [variance_increment (-l) P (Z l) (hZ l) hT₀ hTl fc]
    simp only [hfc]
    ring

  have htail :
      2 * logCovariance f f - 4 * Real.pi * ∫ s in Ioc 0 T₀, H s =
        4 * Real.pi * ∫ s in Ioi T₀, H s := by
    have hfour := four_pi_integral_eq_two_logCovariance f f hfzero hfzero
    have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hHint hT₀.le
    rw [intervalIntegral.integral_of_le hT₀.le] at hsplit
    have hsplit' :
        (∫ s in Ioi (0 : ℝ), H s) - ∫ s in Ioc 0 T₀, H s =
          ∫ s in Ioi T₀, H s := by
      linarith only [hsplit]
    rw [← hfour]
    change 4 * Real.pi * (∫ s in Ioi (0 : ℝ), H s) -
      4 * Real.pi * (∫ s in Ioc 0 T₀, H s) =
        4 * Real.pi * (∫ s in Ioi T₀, H s)
    rw [← mul_sub, hsplit']

  rw [htail] at hincrement
  simpa only [H, hfc] using hincrement

/-- Uniform elementary `U` bound on a fixed horizon. -/
theorem mul_uFun_le_two_of_log_div_le {l T u : ℝ}
    (hl : 0 < l) (hT : 0 < T) (hu : 0 < u) (huT : u ≤ T)
    (hlog : Real.log T / l ≤ 1 / 2) :
    0 ≤ l * uFun l u ∧ l * uFun l u ≤ 2 := by
  have hlogT : Real.log T < l := by
    apply (div_lt_one hl).mp
    exact hlog.trans_lt (by norm_num)
  have hlogu : Real.log u < l :=
    (Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hu) (Set.mem_Ioi.mpr hT) huT).trans_lt hlogT
  have hUu := uFun_pos_le hu hlogu
  have hUT := uFun_pos_le hT hlogT
  constructor
  · exact mul_nonneg hl.le hUu.1.le
  · calc
      l * uFun l u ≤ l * uFun l T :=
        mul_le_mul_of_nonneg_left (uFun_mono hu huT) hl.le
      _ ≤ l * (1 / (l - Real.log T)) :=
        mul_le_mul_of_nonneg_left hUT.2 hl.le
      _ ≤ 2 := by
        rw [mul_one_div]
        apply (div_le_iff₀ (by linarith [hlogT])).2
        have hr := (div_le_iff₀ hl).1 hlog
        nlinarith

/-- The heat-mollification error has `L²(P)` mass and its moving-horizon
second moment is bounded by its full inverse-Laplacian energy. -/
theorem shfPairing_heatSmooth_sub_sq_le_energy
    {Ω : Type*} [MeasurableSpace Ω]
    (l : ℝ) (hl : 0 < l) (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF (-l) P Z)
    (f : TestFn) (hfzero : (∫ x : Plane, f x) = 0)
    {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hlog : Real.log T / l ≤ 1 / 2) :
    MemLp (shfPairing Z 0 T
      (fun x => heatSmooth δ f x - f x) (fun _ => 1)) 2 P ∧
    l * (∫ ω, shfPairing Z 0 T
      (fun x => heatSmooth δ f x - f x) (fun _ => 1) ω ^ 2 ∂P) ≤
      8 * Real.pi *
        ∫ s in Set.Ioi (0 : ℝ), ∫ x : Plane,
          (heatSmooth δ f x - f x) *
            heatSmooth (2 * s) (fun y => heatSmooth δ f y - f y) x := by
  let e : Plane → ℝ := fun x => heatSmooth δ f x - f x
  obtain ⟨Cf, hCf⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
  have hfbd : ∀ x, |f x| ≤ Cf := by
    simpa only [Real.norm_eq_abs] using hCf
  obtain ⟨hemeas, heint, hezero, hebd⟩ :=
    heatSmooth_sub_regular f hδ hfbd
  have heMem : MemLp (shfPairing Z 0 T e (fun _ => 1)) 2 P :=
    memLp_two_shfPairing_one l P Z hZ (a := 0) (T := T)
      (by norm_num) hT hemeas heint hebd
  refine ⟨heMem, ?_⟩
  let H : ℝ → ℝ := fun s => ∫ x : Plane, e x * heatSmooth (2 * s) e x
  have henergy := integral_heatSmooth_sub_energy_eq_fourier f hfzero hδ
  have hHint : IntegrableOn H (Set.Ioi 0) := by
    simpa only [H, e] using henergy.1
  have hHnonneg : ∀ s, 0 < s → 0 ≤ H s := by
    intro s hs
    have hfourier := inner_heatSemigroup_eq_fourier heint heint hs
    change 0 ≤ ∫ x : Plane, e x * heatSmooth (2 * s) e x
    rw [hfourier]
    apply mul_nonneg (sq_nonneg _)
    apply integral_nonneg
    intro ξ
    have hself : (fourierKPZ e ξ * conj (fourierKPZ e ξ)).re =
        ‖fourierKPZ e ξ‖ ^ 2 := by
      rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
    change 0 ≤ (fourierKPZ e ξ * conj (fourierKPZ e ξ)).re * Real.exp (-s * ‖ξ‖ ^ 2)
    rw [hself]
    exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  obtain ⟨hweighted, hmoment⟩ := second_moment_shfPairing
    l P Z hZ (a := 0) (T := T) (by norm_num) hT
    hemeas hemeas heint heint hebd hebd
  have hmoment' :
      (∫ ω, shfPairing Z 0 T e (fun _ => 1) ω ^ 2 ∂P) =
        4 * Real.pi * ∫ s in Set.Ioo 0 T, H s * uFun l (T - s) := by
    rw [show (fun ω => shfPairing Z 0 T e (fun _ => 1) ω ^ 2) =
      fun ω => shfPairing Z 0 T e (fun _ => 1) ω *
        shfPairing Z 0 T e (fun _ => 1) ω by funext ω; ring]
    simpa only [e, H, hezero, zero_mul, zero_add, sub_zero,
      integral_Ioc_eq_integral_Ioo] using hmoment
  have hweightedL : IntegrableOn
      (fun s => H s * (l * uFun l (T - s))) (Set.Ioo 0 T) := by
    have hw : IntegrableOn (fun s => H s * uFun l (T - s)) (Ioo 0 T) := by
      simpa only [H, sub_zero] using hweighted
    have := hw.const_mul l
    apply this.congr
    filter_upwards [] with s
    ring
  have htwoH : IntegrableOn (fun s => 2 * H s) (Set.Ioo 0 T) :=
    (hHint.mono_set Set.Ioo_subset_Ioi_self).const_mul 2
  have htrunc :
      ∫ s in Set.Ioo 0 T, H s * (l * uFun l (T - s)) ≤
        ∫ s in Set.Ioo 0 T, 2 * H s := by
    apply integral_mono_ae hweightedL htwoH
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hu : 0 < T - s := sub_pos.mpr hs.2
    have hU := mul_uFun_le_two_of_log_div_le hl hT hu
      (sub_le_self T hs.1.le) hlog
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hU.2 (hHnonneg s hs.1)
  have hsubset : (∫ s in Ioo 0 T, H s) ≤ ∫ s in Ioi 0, H s := by
    apply setIntegral_mono_set hHint
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact hHnonneg s hs
    · exact Filter.Eventually.of_forall fun s hs => hs.1
  rw [hmoment']
  calc
    l * (4 * Real.pi * ∫ s in Set.Ioo 0 T, H s * uFun l (T - s)) =
        4 * Real.pi * ∫ s in Set.Ioo 0 T,
          H s * (l * uFun l (T - s)) := by
      rw [show l * (4 * Real.pi * ∫ s in Ioo 0 T, H s * uFun l (T - s)) =
          4 * Real.pi * (l * ∫ s in Ioo 0 T, H s * uFun l (T - s)) by ring,
        ← MeasureTheory.integral_const_mul]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with s
      ring
    _ ≤ 4 * Real.pi * ∫ s in Set.Ioo 0 T, 2 * H s :=
      mul_le_mul_of_nonneg_left htrunc (by positivity)
    _ = 8 * Real.pi * ∫ s in Set.Ioo 0 T, H s := by
      rw [MeasureTheory.integral_const_mul]
      ring
    _ ≤ 8 * Real.pi * ∫ s in Set.Ioi 0, H s :=
      mul_le_mul_of_nonneg_left hsubset (by positivity)
    _ = _ := by rfl


/-- Heat smoothing with the identity convention at zero used in the source. -/
@[expose] noncomputable def heatSmooth' (δ : ℝ) (f : Plane → ℝ) : Plane → ℝ :=
  if δ = 0 then f else heatSmooth δ f

/-- Vanishing heat mollification produces a negligible rescaled mass error. -/
theorem mollifier_perturbation_small
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : ∀ l, IsCriticalSHF (-l) P (Z l))
    (f : TestFn) (hfzero : (∫ x : Plane, f x) = 0)
    (T : ℝ → ℝ) (hT : Tendsto T atTop atTop)
    (hlog : Tendsto (fun l => Real.log (T l) / l) atTop (𝓝 0))
    (δ : ℝ → ℝ) (hδ : ∀ l, 0 ≤ δ l) (hδlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun l => l * ∫ ω, shfPairing (Z l) 0 (T l)
      (fun x => heatSmooth' (δ l) f x - f x) (fun _ => 1) ω ^ 2 ∂P)
      atTop (𝓝 0) := by
  classical
  let η : ℝ → ℝ := fun l => if δ l = 0 then Real.exp (-l) else δ l
  have hηpos (l : ℝ) : 0 < η l := by
    dsimp only [η]
    split_ifs with h
    · exact Real.exp_pos _
    · exact lt_of_le_of_ne (hδ l) (Ne.symm h)
  have hα : Tendsto (fun l : ℝ => Real.exp (-l)) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hηlim : Tendsto η atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun l => δ l + Real.exp (-l))
    · exact Filter.Eventually.of_forall fun l => (hηpos l).le
    · exact Filter.Eventually.of_forall fun l => by
        dsimp only [η]
        split_ifs <;> linarith only [hδ l, (Real.exp_pos (-l)).le]
    · simpa only [add_zero] using hδlim.add hα
  let E : ℝ → ℝ := fun u => ∫ s in Ioi (0 : ℝ), ∫ x : Plane,
    (heatSmooth u f x - f x) *
      heatSmooth (2 * s) (fun y => heatSmooth u f y - f y) x
  have hElim : Tendsto (fun l => 8 * Real.pi * E (η l)) atTop (𝓝 0) := by
    have hηwithin : Tendsto η atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hηlim, Filter.Eventually.of_forall hηpos⟩
    have ht := (tendsto_integral_heatSmooth_sub_energy f hfzero).comp hηwithin
    simpa only [mul_zero, E, Function.comp_def] using ht.const_mul (8 * Real.pi)
  have hEnonneg (u : ℝ) (hu : 0 < u) : 0 ≤ E u := by
    rw [show E u = (2 * Real.pi)⁻¹ ^ 2 * ∫ ξ : Plane, ‖fourierKPZ f ξ‖ ^ 2 *
        (Real.exp (-(u / 2) * ‖ξ‖ ^ 2) - 1) ^ 2 / ‖ξ‖ ^ 2 from
      (integral_heatSmooth_sub_energy_eq_fourier f hfzero hu).2]
    exact mul_nonneg (sq_nonneg _) (integral_nonneg fun ξ =>
      div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))
  apply squeeze_zero' (g := fun l => 8 * Real.pi * E (η l))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with l hl
    exact mul_nonneg hl.le (integral_nonneg fun _ => sq_nonneg _)
  · filter_upwards [eventually_gt_atTop (0 : ℝ), hT.eventually_gt_atTop 0,
      hlog.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
        with l hl hTl hsmall
    by_cases hd : δ l = 0
    · simp only [heatSmooth', hd, ite_true, sub_self, shfPairing, zero_mul,
        integral_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
      exact mul_nonneg (by positivity) (hEnonneg (η l) (hηpos l))
    · have hδpos : 0 < δ l := lt_of_le_of_ne (hδ l) (Ne.symm hd)
      have hb := (shfPairing_heatSmooth_sub_sq_le_energy l hl P (Z l) (hZ l)
        f hfzero hTl hδpos hsmall.le).2
      simpa only [heatSmooth', ite_eq_right hd, η, E, ite_eq_right hd] using hb
  · exact hElim

/-- The second moment of the finite vector of normalized martingale tails is
the sum of the scalar heat-energy tails. -/
theorem tendsto_integral_norm_sq_tail_vector
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : ∀ l, IsCriticalSHF (-l) P (Z l))
    (f : Fin n → TestFn) (hfzero : ∀ i, (∫ x : Plane, f i x) = 0)
    {T₀ : ℝ} (hT₀ : 0 < T₀)
    (T : ℝ → ℝ) (hT : Tendsto T atTop atTop)
    (hlog : Tendsto (fun l => Real.log (T l) / l) atTop (𝓝 0)) :
    Tendsto (fun l => ∫ ω,
      ‖WithLp.toLp 2 (fun i : Fin n => Real.sqrt (l / 2) *
        (shfPairing (Z l) 0 (T l) (f i) (fun _ => 1) ω -
          shfPairing (Z l) 0 T₀ (f i) (fun _ => 1) ω))‖ ^ 2 ∂P) atTop
      (𝓝 (2 * Real.pi * ∑ i : Fin n, ∫ s in Ioi T₀,
        ∫ x : Plane, f i x * heatSmooth (2 * s) (f i) x)) := by
  let D : ℝ → Fin n → Ω → ℝ := fun l i ω =>
    shfPairing (Z l) 0 (T l) (f i) (fun _ => 1) ω -
      shfPairing (Z l) 0 T₀ (f i) (fun _ => 1) ω
  have hscalar (i : Fin n) :
      Tendsto (fun l => (1 / 2 : ℝ) * (l * ∫ ω, (D l i ω) ^ 2 ∂P)) atTop
        (𝓝 (2 * Real.pi * ∫ s in Ioi T₀,
          ∫ x : Plane, f i x * heatSmooth (2 * s) (f i) x)) := by
    have h := (tendsto_variance_increment_tail P Z hZ (f i) (hfzero i)
      hT₀ T hT hlog).const_mul (1 / 2 : ℝ)
    have hn : (1 / 2 : ℝ) * (4 * Real.pi * (∫ s in Ioi T₀,
        ∫ x : Plane, f i x * heatSmooth (2 * s) (f i) x)) =
      2 * Real.pi * (∫ s in Ioi T₀, ∫ x : Plane, f i x * heatSmooth (2 * s) (f i) x) := by ring
    rw [hn] at h
    simpa only [D] using h
  have hsum :
      Tendsto (fun l => ∑ i : Fin n, (1 / 2 : ℝ) *
        (l * ∫ ω, (D l i ω) ^ 2 ∂P)) atTop
        (𝓝 (∑ i : Fin n, 2 * Real.pi * ∫ s in Ioi T₀,
          ∫ x : Plane, f i x * heatSmooth (2 * s) (f i) x)) := by
    exact tendsto_finsetSum Finset.univ (fun i _ => hscalar i)
  have heq : ∀ᶠ l in atTop,
      (∫ ω, ‖WithLp.toLp 2 (fun i : Fin n => Real.sqrt (l / 2) * D l i ω)‖ ^ 2 ∂P) =
        ∑ i : Fin n, (1 / 2 : ℝ) * (l * ∫ ω, (D l i ω) ^ 2 ∂P) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hT.eventually_gt_atTop T₀] with l hl hTl
    have hmem (i : Fin n) : MemLp (D l i) 2 P := by
      have hfi : Integrable (f i : Plane → ℝ) :=
        (f i).continuous.integrable_of_hasCompactSupport (f i).hasCompactSupport
      obtain ⟨C, hC⟩ := (f i).hasCompactSupport.exists_bound_of_continuous (f i).continuous
      have hfbd : ∀ x, |f i x| ≤ C := by
        simpa only [Real.norm_eq_abs] using hC
      exact (memLp_two_shfPairing_one l P (Z l) (hZ l) (by norm_num)
        (hT₀.trans hTl) (f i).continuous.measurable hfi hfbd).sub
        (memLp_two_shfPairing_one l P (Z l) (hZ l) (by norm_num)
          hT₀ (f i).continuous.measurable hfi hfbd)
    calc
      _ = ∫ ω, ∑ i : Fin n, ‖Real.sqrt (l / 2) * D l i ω‖ ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards with ω
        simpa only [WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs] using
          EuclideanSpace.real_norm_sq_eq
            (WithLp.toLp 2 (fun i : Fin n => Real.sqrt (l / 2) * D l i ω))
      _ = ∑ i : Fin n, ∫ ω, ‖Real.sqrt (l / 2) * D l i ω‖ ^ 2 ∂P := by
        apply integral_finsetSum
        intro i hi
        simpa only [Real.norm_eq_abs, sq_abs] using
          ((hmem i).const_mul (Real.sqrt (l / 2))).integrable_sq
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [show (∫ ω, ‖Real.sqrt (l / 2) * D l i ω‖ ^ 2 ∂P) =
            (1 / 2 : ℝ) * (l * ∫ ω, (D l i ω) ^ 2 ∂P) by
          rw [show (fun ω => ‖Real.sqrt (l / 2) * D l i ω‖ ^ 2) =
              fun ω => (l / 2) * (D l i ω) ^ 2 by
            funext ω
            rw [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (by positivity)],
            integral_const_mul]
          ring]
  simpa only [D, Finset.mul_sum] using hsum.congr' (heq.mono fun _ h => h.symm)

/-- The deterministic finite collection of heat-energy tails vanishes when
the cutoff is `k + 1`. -/
theorem tendsto_heat_energy_tail_vector_zero
    {n : ℕ} (f : Fin n → TestFn)
    (hfzero : ∀ i, (∫ x : Plane, f i x) = 0) :
    Tendsto (fun k : ℕ => 2 * Real.pi * ∑ i : Fin n,
      ∫ s in Ioi ((k : ℝ) + 1),
        ∫ x : Plane, f i x * heatSmooth (2 * s) (f i) x) atTop (𝓝 0) := by
  have hk : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hi (i : Fin n) : Tendsto (fun k : ℕ =>
      ∫ s in Ioi ((k : ℝ) + 1),
        ∫ x : Plane, f i x * heatSmooth (2 * s) (f i) x) atTop (𝓝 0) := by
    have hInt : IntegrableOn (fun s =>
        ∫ x : Plane, f i x * heatSmooth (2 * s) (f i) x) (Ioi 0) :=
      (integral_inner_heatSemigroup_testFn (f i) (f i) (hfzero i) (hfzero i)).1
    exact tendsto_integral_Ioi_zero hk
  simpa only [Finset.sum_const_zero, mul_zero] using
    (tendsto_finsetSum Finset.univ (fun i _ => hi i)).const_mul (2 * Real.pi)

/-- A finite vector of heat-mollification errors is negligible in annealed
second moment at the GFF normalization.  The convention `heatSmooth' 0 f = f`
makes zero mollifier widths literal zero coordinates. -/
theorem tendsto_integral_norm_sq_mollifier_vector
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : ∀ l, IsCriticalSHF (-l) P (Z l))
    (f : Fin n → TestFn) (hfzero : ∀ i, (∫ x : Plane, f i x) = 0)
    (T : ℝ → ℝ) (hT : Tendsto T atTop atTop)
    (hlog : Tendsto (fun l => Real.log (T l) / l) atTop (𝓝 0))
    (δ : ℝ → ℝ) (hδ : ∀ l, 0 ≤ δ l) (hδlim : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun l => ∫ ω,
      ‖WithLp.toLp 2 (fun i : Fin n => Real.sqrt (l / 2) *
        shfPairing (Z l) 0 (T l)
          (fun x => heatSmooth' (δ l) (f i) x - f i x) (fun _ => 1) ω)‖ ^ 2 ∂P)
      atTop (𝓝 0) := by
  let D : ℝ → Fin n → Ω → ℝ := fun l i ω =>
    shfPairing (Z l) 0 (T l)
      (fun x => heatSmooth' (δ l) (f i) x - f i x) (fun _ => 1) ω
  have hscalar (i : Fin n) :
      Tendsto (fun l => (1 / 2 : ℝ) * (l * ∫ ω, (D l i ω) ^ 2 ∂P))
        atTop (𝓝 0) := by
    have h := (mollifier_perturbation_small P Z hZ (f i) (hfzero i)
      T hT hlog δ hδ hδlim).const_mul (1 / 2 : ℝ)
    simpa only [D, mul_zero] using h
  have hsum : Tendsto (fun l => ∑ i : Fin n,
      (1 / 2 : ℝ) * (l * ∫ ω, (D l i ω) ^ 2 ∂P)) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun i _ => hscalar i)
  have heq : ∀ᶠ l in atTop,
      (∫ ω, ‖WithLp.toLp 2 (fun i : Fin n =>
          Real.sqrt (l / 2) * D l i ω)‖ ^ 2 ∂P) =
        ∑ i : Fin n, (1 / 2 : ℝ) * (l * ∫ ω, (D l i ω) ^ 2 ∂P) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), hT.eventually_gt_atTop 0]
      with l hl hTl
    have hmem (i : Fin n) : MemLp (D l i) 2 P := by
      by_cases hd : δ l = 0
      · have hz : D l i = (0 : Ω → ℝ) := by
          funext ω
          simp only [D, heatSmooth', hd, ite_true, sub_self, shfPairing, zero_mul,
            integral_zero, Pi.zero_apply]
        rw [hz]
        exact MemLp.zero
      · have hδpos : 0 < δ l := lt_of_le_of_ne (hδ l) (Ne.symm hd)
        obtain ⟨C, hC⟩ :=
          (f i).hasCompactSupport.exists_bound_of_continuous (f i).continuous
        have hfbd : ∀ x, |f i x| ≤ C := by
          simpa only [Real.norm_eq_abs] using hC
        obtain ⟨hemeas, heint, _hezero, hebd⟩ :=
          heatSmooth_sub_regular (f i) hδpos hfbd
        have hm := memLp_two_shfPairing_one l P (Z l) (hZ l)
          (a := 0) (T := T l) (by norm_num) hTl hemeas heint hebd
        simpa only [D, heatSmooth', hd, ite_false] using hm
    calc
      _ = ∫ ω, ∑ i : Fin n, ‖Real.sqrt (l / 2) * D l i ω‖ ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards with ω
        simpa only [WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs] using
          EuclideanSpace.real_norm_sq_eq
            (WithLp.toLp 2 (fun i : Fin n => Real.sqrt (l / 2) * D l i ω))
      _ = ∑ i : Fin n, ∫ ω, ‖Real.sqrt (l / 2) * D l i ω‖ ^ 2 ∂P := by
        apply integral_finsetSum
        intro i hi
        simpa only [Real.norm_eq_abs, sq_abs] using
          ((hmem i).const_mul (Real.sqrt (l / 2))).integrable_sq
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [show (∫ ω, ‖Real.sqrt (l / 2) * D l i ω‖ ^ 2 ∂P) =
            (1 / 2 : ℝ) * (l * ∫ ω, (D l i ω) ^ 2 ∂P) by
          rw [show (fun ω => ‖Real.sqrt (l / 2) * D l i ω‖ ^ 2) =
              fun ω => (l / 2) * (D l i ω) ^ 2 by
            funext ω
            rw [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (by positivity)]
            ,
            integral_const_mul]
          ring]
  simpa only [D] using hsum.congr' (heq.mono fun _ h => h.symm)

/-- Regularity of the source convention `heatSmooth'`, including its identity
branch at zero. -/
theorem heatSmooth'_regular (f : TestFn) {δ C : ℝ} (hδ : 0 ≤ δ)
    (hC : ∀ x, |f x| ≤ C) :
    Measurable (heatSmooth' δ f) ∧
    Integrable (heatSmooth' δ f) ∧
    (∫ x : Plane, heatSmooth' δ f x) = ∫ x : Plane, f x ∧
    ∀ x, |heatSmooth' δ f x| ≤ C := by
  by_cases hd : δ = 0
  · subst δ
    have hf : Integrable (f : Plane → ℝ) :=
      f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
    simpa only [heatSmooth', ite_true] using
      (show Measurable (f : Plane → ℝ) ∧ Integrable (f : Plane → ℝ) ∧
        (∫ x : Plane, f x) = ∫ x : Plane, f x ∧ ∀ x, |f x| ≤ C from
        ⟨f.continuous.measurable, hf, rfl, hC⟩)
  · have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hd)
    have hf : Integrable (f : Plane → ℝ) :=
      f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
    simp only [heatSmooth', ite_eq_right hd]
    exact ⟨measurable_heatSmooth_testFn f δ,
      integrable_heatSmooth hf hδpos, integral_heatSmooth_eq f hδpos,
      abs_heatSmooth_le f hδpos hC⟩

/-- Coordinatewise `L²` control gives `L²` control of a finite Euclidean
vector. -/
theorem memLp_two_euclidean_of_forall
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : Fin n → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 P) :
    MemLp (fun ω => WithLp.toLp 2 (fun i => X i ω)) 2 P := by
  exact MemLp.of_eval_piLp hX

/-- Finite vectors of scalar SHF flat pairings are genuinely in `L²`. -/
theorem memLp_two_shfPairing_one_vector
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (l : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF (-l) P Z)
    {a T : ℝ} (ha : 0 ≤ a) (haT : a < T)
    (f : Fin n → Plane → ℝ)
    (hf : ∀ i, Measurable (f i))
    (hf1 : ∀ i, Integrable (f i))
    (C : Fin n → ℝ) (hfbd : ∀ i x, |f i x| ≤ C i)
    (c : ℝ) :
    MemLp (fun ω => WithLp.toLp 2 (fun i =>
      c * shfPairing Z a T (f i) (fun _ => 1) ω)) 2 P := by
  apply memLp_two_euclidean_of_forall
  intro i
  exact (memLp_two_shfPairing_one l P Z hZ ha haT
    (hf i) (hf1 i) (hfbd i)).const_mul c

/-- Finite vectors of `heatSmooth'` flat pairings are genuinely in `L²`. -/
theorem memLp_two_shfPairing_heatSmooth'_vector
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (l : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF (-l) P Z)
    {a T : ℝ} (ha : 0 ≤ a) (haT : a < T)
    (f : Fin n → TestFn) {δ : ℝ} (hδ : 0 ≤ δ) (c : ℝ) :
    MemLp (fun ω => WithLp.toLp 2 (fun i =>
      c * shfPairing Z a T (heatSmooth' δ (f i)) (fun _ => 1) ω)) 2 P := by
  classical
  choose C hC using fun i =>
    (f i).hasCompactSupport.exists_bound_of_continuous (f i).continuous
  have hreg (i : Fin n) := heatSmooth'_regular (f i) hδ
    (fun x => by simpa only [Real.norm_eq_abs] using hC i x)
  apply memLp_two_shfPairing_one_vector l P Z hZ ha haT
    (fun i => heatSmooth' δ (f i))
      (fun i => (hreg i).1) (fun i => (hreg i).2.1) C
      (fun i => (hreg i).2.2.2) c

/-- The vector difference of mollified and plain masses is almost surely the
pairing against the pointwise mollification error. -/
theorem shfPairing_heatSmooth'_sub_vector_ae
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (l : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF (-l) P Z)
    {a T : ℝ} (ha : 0 ≤ a) (haT : a < T)
    (f : Fin n → TestFn) {δ : ℝ} (hδ : 0 ≤ δ) (c : ℝ) :
    (fun ω => WithLp.toLp 2 (fun i => c *
      (shfPairing Z a T (heatSmooth' δ (f i)) (fun _ => 1) ω -
       shfPairing Z a T (f i) (fun _ => 1) ω))) =ᵐ[P]
    (fun ω => WithLp.toLp 2 (fun i => c *
      shfPairing Z a T
        (fun x => heatSmooth' δ (f i) x - f i x) (fun _ => 1) ω)) := by
  classical
  choose C hC using fun i =>
    (f i).hasCompactSupport.exists_bound_of_continuous (f i).continuous
  have hf1 (i : Fin n) : Integrable (f i : Plane → ℝ) :=
    (f i).continuous.integrable_of_hasCompactSupport (f i).hasCompactSupport
  have hreg (i : Fin n) := heatSmooth'_regular (f i) hδ
    (fun x => by simpa only [Real.norm_eq_abs] using hC i x)
  have hsub (i : Fin n) := shfPairing_sub_one_ae (-l) P Z hZ ha haT
    ((hreg i).1) (f i).continuous.measurable (hreg i).2.1 (hf1 i)
  filter_upwards [ae_all_iff.2 hsub] with ω hω
  congr 1
  funext i
  exact congrArg (fun v : ℝ => c * v) (hω i).symm

/-- The same identity with subtraction performed in Euclidean space, as used
by the converging-together distance. -/
theorem shfPairing_heatSmooth'_vector_sub_ae
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (l : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF (-l) P Z)
    {a T : ℝ} (ha : 0 ≤ a) (haT : a < T)
    (f : Fin n → TestFn) {δ : ℝ} (hδ : 0 ≤ δ) (c : ℝ) :
    (fun ω => WithLp.toLp 2 (fun i => c *
      shfPairing Z a T (heatSmooth' δ (f i)) (fun _ => 1) ω) -
      WithLp.toLp 2 (fun i => c *
        shfPairing Z a T (f i) (fun _ => 1) ω)) =ᵐ[P]
    (fun ω => WithLp.toLp 2 (fun i => c *
      shfPairing Z a T
        (fun x => heatSmooth' δ (f i) x - f i x) (fun _ => 1) ω)) := by
  filter_upwards [shfPairing_heatSmooth'_sub_vector_ae
    l P Z hZ ha haT f hδ c] with ω hω
  rw [← hω]
  change WithLp.toLp 2 (fun i : Fin n =>
    c * shfPairing Z a T (heatSmooth' δ (f i)) (fun _ => 1) ω -
    c * shfPairing Z a T (f i) (fun _ => 1) ω) = _
  congr 1
  funext i
  exact (mul_sub c _ _).symm

/-- The normalization used for the half-covariance test is exactly the target
`sqrt (l/2)` normalization on the original test. -/
theorem sqrt_mul_shfPairing_inv_sqrt_two
    {Ω : Type*} [MeasurableSpace Ω]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    {l T : ℝ} (f : TestFn) (ω : Ω) :
    Real.sqrt l * shfPairing Z 0 T ((Real.sqrt 2)⁻¹ • f) (fun _ => 1) ω =
      Real.sqrt (l / 2) * shfPairing Z 0 T f (fun _ => 1) ω := by
  have hsqrt : Real.sqrt (l / 2) = Real.sqrt l * (Real.sqrt 2)⁻¹ := by
    rw [Real.sqrt_div' l (by norm_num : (0 : ℝ) ≤ 2)]
    exact div_eq_mul_inv _ _
  have hpair :
      shfPairing Z 0 T ((Real.sqrt 2)⁻¹ • f) (fun _ => 1) ω =
        (Real.sqrt 2)⁻¹ * shfPairing Z 0 T f (fun _ => 1) ω := by
    simp only [shfPairing, mul_one]
    change (∫ p : Plane × Plane, (Real.sqrt 2)⁻¹ * f p.1 ∂Z 0 T ω) =
      (Real.sqrt 2)⁻¹ * ∫ p : Plane × Plane, f p.1 ∂Z 0 T ω
    exact integral_const_mul _ _
  rw [hpair, hsqrt]
  ring

/-- Vector form of the fixed-horizon scaling conversion. -/
theorem sqrt_mul_shfPairing_vector_inv_sqrt_two
    {Ω : Type*} [MeasurableSpace Ω]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    {l T : ℝ} {n : ℕ} (f : Fin n → TestFn) (ω : Ω) :
    WithLp.toLp 2 (fun i => Real.sqrt l *
      shfPairing Z 0 T ((Real.sqrt 2)⁻¹ • f i) (fun _ => 1) ω) =
    WithLp.toLp 2 (fun i => Real.sqrt (l / 2) *
      shfPairing Z 0 T (f i) (fun _ => 1) ω) := by
  congr 1
  funext i
  exact sqrt_mul_shfPairing_inv_sqrt_two Z (f i) ω


/-- The moving, mollified linear CLT follows from the fixed-horizon CLT.
The preceding moment estimates control the cutoff and mollifier errors.
Positive horizons supply all-index measurability, including indices outside
the asymptotic regime. -/
theorem tendstoInDistribution_mollified_of_fixedHorizon
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : ∀ l, IsCriticalSHF (-l) P (Z l))
    (hfixed : ∀ {m : ℕ} (g : Fin m → TestFn)
      (_hgzero : ∀ i, (∫ x : Plane, g i x) = 0)
      {T₀ : ℝ} (_hT₀ : 0 < T₀),
      TendstoInDistribution
        (fun l ω => WithLp.toLp 2 (fun i : Fin m => Real.sqrt l *
          shfPairing (Z l) 0 T₀ (g i) (fun _ => 1) ω)) atTop id
        (fun _ => P)
        (ProbabilityTheory.multivariateGaussian 0 (Matrix.of fun i j =>
          4 * Real.pi * ∫ s in Ioc (0 : ℝ) T₀,
            ∫ x : Plane, g i x * heatSmooth (2 * s) (g j) x)))
    (f : Fin n → TestFn) (hfzero : ∀ i, (∫ x : Plane, f i x) = 0)
    (T : ℝ → ℝ) (hTpos : ∀ l, 0 < T l)
    (hT : Tendsto T atTop atTop)
    (hlog : Tendsto (fun l => Real.log (T l) / l) atTop (𝓝 0))
    (δ : ℝ → ℝ) (hδ : ∀ l, 0 ≤ δ l) (hδlim : Tendsto δ atTop (𝓝 0))
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hν : IsFiniteGffLaw f ν) :
    TendstoInDistribution
      (fun l ω => WithLp.toLp 2 (fun i : Fin n => Real.sqrt (l / 2) *
        shfPairing (Z l) 0 (T l) (heatSmooth' (δ l) (f i)) (fun _ => 1) ω))
      atTop id (fun _ => P) ν := by
  classical
  have hνeq := isFiniteGffLaw_unique hν (isFiniteGffLaw_multivariateGaussian f hfzero)
  subst ν
  let g : Fin n → TestFn := fun i => (Real.sqrt 2)⁻¹ • f i
  let S : ℕ → Matrix (Fin n) (Fin n) ℝ := fun k => Matrix.of fun i j =>
    4 * Real.pi * ∫ s in Ioc (0 : ℝ) ((k : ℝ) + 1),
      ∫ x : Plane, g i x * heatSmooth (2 * s) (g j) x
  let Q : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun i j => logCovariance (f i) (f j)
  let X : ℝ → ℕ → Ω → EuclideanSpace ℝ (Fin n) := fun l k ω =>
    WithLp.toLp 2 (fun i => Real.sqrt (l / 2) *
      shfPairing (Z l) 0 ((k : ℝ) + 1) (f i) (fun _ => 1) ω)
  let W₀ : ℝ → Ω → EuclideanSpace ℝ (Fin n) := fun l ω =>
    WithLp.toLp 2 (fun i => Real.sqrt (l / 2) *
      shfPairing (Z l) 0 (T l) (f i) (fun _ => 1) ω)
  let W : ℝ → Ω → EuclideanSpace ℝ (Fin n) := fun l ω =>
    WithLp.toLp 2 (fun i => Real.sqrt (l / 2) *
      shfPairing (Z l) 0 (T l) (heatSmooth' (δ l) (f i)) (fun _ => 1) ω)
  have hgzero (i : Fin n) : (∫ x : Plane, g i x) = 0 := by
    simp only [g, smul_apply, smul_eq_mul, integral_const_mul, hfzero, mul_zero]
  have hXY (k : ℕ) : TendstoInDistribution (fun l => X l k) atTop id
      (fun _ => P) (ProbabilityTheory.multivariateGaussian 0 (S k)) := by
    have h := hfixed g hgzero (by positivity : 0 < (k : ℝ) + 1)
    apply h.congr
    · intro l
      exact Filter.Eventually.of_forall fun ω =>
        sqrt_mul_shfPairing_vector_inv_sqrt_two (Z l) f ω
    · exact Filter.Eventually.of_forall fun _ => rfl
  have hGauss : TendstoInDistribution (fun _ : ℕ => id) atTop id
      (fun k => ProbabilityTheory.multivariateGaussian 0 (S k))
      (ProbabilityTheory.multivariateGaussian 0 Q) :=
    tendstoInDistribution_truncatedHeatGaussian f hfzero
  have hplain (l H : ℝ) (hH : 0 < H) : MemLp
      (fun ω => WithLp.toLp 2 (fun i : Fin n => Real.sqrt (l / 2) *
        shfPairing (Z l) 0 H (f i) (fun _ => 1) ω)) 2 P := by
    simpa only [heatSmooth', ite_true] using
      memLp_two_shfPairing_heatSmooth'_vector l P (Z l) (hZ l)
        (a := 0) (T := H) (by norm_num) hH f (δ := 0) (by rfl)
        (Real.sqrt (l / 2))
  have hWmem (l : ℝ) : MemLp (W l) 2 P :=
    memLp_two_shfPairing_heatSmooth'_vector l P (Z l) (hZ l)
      (a := 0) (T := T l) (by norm_num) (hTpos l) f (hδ l) (Real.sqrt (l / 2))
  have hW₀mem (l : ℝ) : MemLp (W₀ l) 2 P := hplain l (T l) (hTpos l)
  have hXmem (l : ℝ) (k : ℕ) : MemLp (X l k) 2 P :=
    hplain l ((k : ℝ) + 1) (by positivity)
  have htail (k : ℕ) : Tendsto
      (fun l => ∫ ω, ‖W₀ l ω - X l k ω‖ ^ 2 ∂P) atTop
      (𝓝 (2 * Real.pi * ∑ i : Fin n, ∫ s in Ioi ((k : ℝ) + 1),
        ∫ x : Plane, f i x * heatSmooth (2 * s) (f i) x)) := by
    have h := tendsto_integral_norm_sq_tail_vector P Z hZ f hfzero
      (T₀ := (k : ℝ) + 1) (by positivity) T hT hlog
    convert h using 1
    funext l
    apply integral_congr_ae
    filter_upwards [] with ω
    congr 2
    change WithLp.toLp 2 (fun i : Fin n =>
      Real.sqrt (l / 2) * shfPairing (Z l) 0 (T l) (f i) (fun _ => 1) ω -
      Real.sqrt (l / 2) * shfPairing (Z l) 0 ((k : ℝ) + 1) (f i) (fun _ => 1) ω) = _
    congr 1
    funext i
    exact (mul_sub _ _ _).symm
  have herr : Tendsto (fun l => ∫ ω, ‖W l ω - W₀ l ω‖ ^ 2 ∂P)
      atTop (𝓝 0) := by
    apply (tendsto_integral_norm_sq_mollifier_vector
      P Z hZ f hfzero T hT hlog δ hδ hδlim).congr'
    filter_upwards [] with l
    apply integral_congr_ae
    filter_upwards [shfPairing_heatSmooth'_vector_sub_ae l P (Z l) (hZ l)
      (a := 0) (T := T l) (by norm_num) (hTpos l) f (hδ l)
      (Real.sqrt (l / 2))] with ω hω
    exact congrArg (fun v => ‖v‖ ^ 2) hω.symm
  let b : ℕ → ℝ := fun k => 2 * (2 * Real.pi * ∑ i : Fin n,
    ∫ s in Ioi ((k : ℝ) + 1),
      ∫ x : Plane, f i x * heatSmooth (2 * s) (f i) x)
  let a : ℝ → ℕ → ℝ := fun l k =>
    2 * (∫ ω, ‖W₀ l ω - X l k ω‖ ^ 2 ∂P) +
    2 * (∫ ω, ‖W l ω - W₀ l ω‖ ^ 2 ∂P)
  have hb : Tendsto b atTop (𝓝 0) := by
    simpa only [b, mul_zero] using
      (tendsto_heat_energy_tail_vector_zero f hfzero).const_mul 2
  have hcontrol (k : ℕ) : Tendsto (fun l => a l k) atTop (𝓝 (b k)) := by
    simpa only [a, b, mul_zero, add_zero] using
      ((htail k).const_mul 2).add (herr.const_mul 2)
  have hInt (k : ℕ) : ∀ᶠ l : ℝ in atTop,
      Integrable (fun ω => ‖X l k ω - W l ω‖ ^ 2) P :=
    Filter.Eventually.of_forall fun l => ((hXmem l k).sub (hWmem l)).norm.integrable_sq
  have hle (k : ℕ) : ∀ᶠ l : ℝ in atTop,
      (∫ ω, ‖X l k ω - W l ω‖ ^ 2 ∂P) ≤ a l k := by
    filter_upwards [] with l
    have hI₁ := ((hW₀mem l).sub (hXmem l k)).norm.integrable_sq
    have hI₂ := ((hWmem l).sub (hW₀mem l)).norm.integrable_sq
    calc
      _ ≤ ∫ ω, 2 * ‖W₀ l ω - X l k ω‖ ^ 2 +
          2 * ‖W l ω - W₀ l ω‖ ^ 2 ∂P := by
        apply integral_mono (((hXmem l k).sub (hWmem l)).norm.integrable_sq)
          ((hI₁.const_mul 2).add (hI₂.const_mul 2))
        intro ω
        change ‖X l k ω - W l ω‖ ^ 2 ≤
          2 * ‖W₀ l ω - X l k ω‖ ^ 2 + 2 * ‖W l ω - W₀ l ω‖ ^ 2
        rw [norm_sub_rev (X l k ω) (W l ω)]
        have hn : ‖W l ω - X l k ω‖ ≤
            ‖W l ω - W₀ l ω‖ + ‖W₀ l ω - X l k ω‖ := by
          simpa only [sub_add_sub_cancel] using
            norm_add_le (W l ω - W₀ l ω) (W₀ l ω - X l k ω)
        have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 hn
        nlinarith only [hs, sq_nonneg (‖W l ω - W₀ l ω‖ - ‖W₀ l ω - X l k ω‖)]
      _ = a l k := by
        change (∫ ω, 2 * ‖(W₀ l - X l k) ω‖ ^ 2 +
          2 * ‖(W l - W₀ l) ω‖ ^ 2 ∂P) = a l k
        rw [integral_add (hI₁.const_mul 2) (hI₂.const_mul 2),
          integral_const_mul, integral_const_mul]
        rfl
  exact tendstoInDistribution_of_converging_together_tail_varying
    (fun l k => (hXmem l k).aemeasurable) (fun _ => aemeasurable_id)
    aemeasurable_id (fun l => (hWmem l).aemeasurable) hXY hGauss
    (probability_tail_eventually_of_sq_moment_le_tendsto X W a b hInt hle hcontrol hb)

end Critical2DKPZ.Extensions.GffTangent

end
