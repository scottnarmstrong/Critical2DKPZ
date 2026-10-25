/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # The angular Bessel kernel

The order-zero Bessel kernel is represented by its angular integral. This is the form that appears
when a radial Fourier transform is averaged over directions in the plane.
-/

@[expose] public section

open Complex Real

namespace Critical2DKPZ.Spectral

/-- The order-zero Bessel kernel, in its angular-integral representation. -/
noncomputable def besselJ0Angular (t : ℝ) : ℝ :=
  Real.circleAverage (fun z : ℂ => Real.cos (t * z.re)) 0 1

private theorem circleIntegrable_cos_re (t : ℝ) :
    CircleIntegrable (fun z : ℂ => Real.cos (t * z.re)) 0 1 := by
  apply ContinuousOn.circleIntegrable (by norm_num)
  exact (by fun_prop : Continuous (fun z : ℂ => Real.cos (t * z.re))).continuousOn.mono
    (Set.subset_univ _)


/-- The angular Bessel kernel is bounded in absolute value by one. -/
theorem abs_besselJ0Angular_le_one (t : ℝ) : |besselJ0Angular t| ≤ 1 := by
  have hf := circleIntegrable_cos_re t
  have habs : |besselJ0Angular t| ≤
      Real.circleAverage (fun z : ℂ => |Real.cos (t * z.re)|) 0 1 := by
    exact Real.abs_circleAverage_le_circleAverage_abs
  have hbound : ∀ z ∈ Metric.sphere (0 : ℂ) |(1 : ℝ)|,
      |Real.cos (t * z.re)| ≤ 1 := by
    intro z hz
    exact abs_cos_le_one _
  have havg : Real.circleAverage (fun z : ℂ => |Real.cos (t * z.re)|) 0 1 ≤ 1 :=
    Real.circleAverage_mono_on_of_le_circle hf.abs hbound
  exact habs.trans havg

/-- The angular Bessel kernel is Lipschitz, hence continuous, in its radial parameter. -/
theorem abs_besselJ0Angular_sub_le (s t : ℝ) :
    |besselJ0Angular t - besselJ0Angular s| ≤ |t - s| := by
  let f : ℂ → ℝ := fun z => Real.cos (t * z.re)
  let g : ℂ → ℝ := fun z => Real.cos (s * z.re)
  have hf : CircleIntegrable f 0 1 := circleIntegrable_cos_re t
  have hg : CircleIntegrable g 0 1 := circleIntegrable_cos_re s
  have hdiff : besselJ0Angular t - besselJ0Angular s =
      Real.circleAverage (fun z : ℂ => f z - g z) 0 1 := by
    dsimp [f, g, besselJ0Angular]
    exact (Real.circleAverage_fun_sub hf hg).symm
  have hbound : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      |f z - g z| ≤ |t - s| := by
    intro z hz
    have hzNorm : ‖z‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hzRe : |z.re| ≤ 1 := by
      simpa [hzNorm] using abs_re_le_norm z
    calc
      |Real.cos (t * z.re) - Real.cos (s * z.re)| ≤ |t * z.re - s * z.re| :=
        Real.abs_cos_sub_cos_le _ _
      _ = |t - s| * |z.re| := by rw [show t * z.re - s * z.re = (t - s) * z.re by ring, abs_mul]
      _ ≤ |t - s| := by nlinarith [abs_nonneg (t - s)]
  have hdiffInt : CircleIntegrable (fun z : ℂ => f z - g z) 0 1 := hf.sub hg
  have habs : |Real.circleAverage (fun z : ℂ => f z - g z) 0 1| ≤
      Real.circleAverage (fun z : ℂ => |f z - g z|) 0 1 :=
    Real.abs_circleAverage_le_circleAverage_abs
  have havg : Real.circleAverage (fun z : ℂ => |f z - g z|) 0 1 ≤ |t - s| :=
    Real.circleAverage_mono_on_of_le_circle hdiffInt.abs (by simpa using hbound)
  rw [hdiff]
  exact habs.trans havg

/-- Continuity of the angular Bessel kernel follows from its uniform Lipschitz bound. -/
theorem continuous_besselJ0Angular : Continuous besselJ0Angular := by
  rw [Metric.continuous_iff]
  intro t ε hε
  refine ⟨ε, hε, ?_⟩
  intro s hs
  have h := abs_besselJ0Angular_sub_le s t
  rw [abs_sub_comm] at h
  have hs' : |t - s| < ε := by simpa [Real.dist_eq, abs_sub_comm] using hs
  exact lt_of_le_of_lt h hs'

/-- The angular Bessel kernel differs from one by at most a quadratic error near the origin. -/
theorem abs_besselJ0Angular_sub_one_le (t : ℝ) :
    |besselJ0Angular t - 1| ≤ t ^ 2 / 2 := by
  let f : ℂ → ℝ := fun z => Real.cos (t * z.re)
  have hf : CircleIntegrable f 0 1 := circleIntegrable_cos_re t
  have hconst : CircleIntegrable (fun _ : ℂ => (1 : ℝ)) 0 1 := circleIntegrable_const 1 0 1
  have hdiff : besselJ0Angular t - 1 =
      Real.circleAverage (fun z : ℂ => f z - 1) 0 1 := by
    calc
      besselJ0Angular t - 1 = Real.circleAverage f 0 1 - 1 := rfl
      _ = Real.circleAverage f 0 1 - Real.circleAverage (fun _ : ℂ => (1 : ℝ)) 0 1 := by
        rw [Real.circleAverage_const]
      _ = _ := (Real.circleAverage_fun_sub hf hconst).symm
  have hbound : ∀ z ∈ Metric.sphere (0 : ℂ) 1, |f z - 1| ≤ t ^ 2 / 2 := by
    intro z hz
    have hzNorm : ‖z‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hzRe : |z.re| ≤ 1 := by
      simpa [hzNorm] using abs_re_le_norm z
    have hzReSq : (z.re) ^ 2 ≤ 1 := by
      have h := (sq_le_sq₀ (abs_nonneg z.re) (by norm_num : (0 : ℝ) ≤ 1)).2 hzRe
      simpa using h
    have hySq : (t * z.re) ^ 2 ≤ t ^ 2 := by
      calc
        (t * z.re) ^ 2 = t ^ 2 * (z.re) ^ 2 := by ring
        _ ≤ t ^ 2 * 1 := mul_le_mul_of_nonneg_left hzReSq (sq_nonneg t)
        _ = t ^ 2 := by ring
    have hcos : 1 - (t * z.re) ^ 2 / 2 ≤ Real.cos (t * z.re) :=
      one_sub_sq_div_two_le_cos
    have hcosOne : Real.cos (t * z.re) ≤ 1 := cos_le_one _
    rw [show f z - 1 = Real.cos (t * z.re) - 1 by rfl,
      abs_of_nonpos (by linarith : Real.cos (t * z.re) - 1 ≤ 0)]
    nlinarith
  have hdiffInt : CircleIntegrable (fun z : ℂ => f z - 1) 0 1 := hf.sub hconst
  have habs : |Real.circleAverage (fun z : ℂ => f z - 1) 0 1| ≤
      Real.circleAverage (fun z : ℂ => |f z - 1|) 0 1 :=
    Real.abs_circleAverage_le_circleAverage_abs
  have hbound' : ∀ z ∈ Metric.sphere (0 : ℂ) |(1 : ℝ)|, |f z - 1| ≤ t ^ 2 / 2 := by
    simpa using hbound
  have havg : Real.circleAverage (fun z : ℂ => |f z - 1|) 0 1 ≤ t ^ 2 / 2 :=
    Real.circleAverage_mono_on_of_le_circle hdiffInt.abs hbound'
  calc
    |besselJ0Angular t - 1| = |Real.circleAverage (fun z : ℂ => f z - 1) 0 1| :=
      congrArg abs hdiff
    _ ≤ Real.circleAverage (fun z : ℂ => |f z - 1|) 0 1 := habs
    _ ≤ t ^ 2 / 2 := havg


private theorem besselJ0Angular_eq_quarter_integral (t : ℝ) :
    besselJ0Angular t = (2 / Real.pi) *
      ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos (t * Real.cos θ) := by
  let f : ℝ → ℝ := fun θ => Real.cos (t * Real.cos θ)
  have hfper : Function.Periodic f Real.pi := by
    intro θ
    simp [f, Real.cos_add_pi, Real.cos_neg]
  have hfcont : Continuous f := by
    change Continuous (fun θ : ℝ => Real.cos (t * Real.cos θ))
    fun_prop
  have hint : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b := by
    intro a b
    exact hfcont.intervalIntegrable (μ := MeasureTheory.volume) a b
  have hperiod := hfper.intervalIntegral_add_zsmul_eq (2 : ℤ) 0 hint
  have hwhole : (∫ θ in (0 : ℝ)..2 * Real.pi, f θ) =
      2 * ∫ θ in (0 : ℝ)..Real.pi, f θ := by
    convert hperiod using 1 <;> norm_num [smul_eq_mul]
  have hreflect : (∫ θ in (0 : ℝ)..Real.pi, f θ) =
      2 * ∫ θ in (0 : ℝ)..(Real.pi / 2), f θ := by
    have hsubst' : (∫ θ in (0 : ℝ)..(Real.pi / 2), f (Real.pi - θ)) =
        - ∫ θ in Real.pi..(Real.pi / 2), f θ := by
      have h := intervalIntegral.integral_comp_mul_add f (by norm_num : (-1 : ℝ) ≠ 0) Real.pi
        (a := 0) (b := Real.pi / 2)
      rw [show (-1 : ℝ) * (Real.pi / 2) + Real.pi = Real.pi / 2 by ring] at h
      have h' : (∫ θ in (0 : ℝ)..(Real.pi / 2), f (-1 * θ + Real.pi)) =
          - ∫ θ in Real.pi..(Real.pi / 2), f θ := by
        simpa [smul_eq_mul] using h
      simpa [sub_eq_add_neg, neg_one_mul, add_comm] using h'
    have hsubst : (∫ θ in (0 : ℝ)..(Real.pi / 2), f (Real.pi - θ)) =
        ∫ θ in (Real.pi / 2)..Real.pi, f θ := by
      rw [hsubst', intervalIntegral.integral_symm]
      ring
    have hcongr : (∫ θ in (0 : ℝ)..(Real.pi / 2), f (Real.pi - θ)) =
        ∫ θ in (0 : ℝ)..(Real.pi / 2), f θ := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      simp [f, Real.cos_pi_sub, Real.cos_neg]
    calc
      (∫ θ in (0 : ℝ)..Real.pi, f θ) =
          (∫ θ in (0 : ℝ)..(Real.pi / 2), f θ) +
            ∫ θ in (Real.pi / 2)..Real.pi, f θ :=
        (intervalIntegral.integral_add_adjacent_intervals (hint 0 (Real.pi / 2))
          (hint (Real.pi / 2) Real.pi)).symm
      _ = (∫ θ in (0 : ℝ)..(Real.pi / 2), f θ) +
            ∫ θ in (0 : ℝ)..(Real.pi / 2), f θ := by rw [← hsubst, ← hcongr]
      _ = _ := by ring
  rw [besselJ0Angular, Real.circleAverage_def]
  simp only [circleMap_zero_re, one_mul, smul_eq_mul]
  rw [hwhole, hreflect]
  ring

private theorem hasDerivAt_inv_sin {x : ℝ} (hx : Real.sin x ≠ 0) :
    HasDerivAt (fun y : ℝ => (Real.sin y)⁻¹)
      (-(Real.cos x) / (Real.sin x) ^ 2) x := by
  have h := (hasDerivAt_inv hx).comp x (Real.hasDerivAt_sin x)
  exact h.congr_deriv (by rw [div_eq_mul_inv]; ring)

private theorem hasDerivAt_sin_cos (t x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin (t * Real.cos y))
      (-t * Real.sin x * Real.cos (t * Real.cos x)) x := by
  have h := (Real.hasDerivAt_sin (t * Real.cos x)).comp x
    ((Real.hasDerivAt_cos x).const_mul t)
  exact h.congr_deriv (by ring)

private theorem invSin_deriv_abs_integral {δ : ℝ} (hδ : 0 < δ)
    (hδ' : δ ≤ Real.pi / 2) :
    ∫ x in δ..(Real.pi / 2), |-Real.cos x / (Real.sin x) ^ 2| =
      (Real.sin δ)⁻¹ - 1 := by
  let u : ℝ → ℝ := fun x => (Real.sin x)⁻¹
  let up : ℝ → ℝ := fun x => -Real.cos x / (Real.sin x) ^ 2
  have hsin (x : ℝ) (hx : x ∈ Set.Icc δ (Real.pi / 2)) : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le hδ hx.1) (by
      have : Real.pi / 2 < Real.pi := by linarith [Real.pi_pos]
      exact lt_of_le_of_lt hx.2 this)
  have huD : ∀ x ∈ Set.Icc δ (Real.pi / 2), HasDerivAt u (up x) x := by
    intro x hx
    simpa [u, up] using hasDerivAt_inv_sin (ne_of_gt (hsin x hx))
  have hupcont : ContinuousOn up (Set.Icc δ (Real.pi / 2)) := by
    dsimp [up]
    refine ContinuousOn.div ?_ ?_ ?_
    · exact Real.continuous_cos.neg.continuousOn
    · exact (Real.continuous_sin.pow 2).continuousOn
    · intro x hx
      exact pow_ne_zero 2 (ne_of_gt (hsin x hx))
  have hderiv : ∀ x ∈ Set.Icc δ (Real.pi / 2), deriv u x = up x := by
    intro x hx
    exact (huD x hx).deriv
  have hderivCont : ContinuousOn (deriv u) (Set.Icc δ (Real.pi / 2)) :=
    hupcont.congr fun x hx => hderiv x hx
  have hderivInt : IntervalIntegrable (deriv u) MeasureTheory.volume δ (Real.pi / 2) :=
    hderivCont.intervalIntegrable_of_Icc hδ'
  have hftc := intervalIntegral.integral_deriv_eq_sub
    (a := δ) (b := Real.pi / 2) (f := u)
    (fun x hx => by
      rw [Set.uIcc_of_le hδ'] at hx
      exact (huD x hx).differentiableAt) hderivInt
  have hupInt : ∫ x in δ..(Real.pi / 2), up x = u (Real.pi / 2) - u δ := by
    calc
      _ = ∫ x in δ..(Real.pi / 2), deriv u x := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hδ'] at hx
        exact (hderiv x hx).symm
      _ = _ := hftc
  have hupNonpos : ∀ x ∈ Set.Icc δ (Real.pi / 2), up x ≤ 0 := by
    intro x hx
    dsimp [up]
    apply div_nonpos_of_nonpos_of_nonneg
    · have hx0 : 0 ≤ x := le_trans hδ.le hx.1
      have hlow : -(Real.pi / 2) ≤ x := by linarith [Real.pi_pos, hx0]
      exact neg_nonpos.mpr (Real.cos_nonneg_of_mem_Icc ⟨hlow, hx.2⟩)
    · positivity
  have habs : (∫ x in δ..(Real.pi / 2), |up x|) =
      - ∫ x in δ..(Real.pi / 2), up x := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hδ'] at hx
    change |up x| = -up x
    exact abs_of_nonpos (hupNonpos x hx)
  have hupAbs : ∫ x in δ..(Real.pi / 2), |up x| =
      (Real.sin δ)⁻¹ - 1 := by
    rw [habs, hupInt]
    simp [u, Real.sin_pi_div_two]
  simpa [up] using hupAbs


/-- The cosine oscillatory integral over [δ, π/2] is bounded in absolute value by 2/(t sin δ) for positive t and δ. -/
private theorem bessel_quarter_tail_bound {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ)
    (hδ' : δ ≤ Real.pi / 2) :
    |∫ x in δ..(Real.pi / 2), Real.cos (t * Real.cos x)| ≤
      2 / (t * Real.sin δ) := by
  let u : ℝ → ℝ := fun x => (Real.sin x)⁻¹
  let up : ℝ → ℝ := fun x => -Real.cos x / (Real.sin x) ^ 2
  let v : ℝ → ℝ := fun x => Real.sin (t * Real.cos x)
  let vp : ℝ → ℝ := fun x => -t * Real.sin x * Real.cos (t * Real.cos x)
  have hsin (x : ℝ) (hx : x ∈ Set.Icc δ (Real.pi / 2)) : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi (lt_of_lt_of_le hδ hx.1) (by
      have : Real.pi / 2 < Real.pi := by linarith [Real.pi_pos]
      exact lt_of_le_of_lt hx.2 this)
  have huD : ∀ x ∈ Set.Icc δ (Real.pi / 2), HasDerivAt u (up x) x := by
    intro x hx
    simpa [u, up] using hasDerivAt_inv_sin (ne_of_gt (hsin x hx))
  have hvD : ∀ x ∈ Set.Icc δ (Real.pi / 2), HasDerivAt v (vp x) x := by
    intro x hx
    simpa [v, vp] using hasDerivAt_sin_cos t x
  have hucont : ContinuousOn u (Set.Icc δ (Real.pi / 2)) := by
    intro x hx
    exact (huD x hx).continuousAt.continuousWithinAt
  have hvcont : ContinuousOn v (Set.Icc δ (Real.pi / 2)) := by
    intro x hx
    exact (hvD x hx).continuousAt.continuousWithinAt
  have hupcont : ContinuousOn up (Set.Icc δ (Real.pi / 2)) := by
    dsimp [up]
    refine ContinuousOn.div ?_ ?_ ?_
    · exact Real.continuous_cos.neg.continuousOn
    · exact (Real.continuous_sin.pow 2).continuousOn
    · intro x hx
      exact pow_ne_zero 2 (ne_of_gt (hsin x hx))
  have hvpcont : ContinuousOn vp (Set.Icc δ (Real.pi / 2)) := by
    dsimp [vp]
    fun_prop
  have huInt : IntervalIntegrable up MeasureTheory.volume δ (Real.pi / 2) :=
    hupcont.intervalIntegrable_of_Icc hδ'
  have hvpInt : IntervalIntegrable vp MeasureTheory.volume δ (Real.pi / 2) :=
    hvpcont.intervalIntegrable_of_Icc hδ'
  have hvInt : IntervalIntegrable v MeasureTheory.volume δ (Real.pi / 2) :=
    hvcont.intervalIntegrable_of_Icc hδ'
  have hupvcont : ContinuousOn (fun x : ℝ => up x * v x) (Set.Icc δ (Real.pi / 2)) :=
    hupcont.mul hvcont
  have hupvInt : IntervalIntegrable (fun x : ℝ => up x * v x)
      MeasureTheory.volume δ (Real.pi / 2) := hupvcont.intervalIntegrable_of_Icc hδ'
  have huDoo : ∀ x ∈ Set.Ioo δ (Real.pi / 2), HasDerivAt u (up x) x := by
    intro x hx
    exact huD x (Set.Ioo_subset_Icc_self hx)
  have hvDoo : ∀ x ∈ Set.Ioo δ (Real.pi / 2), HasDerivAt v (vp x) x := by
    intro x hx
    exact hvD x (Set.Ioo_subset_Icc_self hx)
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := δ) (b := Real.pi / 2) (u := u) (v := v) (u' := up) (v' := vp)
    (by simpa only [Set.uIcc_of_le hδ'] using hucont)
    (by simpa only [Set.uIcc_of_le hδ'] using hvcont)
    (by simpa only [min_eq_left hδ', max_eq_right hδ'] using huDoo)
    (by simpa only [min_eq_left hδ', max_eq_right hδ'] using hvDoo)
    huInt hvpInt
  have hprod (x : ℝ) (hx : x ∈ Set.Icc δ (Real.pi / 2)) :
      u x * vp x = -t * Real.cos (t * Real.cos x) := by
    dsimp [u, vp]
    field_simp [ne_of_gt (hsin x hx)]
  have hprodInt : (∫ x in δ..(Real.pi / 2), u x * vp x) =
      -t * ∫ x in δ..(Real.pi / 2), Real.cos (t * Real.cos x) := by
    calc
      _ = ∫ x in δ..(Real.pi / 2), -t * Real.cos (t * Real.cos x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hδ'] at hx
        exact hprod x hx
      _ = _ := intervalIntegral.integral_const_mul (-t)
        (fun x : ℝ => Real.cos (t * Real.cos x))
  have hparts' : -t * ∫ x in δ..(Real.pi / 2), Real.cos (t * Real.cos x) =
      -(Real.sin δ)⁻¹ * Real.sin (t * Real.cos δ) -
        ∫ x in δ..(Real.pi / 2), up x * v x := by
    rw [hprodInt] at hparts
    simpa [u, v, Real.sin_pi_div_two, Real.cos_pi_div_two] using hparts
  have hmulBound : ∀ x ∈ Set.Icc δ (Real.pi / 2),
      |up x * v x| ≤ |up x| := by
    intro x hx
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _)
  have hB : |∫ x in δ..(Real.pi / 2), up x * v x| ≤
      ∫ x in δ..(Real.pi / 2), |up x| := by
    calc
      _ ≤ ∫ x in δ..(Real.pi / 2), |up x * v x| :=
        intervalIntegral.abs_integral_le_integral_abs hδ'
      _ ≤ ∫ x in δ..(Real.pi / 2), |up x| :=
        intervalIntegral.integral_mono_on hδ' hupvInt.abs huInt.abs
          hmulBound
  have hvar := invSin_deriv_abs_integral hδ hδ'
  have hvar' : ∫ x in δ..(Real.pi / 2), |up x| = (Real.sin δ)⁻¹ - 1 := by
    simpa [up] using hvar
  have hvarBound : ∫ x in δ..(Real.pi / 2), |up x| ≤ (Real.sin δ)⁻¹ := by
    rw [hvar']
    linarith
  have hsinδ : 0 < Real.sin δ := hsin δ ⟨le_rfl, hδ'⟩
  have hcsc : 0 < (Real.sin δ)⁻¹ := inv_pos.mpr hsinδ
  have hvδ : |Real.sin (t * Real.cos δ)| ≤ 1 := abs_sin_le_one _
  have hboundary : |-(Real.sin δ)⁻¹ * Real.sin (t * Real.cos δ)| ≤
      (Real.sin δ)⁻¹ := by
    rw [abs_mul, abs_neg, abs_of_pos hcsc]
    exact mul_le_of_le_one_right hcsc.le hvδ
  have hbound : |-(Real.sin δ)⁻¹ * Real.sin (t * Real.cos δ) -
      ∫ x in δ..(Real.pi / 2), up x * v x| ≤ 2 * (Real.sin δ)⁻¹ := by
    calc
      _ ≤ |-(Real.sin δ)⁻¹ * Real.sin (t * Real.cos δ)| +
          |∫ x in δ..(Real.pi / 2), up x * v x| := by
        rw [sub_eq_add_neg]
        have h := abs_add_le (-(Real.sin δ)⁻¹ * Real.sin (t * Real.cos δ))
          (-(∫ x in δ..(Real.pi / 2), up x * v x))
        simpa only [abs_neg] using h
      _ ≤ (Real.sin δ)⁻¹ + ∫ x in δ..(Real.pi / 2), |up x| := by
        exact add_le_add hboundary hB
      _ ≤ 2 * (Real.sin δ)⁻¹ := by
        calc
          _ ≤ (Real.sin δ)⁻¹ + (Real.sin δ)⁻¹ :=
            add_le_add_right hvarBound ((Real.sin δ)⁻¹)
          _ = 2 * (Real.sin δ)⁻¹ := by ring
  have hscale : |(-t) * ∫ x in δ..(Real.pi / 2), Real.cos (t * Real.cos x)| ≤
      2 * (Real.sin δ)⁻¹ := by rw [hparts']; exact hbound
  have habs : |(-t) * ∫ x in δ..(Real.pi / 2), Real.cos (t * Real.cos x)| =
      t * |∫ x in δ..(Real.pi / 2), Real.cos (t * Real.cos x)| := by
    rw [abs_mul, abs_neg, abs_of_pos ht]
  rw [habs] at hscale
  have hdiv := (div_le_div_of_nonneg_right hscale ht.le)
  calc
    |∫ x in δ..(Real.pi / 2), Real.cos (t * Real.cos x)| =
        (t * |∫ x in δ..(Real.pi / 2), Real.cos (t * Real.cos x)|) / t := by
          field_simp [ne_of_gt ht]
    _ ≤ (2 * (Real.sin δ)⁻¹) / t := hdiv
    _ = 2 / (t * Real.sin δ) := by
      field_simp [ne_of_gt ht, ne_of_gt hsinδ]

/-- The angular Bessel kernel has the stationary-phase decay needed for radial inversion. -/
theorem abs_besselJ0Angular_le_three_div_sqrt {t : ℝ} (ht : 1 ≤ t) :
    |besselJ0Angular t| ≤ 3 / Real.sqrt t := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 htpos
  have hsqrt1 : 1 ≤ Real.sqrt t := by
    simpa using Real.sqrt_le_sqrt ht
  let δ : ℝ := Real.pi / (2 * Real.sqrt t)
  have hδ : 0 < δ := by positivity
  have hδle : δ ≤ Real.pi / 2 := by
    dsimp [δ]
    have hinv : (Real.sqrt t)⁻¹ ≤ 1 := (inv_le_one₀ hsqrt).2 hsqrt1
    calc
      Real.pi / (2 * Real.sqrt t) = (Real.pi / 2) * (Real.sqrt t)⁻¹ := by ring
      _ ≤ Real.pi / 2 := mul_le_of_le_one_right (by positivity) hinv
  have hsinδ : 0 < Real.sin δ :=
    Real.sin_pos_of_pos_of_lt_pi hδ (lt_of_le_of_lt hδle (by linarith [Real.pi_pos]))
  have hsinLower : (Real.sqrt t)⁻¹ ≤ Real.sin δ := by
    calc
      (Real.sqrt t)⁻¹ = (2 / Real.pi) * δ := by
        dsimp [δ]
        field_simp [ne_of_gt Real.pi_pos, ne_of_gt hsqrt]
      _ ≤ Real.sin δ := Real.mul_le_sin hδ.le hδle
  have hden : Real.sqrt t ≤ t * Real.sin δ := by
    calc
      Real.sqrt t = t * (Real.sqrt t)⁻¹ := by
        field_simp [ne_of_gt hsqrt]
        nlinarith [Real.sq_sqrt htpos.le]
      _ ≤ t * Real.sin δ := mul_le_mul_of_nonneg_left hsinLower htpos.le
  have htail : 2 / (t * Real.sin δ) ≤ 2 / Real.sqrt t := by
    rw [div_le_div_iff₀ (mul_pos htpos hsinδ) hsqrt]
    nlinarith
  let f : ℝ → ℝ := fun x => Real.cos (t * Real.cos x)
  have hfcont : Continuous f := by
    change Continuous (fun x : ℝ => Real.cos (t * Real.cos x))
    fun_prop
  have hfint : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b := by
    intro a b
    exact hfcont.intervalIntegrable (μ := MeasureTheory.volume) a b
  have hsmall : |∫ x in (0 : ℝ)..δ, f x| ≤ δ := by
    calc
      _ ≤ ∫ x in (0 : ℝ)..δ, |f x| :=
        intervalIntegral.abs_integral_le_integral_abs hδ.le
      _ ≤ ∫ x in (0 : ℝ)..δ, (1 : ℝ) :=
        intervalIntegral.integral_mono_on hδ.le (hfint 0 δ).abs
          (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) 0 δ) (by
            intro x hx
            exact abs_cos_le_one _)
      _ = δ := by simp [intervalIntegral.integral_const]
  have htailI := bessel_quarter_tail_bound htpos hδ hδle
  have htailI' : |∫ x in δ..(Real.pi / 2), f x| ≤ 2 / Real.sqrt t := by
    simpa [f] using htailI.trans htail
  have hquarter : |∫ x in (0 : ℝ)..(Real.pi / 2), f x| ≤ δ + 2 / Real.sqrt t := by
    have hsplit : (∫ x in (0 : ℝ)..(Real.pi / 2), f x) =
        (∫ x in (0 : ℝ)..δ, f x) + ∫ x in δ..(Real.pi / 2), f x :=
      (intervalIntegral.integral_add_adjacent_intervals (hfint 0 δ)
        (hfint δ (Real.pi / 2))).symm
    calc
      _ ≤ |∫ x in (0 : ℝ)..δ, f x| +
          |∫ x in δ..(Real.pi / 2), f x| := by
        rw [hsplit]
        exact abs_add_le _ _
      _ ≤ δ + 2 / Real.sqrt t := add_le_add hsmall htailI'
  have hcoeff : (2 / Real.pi) * (Real.pi / 2 + 2) ≤ 3 := by
    have hpi := Real.two_le_pi
    field_simp [ne_of_gt Real.pi_pos]
    nlinarith
  rw [besselJ0Angular_eq_quarter_integral]
  calc
    |(2 / Real.pi) * ∫ x in (0 : ℝ)..(Real.pi / 2), f x| =
        (2 / Real.pi) * |∫ x in (0 : ℝ)..(Real.pi / 2), f x| := by
          rw [abs_mul, abs_of_pos (by positivity)]
    _ ≤ (2 / Real.pi) * (δ + 2 / Real.sqrt t) :=
      mul_le_mul_of_nonneg_left hquarter (by positivity)
    _ = ((2 / Real.pi) * (Real.pi / 2 + 2)) / Real.sqrt t := by
      dsimp [δ]
      field_simp [ne_of_gt Real.pi_pos, ne_of_gt hsqrt]
    _ ≤ 3 / Real.sqrt t := by
      exact div_le_div_of_nonneg_right hcoeff hsqrt.le


/-- The angular average of a sine of any real linear functional vanishes by antipodal
symmetry. -/
theorem circleAverage_sin_linear_eq_zero (a b r : ℝ) :
    Real.circleAverage (fun z : ℂ => Real.sin (a * z.re + b * z.im)) 0 r = 0 := by
  let f : ℂ → ℝ := fun z => Real.sin (a * z.re + b * z.im)
  have hmap (θ : ℝ) : circleMap 0 (-r) θ = -circleMap 0 r θ := by
    simp [circleMap]
  have hneg : Real.circleAverage f 0 (-r) = -Real.circleAverage f 0 r := by
    rw [Real.circleAverage_def, Real.circleAverage_def]
    rw [← smul_neg, ← intervalIntegral.integral_neg]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ hθ
    simp only [f, hmap θ, Complex.neg_re, Complex.neg_im]
    rw [show a * -(circleMap 0 r θ).re + b * -(circleMap 0 r θ).im =
        -(a * (circleMap 0 r θ).re + b * (circleMap 0 r θ).im) by ring]
    rw [Real.sin_neg]
  have hradius : Real.circleAverage f 0 (-r) = Real.circleAverage f 0 r := by
    simp
  rw [← hradius] at hneg
  linarith

/-- The circle average of the cosine of a linear functional is the order-zero Bessel kernel evaluated at the coefficient norm times the radius. -/
theorem circleAverage_cos_linear_eq_besselJ0Angular (a b r : ℝ) :
    Real.circleAverage (fun z : ℂ => Real.cos (a * z.re + b * z.im)) 0 r =
      besselJ0Angular (‖(a : ℂ) + (b : ℂ) * Complex.I‖ * r) := by
  let w : ℂ := (a : ℂ) + (b : ℂ) * Complex.I
  have hA : a = ‖w‖ * Real.cos (Complex.arg w) := by
    rw [Complex.norm_mul_cos_arg w]
    simp [w]
  have hB : b = ‖w‖ * Real.sin (Complex.arg w) := by
    rw [Complex.norm_mul_sin_arg w]
    simp [w]
  have hshift : besselJ0Angular (‖w‖ * r) =
      (2 * Real.pi)⁻¹ • ∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.cos ((‖w‖ * r) * (circleMap 0 1 (θ - Complex.arg w)).re) := by
    rw [besselJ0Angular, Real.circleAverage_eq_integral_add (η := -Complex.arg w)]
    simp [sub_eq_add_neg]
  calc
    Real.circleAverage (fun z : ℂ => Real.cos (a * z.re + b * z.im)) 0 r =
        (2 * Real.pi)⁻¹ • ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.cos (a * (circleMap 0 r θ).re + b * (circleMap 0 r θ).im) :=
      Real.circleAverage_def
    _ = (2 * Real.pi)⁻¹ • ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.cos ((‖w‖ * r) * (circleMap 0 1 (θ - Complex.arg w)).re) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro θ hθ
      simp only [circleMap_zero_re, circleMap_zero_im]
      rw [hA, hB, Real.cos_sub]
      ring_nf
    _ = besselJ0Angular (‖w‖ * r) := hshift.symm

end Critical2DKPZ.Spectral

end
