/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.WeightedFormBound
public import Critical2DKPZ.Analysis.Heat.Basic
public import Critical2DKPZ.Analysis.Heat.Semigroup
public import Critical2DKPZ.SHF.DeltaBose.Measurability
public import Critical2DKPZ.SHF.DeltaBose.HeatPotential
public import Critical2DKPZ.SHF.DeltaBose.ConfigurationWeight
import Critical2DKPZ.SHF.DeltaBose.WeightedBlockL2
import Critical2DKPZ.SHF.DeltaBose.SupBlockBounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Beta
import Mathlib.Tactic

/-! # Elementary heat and Beta estimates for Tsai's kernel bounds -/

@[expose] public section

open MeasureTheory Set Critical2DKPZ.DeltaBose ProbabilityTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Beta integral for two endpoint powers on a finite positive interval. -/
theorem integral_rpow_mul_rpow_sub_eq (t : ℝ) (ht : 0 < t) {b b' : ℝ}
    (hb : -1 < b) (hb' : -1 < b') :
    ∫ s in Set.Ioo 0 t, s ^ b * (t - s) ^ b' =
      t ^ (b + b' + 1) * (Real.Gamma (b + 1) * Real.Gamma (b' + 1) /
        Real.Gamma (b + b' + 2)) := by
  have hα : 0 < b + 1 := by linarith
  have hβ : 0 < b' + 1 := by linarith
  have hComplexIntegrable : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (((b + 1 : ℝ) : ℂ) - 1) *
        (1 - (x : ℂ)) ^ (((b' + 1 : ℝ) : ℂ) - 1)) (Ioc 0 1) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    exact Complex.betaIntegral_convergent (u := ((b + 1 : ℝ) : ℂ)) (v := ((b' + 1 : ℝ) : ℂ))
      (by exact_mod_cast hα) (by exact_mod_cast hβ)
  have hbetaIoo : ProbabilityTheory.beta (b + 1) (b' + 1) =
      ∫ u in Ioo (0 : ℝ) 1, u ^ b * (1 - u) ^ b' := by
    rw [ProbabilityTheory.beta_eq_betaIntegralReal (b + 1) (b' + 1) hα hβ,
      Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← integral_Ioc_eq_integral_Ioo, ← RCLike.re_to_complex, ← integral_re]
    refine setIntegral_congr_fun measurableSet_Ioc ?_
    intro u hu
    norm_cast
    simp only [add_sub_cancel_right]
    rw [← Complex.ofReal_cpow hu.1.le b,
      ← Complex.ofReal_cpow (sub_nonneg.mpr hu.2) b', RCLike.re_to_complex,
      Complex.re_mul_ofReal, Complex.ofReal_re]
    exact hComplexIntegrable
  have hbetaGamma : ProbabilityTheory.beta (b + 1) (b' + 1) =
      Real.Gamma (b + 1) * Real.Gamma (b' + 1) / Real.Gamma (b + b' + 2) := by
    change Real.Gamma (b + 1) * Real.Gamma (b' + 1) /
      Real.Gamma ((b + 1) + (b' + 1)) = _
    rw [show (b + 1) + (b' + 1) = b + b' + 2 by ring]
  have hbetaInterval :
      (∫ u in (0 : ℝ)..1, u ^ b * (1 - u) ^ b') =
        Real.Gamma (b + 1) * Real.Gamma (b' + 1) / Real.Gamma (b + b' + 2) := by
    calc
      _ = ∫ u in Ioc (0 : ℝ) 1, u ^ b * (1 - u) ^ b' :=
        intervalIntegral.integral_of_le (by norm_num)
      _ = ∫ u in Ioo (0 : ℝ) 1, u ^ b * (1 - u) ^ b' := integral_Ioc_eq_integral_Ioo
      _ = _ := hbetaIoo.symm.trans hbetaGamma
  have hscaleIntegrand (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
      (t * u) ^ b * (t - t * u) ^ b' =
        t ^ (b + b') * (u ^ b * (1 - u) ^ b') := by
    rw [show t - t * u = t * (1 - u) by ring,
      Real.mul_rpow ht.le hu.1.le,
      Real.mul_rpow ht.le (sub_nonneg.mpr hu.2.le)]
    calc
      t ^ b * u ^ b * (t ^ b' * (1 - u) ^ b') =
          (t ^ b * t ^ b') * (u ^ b * (1 - u) ^ b') := by ring
      _ = t ^ (b + b') * (u ^ b * (1 - u) ^ b') := by rw [← Real.rpow_add ht]
  have hscale :
      (∫ u in (0 : ℝ)..1, (t * u) ^ b * (t - t * u) ^ b') =
        t ^ (b + b') * (∫ u in (0 : ℝ)..1, u ^ b * (1 - u) ^ b') := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr_Ioo_of_le (by norm_num) fun u hu => hscaleIntegrand u hu
  have hchange :
      t * (∫ u in (0 : ℝ)..1, (t * u) ^ b * (t - t * u) ^ b') =
        ∫ s in Ioo (0 : ℝ) t, s ^ b * (t - s) ^ b' := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le]
    simpa only [smul_eq_mul, zero_mul, mul_zero, add_zero, mul_one, zero_add] using
      (intervalIntegral.smul_integral_comp_mul_add
        (a := (0 : ℝ)) (b := 1) (f := fun s : ℝ => s ^ b * (t - s) ^ b') t 0)
  calc
    ∫ s in Ioo (0 : ℝ) t, s ^ b * (t - s) ^ b' =
        t * (∫ u in (0 : ℝ)..1, (t * u) ^ b * (t - t * u) ^ b') := hchange.symm
    _ = t * (t ^ (b + b') * (∫ u in (0 : ℝ)..1, u ^ b * (1 - u) ^ b')) := by rw [hscale]
    _ = t ^ (b + b' + 1) *
        (Real.Gamma (b + 1) * Real.Gamma (b' + 1) / Real.Gamma (b + b' + 2)) := by
          rw [hbetaInterval]
          have hrpow : t ^ (b + b' + 1) = t * t ^ (b + b') := by
            rw [show b + b' + 1 = 1 + (b + b') by ring,
              Real.rpow_add ht, Real.rpow_one]
          rw [hrpow]
          ring

/-- Integrability of the two-endpoint Beta integrand. The singular powers are
handled on opposite halves of the interval, where the other factor is
continuous and bounded. -/
theorem integrableOn_rpow_mul_rpow_sub {t b b' : ℝ} (ht : 0 < t)
    (hb : -1 < b) (hb' : -1 < b') :
    IntegrableOn (fun s : ℝ => s ^ b * (t - s) ^ b') (Ioo 0 t) := by
  let m : ℝ := t / 2
  have hm0 : 0 < m := by dsimp [m]; linarith
  have hmt : m < t := by dsimp [m]; linarith
  have hleftPower : IntegrableOn (fun s : ℝ => s ^ b) (Ioo 0 m) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hm0).2 hb
  have hleftFactor : ContinuousOn (fun s : ℝ => (t - s) ^ b') (Icc 0 m) := by
    apply (by fun_prop : ContinuousOn (fun s : ℝ => t - s) (Icc 0 m)).rpow_const
    intro s hs
    left
    apply ne_of_gt
    have hs' : s ≤ m := hs.2
    dsimp [m] at hs'
    linarith
  have hleft : IntegrableOn (fun s : ℝ => s ^ b * (t - s) ^ b') (Ioo 0 m) :=
    hleftPower.mul_continuousOn_of_subset hleftFactor measurableSet_Ioo isCompact_Icc
      (by intro s hs; exact ⟨hs.1.le, hs.2.le⟩)
  have hrightPower : IntervalIntegrable (fun u : ℝ => u ^ b') volume 0 (t - m) :=
    intervalIntegral.intervalIntegrable_rpow' hb'
  have hrightReflect : IntervalIntegrable
      (fun s : ℝ => (t - s) ^ b') volume m t := by
    have h := (hrightPower.comp_sub_left t).symm
    have heq : t - (t - m) = m := by ring
    simpa only [heq, sub_zero] using h
  have hrightFactor : IntegrableOn (fun s : ℝ => (t - s) ^ b') (Ioo m t) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hmt.le
      (by finiteness) (by finiteness)).mp hrightReflect
  have hrightBase : ContinuousOn (fun s : ℝ => s ^ b) (Icc m t) := by
    apply (continuousOn_id : ContinuousOn (fun s : ℝ => s) (Icc m t)).rpow_const
    intro s hs
    left
    exact ne_of_gt (lt_of_lt_of_le hm0 hs.1)
  have hright : IntegrableOn (fun s : ℝ => s ^ b * (t - s) ^ b') (Ioo m t) :=
    IntegrableOn.continuousOn_mul_of_subset hrightBase hrightFactor isCompact_Icc measurableSet_Ioo
      (by intro s hs; exact ⟨hs.1.le, hs.2.le⟩)
  have hrightIco : IntegrableOn (fun s : ℝ => s ^ b * (t - s) ^ b') (Ico m t) := by
    rw [integrableOn_Ico_iff_integrableOn_Ioo' (μ := volume)
      (f := fun s : ℝ => s ^ b * (t - s) ^ b') (a := m) (b := t) (by simp)]
    exact hright
  rw [← Ioo_union_Ico_eq_Ioo hm0 hmt.le, integrableOn_union]
  exact ⟨hleft, hrightIco⟩

private theorem lintegral_heatKernel_rpow_sub_le {t q : ℝ} (ht : 0 < t) (hq : 1 < q)
    (y : Plane) :
    (∫⁻ x : Plane, (ENNReal.ofReal (heatKernel t (y - x))) ^ q) ≤
      ENNReal.ofReal (((2 * Real.pi * t)⁻¹) ^ (q - 1)) := by
  let k : Plane → ℝ := fun x => heatKernel t (y - x)
  let A : ℝ := (2 * Real.pi * t)⁻¹
  have hA : 0 < A := by dsimp [A]; positivity
  have hkEq : k = fun x => heatKernel t (x - y) := by
    funext x
    dsimp [k]
    rw [show y - x = -(x - y) by abel, heatKernel_neg]
  have hkInt : Integrable k := by
    rw [hkEq]
    exact (integrable_heatKernel ht).comp_sub_right y
  have hmass : (∫ x : Plane, k x) = 1 := by
    rw [hkEq]
    exact integral_heatKernel_sub ht y
  have hkmeas : Measurable k := by
    dsimp [k]
    exact (measurable_heatKernel t).comp (measurable_const.sub measurable_id)
  have hpmeas : Measurable (fun x : Plane => k x ^ q) :=
    measurable_real_rpow.comp (hkmeas.prodMk measurable_const)
  have hpoint (x : Plane) : k x ^ q ≤ A ^ (q - 1) * k x := by
    have hkpos : 0 < k x := by dsimp [k]; exact heatKernel_pos ht _
    have hk0 : 0 ≤ k x := hkpos.le
    have hkupper : k x ≤ A := by
      dsimp [k, A]
      exact heatKernel_le_at_zero ht.le _
    calc
      k x ^ q = k x ^ ((q - 1) + 1) := by congr 1; ring
      _ = k x ^ (q - 1) * k x := by rw [Real.rpow_add hkpos, Real.rpow_one]
      _ ≤ A ^ (q - 1) * k x :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hk0 hkupper (by linarith)) hk0
  have hdomInt : Integrable (fun x : Plane => A ^ (q - 1) * k x) := hkInt.const_mul _
  have hpowInt : Integrable (fun x : Plane => k x ^ q) := by
    apply hdomInt.mono' hpmeas.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (le_of_lt (heatKernel_pos ht _)) _)]
    exact hpoint x
  have hreal : (∫ x : Plane, k x ^ q) ≤ A ^ (q - 1) := by
    calc
      (∫ x : Plane, k x ^ q) ≤ ∫ x : Plane, A ^ (q - 1) * k x :=
        integral_mono hpowInt hdomInt hpoint
      _ = A ^ (q - 1) := by rw [integral_const_mul, hmass, mul_one]
  have hconv := ofReal_integral_eq_lintegral_ofReal hpowInt
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (le_of_lt (heatKernel_pos ht _)) _)
  calc
    (∫⁻ x : Plane, (ENNReal.ofReal (k x)) ^ q) = ∫⁻ x : Plane, ENNReal.ofReal (k x ^ q) := by
      apply lintegral_congr
      intro x
      exact ENNReal.ofReal_rpow_of_nonneg (le_of_lt (heatKernel_pos ht _)) (by positivity)
    _ = ENNReal.ofReal (∫ x : Plane, k x ^ q) := hconv.symm
    _ ≤ ENNReal.ofReal (A ^ (q - 1)) := ENNReal.ofReal_le_ofReal hreal

/-- Nonnegative planar heat convolution has the `Lᵖ` point-evaluation bound in Tsai (2024), equation (2.10c). -/
theorem integral_heatKernel_mul_le {p : ℝ} (hp : 1 < p) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 < t → ∀ (y : Plane) (ψ : Plane → ℝ≥0∞), Measurable ψ →
      ∫⁻ x, ENNReal.ofReal (heatKernel t (y - x)) * ψ x ≤
        ENNReal.ofReal (c * t ^ (-1 / p)) * (∫⁻ x, ψ x ^ p) ^ (1 / p) := by
  let q : ℝ := p / (p - 1)
  let c : ℝ := (2 * Real.pi) ^ (-1 / p)
  have hpden : 0 < p - 1 := by linarith
  have hq : 1 < q := by
    dsimp [q]
    rw [lt_div_iff₀ hpden]
    linarith
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hpq : p.HolderConjugate q := (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  have hqexp : (q - 1) * (1 / q) = 1 / p := by
    dsimp [q]
    field_simp
    ring
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro t ht y ψ hψ
  have hkernel := lintegral_heatKernel_rpow_sub_le ht hq y
  let A : ℝ := (2 * Real.pi * t)⁻¹
  have hA : 0 < A := by dsimp [A]; positivity
  have hscale : (A ^ (q - 1)) ^ (1 / q) = c * t ^ (-1 / p) := by
    calc
      (A ^ (q - 1)) ^ (1 / q) = A ^ ((q - 1) * (1 / q)) := by
        rw [← Real.rpow_mul hA.le]
      _ = A ^ (1 / p) := by rw [hqexp]
      _ = (2 * Real.pi * t) ^ (-1 / p) := by
        dsimp [A]
        rw [Real.inv_rpow (by positivity)]
        rw [← Real.rpow_neg (by positivity : 0 ≤ 2 * Real.pi * t)]
        congr 1
        ring
      _ = c * t ^ (-1 / p) := by
        dsimp [c]
        rw [Real.mul_rpow (by positivity) ht.le]
  have hroot := ENNReal.rpow_le_rpow hkernel (by positivity : 0 ≤ 1 / q)
  have hrootEq : (ENNReal.ofReal (A ^ (q - 1))) ^ (1 / q) =
      ENNReal.ofReal ((A ^ (q - 1)) ^ (1 / q)) :=
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hA.le _) (by positivity)
  have hnorm :
      (∫⁻ x : Plane, (ENNReal.ofReal (heatKernel t (y - x))) ^ q) ^ (1 / q) ≤
        ENNReal.ofReal (c * t ^ (-1 / p)) := by
    calc
      _ ≤ (ENNReal.ofReal (A ^ (q - 1))) ^ (1 / q) := hroot
      _ = ENNReal.ofReal ((A ^ (q - 1)) ^ (1 / q)) := hrootEq
      _ = ENNReal.ofReal (c * t ^ (-1 / p)) := by rw [hscale]
  have hkernelMeas : Measurable (fun x : Plane => ENNReal.ofReal (heatKernel t (y - x))) := by
    exact ((measurable_heatKernel t).comp (measurable_const.sub measurable_id)).ennreal_ofReal
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq hψ.aemeasurable
    hkernelMeas.aemeasurable
  calc
    ∫⁻ x, ENNReal.ofReal (heatKernel t (y - x)) * ψ x ≤
        (∫⁻ x, ψ x ^ p) ^ (1 / p) *
          (∫⁻ x, (ENNReal.ofReal (heatKernel t (y - x))) ^ q) ^ (1 / q) := by
      simpa only [Pi.mul_apply, mul_comm] using hholder
    _ ≤ (∫⁻ x, ψ x ^ p) ^ (1 / p) * ENNReal.ofReal (c * t ^ (-1 / p)) :=
      mul_le_mul' le_rfl hnorm
    _ = ENNReal.ofReal (c * t ^ (-1 / p)) * (∫⁻ x, ψ x ^ p) ^ (1 / p) := by rw [mul_comm]

/-- A positive kernel with row masses at most one and column masses at most `B` satisfies Schur's `Lᵖ` bound with `p`th-power constant `B`. -/
theorem lintegral_kernel_lp_schur {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {K : X → Y → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {p q : ℝ} {B : ℝ≥0∞} (hpq : p.HolderConjugate q)
    (hrow : ∀ x, ∫⁻ y, K x y ∂ν ≤ 1) (hcol : ∀ y, ∫⁻ x, K x y ∂μ ≤ B)
    {f : Y → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ p ∂μ) ≤
      B * ∫⁻ y, f y ^ p ∂ν := by
  let A : X → ℝ≥0∞ := fun x => ∫⁻ y, K x y * f y ∂ν
  have hAmeas : Measurable A := measurable_kernelAction ν hK hf
  have hKsection (x : X) : Measurable (K x) :=
    hK.comp (measurable_const.prodMk measurable_id)
  have hAction (x : X) : A x ^ p ≤ ∫⁻ y, K x y * f y ^ p ∂ν := by
    let ρ : Measure Y := ν.withDensity (K x)
    have hmass : (∫⁻ y, (1 : ℝ≥0∞) ∂ρ) = ∫⁻ y, K x y ∂ν := by
      rw [lintegral_withDensity_eq_lintegral_mul ν (hKsection x) measurable_const]
      simp only [Pi.mul_apply, mul_one]
    have hfp : (∫⁻ y, f y ^ p ∂ρ) =
        ∫⁻ y, K x y * f y ^ p ∂ν := by
      rw [lintegral_withDensity_eq_lintegral_mul ν (hKsection x) (hf.pow_const p)]
      simp only [Pi.mul_apply]
    have hleft : (∫⁻ y, f y ∂ρ) = A x := by
      rw [lintegral_withDensity_eq_lintegral_mul ν (hKsection x) hf]
      rfl
    have hpnonneg : 0 ≤ p := hpq.left_pos.le
    have hqnonneg : 0 ≤ q := hpq.right_pos.le
    have hqInvNonneg : 0 ≤ 1 / q := one_div_nonneg.mpr hqnonneg
    have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq ρ hpq hf.aemeasurable
      ((measurable_const : Measurable (fun _ : Y => (1 : ℝ≥0∞))).aemeasurable)
    have hHolder' : (∫⁻ y, f y ∂ρ) ≤
        (∫⁻ y, f y ^ p ∂ρ) ^ (1 / p) *
          (∫⁻ y, (1 : ℝ≥0∞) ^ q ∂ρ) ^ (1 / q) := by
      simpa only [Pi.mul_apply, mul_one] using hHolder
    have hmassRoot : (∫⁻ y, (1 : ℝ≥0∞) ^ q ∂ρ) ^ (1 / q) ≤ 1 := by
      calc
        _ = (∫⁻ y, (1 : ℝ≥0∞) ∂ρ) ^ (1 / q) := by
          congr 1
          apply lintegral_congr
          intro y
          exact ENNReal.one_rpow _
        _ ≤ 1 ^ (1 / q) := ENNReal.rpow_le_rpow
          (calc
            (∫⁻ y, (1 : ℝ≥0∞) ∂ρ) = ∫⁻ y, K x y ∂ν := hmass
            _ ≤ 1 := hrow x) hqInvNonneg
        _ = 1 := by simp
    have hroot : A x ≤ (∫⁻ y, K x y * f y ^ p ∂ν) ^ (1 / p) := by
      calc
        A x = ∫⁻ y, f y ∂ρ := hleft.symm
        _ ≤ (∫⁻ y, f y ^ p ∂ρ) ^ (1 / p) *
              (∫⁻ y, (1 : ℝ≥0∞) ^ q ∂ρ) ^ (1 / q) := hHolder'
        _ ≤ (∫⁻ y, K x y * f y ^ p ∂ν) ^ (1 / p) * 1 :=
          mul_le_mul' (by rw [hfp]) hmassRoot
        _ = _ := by simp
    have hpow := ENNReal.rpow_le_rpow hroot hpnonneg
    calc
      A x ^ p ≤
          ((∫⁻ y, K x y * f y ^ p ∂ν) ^ (1 / p)) ^ p := hpow
      _ = ∫⁻ y, K x y * f y ^ p ∂ν := by
        rw [← ENNReal.rpow_mul]
        have he : (1 / p) * p = 1 := by field_simp [ne_of_gt hpq.left_pos]
        rw [he, ENNReal.rpow_one]
  have hProd : Measurable (fun z : X × Y => K z.1 z.2 * f z.2 ^ p) :=
    hK.mul ((hf.comp measurable_snd).pow_const p)
  calc
    (∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ p ∂μ) ≤
        ∫⁻ x, ∫⁻ y, K x y * f y ^ p ∂ν ∂μ := by
      apply lintegral_mono
      exact hAction
    _ = ∫⁻ y, ∫⁻ x, K x y * f y ^ p ∂μ ∂ν :=
      lintegral_lintegral_swap hProd.aemeasurable
    _ ≤ ∫⁻ y, B * f y ^ p ∂ν := by
      apply lintegral_mono
      intro y
      change (∫⁻ x, K x y * f y ^ p ∂μ) ≤ B * f y ^ p
      have hKy : Measurable (fun x : X => K x y) := hK.comp (measurable_id.prodMk measurable_const)
      rw [lintegral_mul_const _ hKy]
      exact mul_le_mul' (hcol y) le_rfl
    _ = B * ∫⁻ y, f y ^ p ∂ν := lintegral_const_mul B (hf.pow_const p)

/-- Symmetric row and column mass bounds give the sharp Schur estimate on
`Lᵖ`: if both masses are at most `M`, the `p`th power of the operator norm is
at most `M ^ p`. -/
theorem lintegral_kernel_lp_schur_of_mass_bound {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {K : X → Y → ℝ≥0∞} (hK : Measurable (Function.uncurry K)
    ) {p q : ℝ} (hpq : p.HolderConjugate q) {M : ℝ≥0∞}
    (hM0 : M ≠ 0) (hMtop : M ≠ ⊤)
    (hrow : ∀ x, ∫⁻ y, K x y ∂ν ≤ M)
    (hcol : ∀ y, ∫⁻ x, K x y ∂μ ≤ M)
    {f : Y → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, (∫⁻ y, K x y * f y ∂ν) ^ p ∂μ) ≤
      M ^ p * ∫⁻ y, f y ^ p ∂ν := by
  let K' : X → Y → ℝ≥0∞ := fun x y => M⁻¹ * K x y
  have hMinvTop : M⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hM0
  have hMcancel : M * M⁻¹ = 1 := ENNReal.mul_inv_cancel hM0 hMtop
  have hK'meas : Measurable (Function.uncurry K') := by
    exact measurable_const.mul hK
  have hrow' (x : X) : ∫⁻ y, K' x y ∂ν ≤ 1 := by
    calc
      ∫⁻ y, K' x y ∂ν = M⁻¹ * ∫⁻ y, K x y ∂ν := by
        exact lintegral_const_mul' M⁻¹ (K x) hMinvTop
      _ ≤ M⁻¹ * M := mul_le_mul' le_rfl (hrow x)
      _ = 1 := by rw [mul_comm M⁻¹ M, hMcancel]
  have hcol' (y : Y) : ∫⁻ x, K' x y ∂μ ≤ 1 := by
    calc
      ∫⁻ x, K' x y ∂μ = M⁻¹ * ∫⁻ x, K x y ∂μ := by
        exact lintegral_const_mul' M⁻¹ (fun x => K x y) hMinvTop
      _ ≤ M⁻¹ * M := mul_le_mul' le_rfl (hcol y)
      _ = 1 := by rw [mul_comm M⁻¹ M, hMcancel]
  have hschur := lintegral_kernel_lp_schur hK'meas hpq hrow' hcol' hf
  have hscale (x : X) :
      (∫⁻ y, K x y * f y ∂ν) = M * (∫⁻ y, K' x y * f y ∂ν) := by
    calc
      _ = ∫⁻ y, M * (K' x y * f y) ∂ν := by
        apply lintegral_congr
        intro y
        change K x y * f y = M * ((M⁻¹ * K x y) * f y)
        calc
          K x y * f y = (M * M⁻¹) * (K x y * f y) := by rw [hMcancel, one_mul]
          _ = M * ((M⁻¹ * K x y) * f y) := by ac_rfl
      _ = _ := lintegral_const_mul' M (fun y => K' x y * f y) hMtop
  have hpoint (x : X) :
      (∫⁻ y, K x y * f y ∂ν) ^ p ≤
        M ^ p * (∫⁻ y, K' x y * f y ∂ν) ^ p := by
    rw [hscale x, ENNReal.mul_rpow_of_nonneg _ _ hpq.left_pos.le]
  have hMpTop : M ^ p ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hpq.left_pos.le hMtop
  calc
    _ ≤ ∫⁻ x, M ^ p * (∫⁻ y, K' x y * f y ∂ν) ^ p ∂μ := by
      apply lintegral_mono
      exact hpoint
    _ = M ^ p * ∫⁻ x, (∫⁻ y, K' x y * f y ∂ν) ^ p ∂μ :=
      lintegral_const_mul' _ _ hMpTop
    _ ≤ M ^ p * (1 * ∫⁻ y, f y ^ p ∂ν) := mul_le_mul' le_rfl hschur
    _ = M ^ p * ∫⁻ y, f y ^ p ∂ν := by simp

/-- The incoming kernel has an unweighted `Lᵖ → Lᵖ` form bound of order `t^{-1/p}`, as in Tsai (2024), equation (2.10d). -/
theorem weightedFormBound_incoming_unweighted {n : ℕ} (α : CollisionPair n) {p : ℝ} (hp : 1 < p) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 < t →
      WeightedFormBound volume volume (fun _ => 0) (fun _ => 0) p (p / (p - 1))
        (fun (y : FusedConfiguration α) (x : Configuration n) =>
          ENNReal.ofReal (incomingKernel α t y x)) (ENNReal.ofReal (c * t ^ (-1 / p))) := by
  let q : ℝ := p / (p - 1)
  let c : ℝ := (4 * Real.pi) ^ (-1 / p)
  have hpden : 0 < p - 1 := by linarith
  have hq : 1 < q := by
    dsimp [q]
    rw [lt_div_iff₀ hpden]
    linarith
  have hpq : p.HolderConjugate q := (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro t ht
  let K : FusedConfiguration α → Configuration n → ℝ≥0∞ := fun z x =>
    ENNReal.ofReal (incomingKernel α t z x)
  let B : ℝ≥0∞ := (ENNReal.ofReal (4 * Real.pi * t))⁻¹
  have hK : Measurable (Function.uncurry K) := by
    change Measurable (fun z : FusedConfiguration α × Configuration n =>
      ENNReal.ofReal (incomingKernel α t z.1 z.2))
    exact ((measurable_incomingKernel α).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hrow (z : FusedConfiguration α) : (∫⁻ x : Configuration n, K z x) ≤ 1 := by
    simpa only [K] using (lintegral_incomingKernel_full α ht z).le
  have hB : B = ENNReal.ofReal ((4 * Real.pi * t)⁻¹) := by
    dsimp [B]
    rw [ENNReal.ofReal_inv_of_pos (by positivity : 0 < 4 * Real.pi * t)]
  have hcol (x : Configuration n) : (∫⁻ z : FusedConfiguration α, K z x) ≤ B := by
    rw [hB]
    simpa only [K] using lintegral_incomingKernel_fused_le α ht x
  have hCroot : B ^ (1 / p) = ENNReal.ofReal (c * t ^ (-1 / p)) := by
    calc
      B ^ (1 / p) = ENNReal.ofReal (((4 * Real.pi * t)⁻¹) ^ (1 / p)) := by
        rw [hB, ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ (4 * Real.pi * t)⁻¹)
          (by positivity)]
      _ = ENNReal.ofReal ((4 * Real.pi * t) ^ (-1 / p)) := by
        congr 1
        rw [Real.inv_rpow (by positivity)]
        rw [← Real.rpow_neg (by positivity : 0 ≤ 4 * Real.pi * t)]
        congr 1
        ring
      _ = ENNReal.ofReal ((4 * Real.pi) ^ (-1 / p) * t ^ (-1 / p)) := by
        congr 1
        rw [Real.mul_rpow (by positivity) ht.le]
      _ = ENNReal.ofReal (c * t ^ (-1 / p)) := by rw [show c = (4 * Real.pi) ^ (-1 / p) by rfl]
  intro f g hf hg
  let A : FusedConfiguration α → ℝ≥0∞ := fun z => ∫⁻ x, K z x * f x ∂volume
  have hA : Measurable A := measurable_kernelAction volume hK hf
  have hLp := lintegral_kernel_lp_schur hK hpq hrow hcol hf
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq hA.aemeasurable hg.aemeasurable
  have hAroot : (∫⁻ z, A z ^ p ∂volume) ^ (1 / p) ≤
      ENNReal.ofReal (c * t ^ (-1 / p)) * (∫⁻ x, f x ^ p ∂volume) ^ (1 / p) := by
    calc
      _ ≤ (B * ∫⁻ x, f x ^ p ∂volume) ^ (1 / p) := by
        exact ENNReal.rpow_le_rpow hLp (by positivity)
      _ = B ^ (1 / p) * (∫⁻ x, f x ^ p ∂volume) ^ (1 / p) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
      _ = _ := by rw [hCroot]
  have hfinal : (∫⁻ z, g z * (∫⁻ x, K z x * f x ∂volume) ∂volume) ≤
      ENNReal.ofReal (c * t ^ (-1 / p)) * (∫⁻ x, f x ^ p ∂volume) ^ (1 / p) *
        (∫⁻ z, g z ^ q ∂volume) ^ (1 / q) := calc
    (∫⁻ z, g z * (∫⁻ x, K z x * f x ∂volume) ∂volume) ≤
        (∫⁻ z, A z ^ p ∂volume) ^ (1 / p) * (∫⁻ z, g z ^ q ∂volume) ^ (1 / q) := by
      simpa only [A, Pi.mul_apply, mul_comm] using hHolder
    _ ≤ ENNReal.ofReal (c * t ^ (-1 / p)) * (∫⁻ x, f x ^ p ∂volume) ^ (1 / p) *
        (∫⁻ z, g z ^ q ∂volume) ^ (1 / q) := mul_le_mul' hAroot le_rfl
  simpa [q, Real.exp_zero] using hfinal

/-- The exponentially weighted `Lᵖ` norm controls the configuration `L²` norm, as in Tsai (2024), equation (2.10b). -/
theorem lintegral_sq_le_weighted {n : ℕ} {p a : ℝ} (hp : 2 < p) (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : Configuration n → ℝ≥0∞, Measurable f →
      (∫⁻ x, f x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal c *
          (∫⁻ x, (f x * ENNReal.ofReal (Real.exp (a * configurationOneNorm x))) ^ p) ^ (1 / p) := by
  let r : ℝ := p / 2
  let q : ℝ := p / (p - 2)
  let M : ℝ := ((2 / (2 * a * q)) ^ 2) ^ n
  let c : ℝ := M ^ (1 / (2 * q))
  have hpden : 0 < p - 2 := by linarith
  have hr : 1 < r := by dsimp [r]; linarith
  have hq : 0 < q := by dsimp [q]; positivity
  have hrq : r.HolderConjugate q := by
    rw [Real.holderConjugate_iff_eq_conjExponent hr]
    dsimp [r, q]
    have hpden' : p - 2 ≠ 0 := ne_of_gt hpden
    field_simp [hpden']
  have hb : 0 < 2 * a * q := by positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hc : 0 < c := by dsimp [c]; exact Real.rpow_pos_of_pos hM _
  refine ⟨c, hc, ?_⟩
  intro f hf
  let w : Configuration n → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.exp (a * configurationOneNorm x))
  let F : Configuration n → ℝ≥0∞ := fun x => (f x * w x) ^ 2
  let G : Configuration n → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.exp (-2 * a * configurationOneNorm x))
  have hN : Measurable (configurationOneNorm : Configuration n → ℝ) :=
    measurable_configurationOneNorm
  have hw : Measurable w := by
    dsimp [w]
    exact (measurable_const.mul hN).exp.ennreal_ofReal
  have hF : Measurable F := by
    dsimp [F]
    exact (hf.mul hw).pow_const 2
  have hG : Measurable G := by
    dsimp [G]
    exact (measurable_const.mul hN).exp.ennreal_ofReal
  have hexp (x : Configuration n) :
      Real.exp (a * configurationOneNorm x) ^ 2 *
        Real.exp (-2 * a * configurationOneNorm x) = 1 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    rw [show a * configurationOneNorm x + a * configurationOneNorm x +
      -2 * a * configurationOneNorm x = 0 by ring, Real.exp_zero]
  have hfactor (x : Configuration n) : f x ^ (2 : ℝ) = F x * G x := by
    rw [ENNReal.rpow_two]
    dsimp [F, G, w]
    rw [mul_pow, ← ENNReal.ofReal_pow (Real.exp_nonneg _) 2, mul_assoc,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp (a * configurationOneNorm x) ^ 2),
      hexp x, ENNReal.ofReal_one]
    simp
  have hFpow (x : Configuration n) : F x ^ r =
      (f x * ENNReal.ofReal (Real.exp (a * configurationOneNorm x))) ^ p := by
    dsimp [F, w]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    dsimp [r]
    ring
  have hFint : (∫⁻ x, F x ^ r) =
      ∫⁻ x, (f x * ENNReal.ofReal (Real.exp (a * configurationOneNorm x))) ^ p := by
    apply lintegral_congr
    exact hFpow
  have hGpow (x : Configuration n) : G x ^ q =
      configurationExpDecayKernel (2 * a * q) (fun _ : Fin n => 0) x := by
    rw [configurationExpDecayKernel_apply]
    dsimp [G]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_nonneg _) (le_of_lt hq), ← Real.exp_mul]
    congr 1
    simp only [configurationOneNorm, sub_zero]
    ring_nf
  have hGint : (∫⁻ x, G x ^ q) = ENNReal.ofReal M := by
    calc
      (∫⁻ x, G x ^ q) =
          ∫⁻ x, configurationExpDecayKernel (2 * a * q) (fun _ : Fin n => 0) x := by
        apply lintegral_congr
        exact hGpow
      _ = ENNReal.ofReal M := by
        dsimp [M]
        exact lintegral_configurationExpDecayKernel_right hb (fun _ => 0)
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hrq hF.aemeasurable hG.aemeasurable
  have hmain : (∫⁻ x, f x ^ (2 : ℝ)) ≤ (∫⁻ x, F x ^ r) ^ (1 / r) *
      (∫⁻ x, G x ^ q) ^ (1 / q) := by
    calc
      (∫⁻ x, f x ^ (2 : ℝ)) = ∫⁻ x, F x * G x := by
        apply lintegral_congr
        intro x
        exact hfactor x
      _ ≤ (∫⁻ x, F x ^ r) ^ (1 / r) * (∫⁻ x, G x ^ q) ^ (1 / q) := hholder
  have hpexp : (1 / r) * (1 / 2 : ℝ) = 1 / p := by dsimp [r]; field_simp
  have hqexp : (1 / q) * (1 / 2) = 1 / (2 * q) := by ring
  have hrootprod (A B : ℝ≥0∞) : (A ^ (1 / r) * B ^ (1 / q)) ^ (1 / 2 : ℝ) =
      A ^ (1 / p) * B ^ (1 / (2 * q)) := by
    calc
      (A ^ (1 / r) * B ^ (1 / q)) ^ (1 / 2 : ℝ) =
          (A ^ (1 / r)) ^ (1 / 2 : ℝ) * (B ^ (1 / q)) ^ (1 / 2 : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (1 / 2 : ℝ))
      _ = A ^ (1 / p) * B ^ (1 / (2 * q)) := by
        rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hpexp, hqexp]
  have hMroot : (ENNReal.ofReal M) ^ (1 / (2 * q)) = ENNReal.ofReal c := by
    rw [ENNReal.ofReal_rpow_of_nonneg hM.le (by positivity)]
  have hsqrt := ENNReal.rpow_le_rpow hmain (by norm_num : 0 ≤ (1 / 2 : ℝ))
  calc
    (∫⁻ x, f x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        (∫⁻ x, F x ^ r) ^ (1 / p) * ENNReal.ofReal c := by
      calc
        _ ≤ ((∫⁻ x, F x ^ r) ^ (1 / r) * (∫⁻ x, G x ^ q) ^ (1 / q)) ^ (1 / 2) := hsqrt
        _ = (∫⁻ x, F x ^ r) ^ (1 / p) * (∫⁻ x, G x ^ q) ^ (1 / (2 * q)) :=
          hrootprod _ _
        _ = _ := by rw [hGint, hMroot]
    _ = ENNReal.ofReal c *
        (∫⁻ x, (f x * ENNReal.ofReal (Real.exp (a * configurationOneNorm x))) ^ p) ^ (1 / p) := by
      rw [hFint]
      exact mul_comm _ _

/-- The same weighted `Lᵖ` to `L²` embedding on a fused collision space. -/
theorem lintegral_sq_le_weighted_fused {n : ℕ} (α : CollisionPair n) {p a : ℝ}
    (hp : 2 < p) (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : FusedConfiguration α → ℝ≥0∞, Measurable f →
      (∫⁻ z, f z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal c *
          (∫⁻ z, (f z * ENNReal.ofReal (Real.exp (a * fusedOneNorm α z))) ^ p) ^ (1 / p) := by
  let r : ℝ := p / 2
  let q : ℝ := p / (p - 2)
  let M : ℝ := ((2 / (2 * a * q)) ^ 2) ^ (Fintype.card (Spectator α) + 1)
  let c : ℝ := M ^ (1 / (2 * q))
  have hpden : 0 < p - 2 := by linarith
  have hr : 1 < r := by dsimp [r]; linarith
  have hq : 0 < q := by dsimp [q]; positivity
  have hrq : r.HolderConjugate q := by
    rw [Real.holderConjugate_iff_eq_conjExponent hr]
    dsimp [r, q]
    have hpden' : p - 2 ≠ 0 := ne_of_gt hpden
    field_simp [hpden']
  have hb : 0 < 2 * a * q := by positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hc : 0 < c := by dsimp [c]; exact Real.rpow_pos_of_pos hM _
  refine ⟨c, hc, ?_⟩
  intro f hf
  let w : FusedConfiguration α → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (a * fusedOneNorm α z))
  let F : FusedConfiguration α → ℝ≥0∞ := fun z => (f z * w z) ^ 2
  let G : FusedConfiguration α → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (-2 * a * fusedOneNorm α z))
  have hN : Measurable (fusedOneNorm α) := by
    unfold fusedOneNorm
    apply (measurable_const.mul (measurable_planeOneNorm.comp measurable_fst)).add
    apply Finset.measurable_sum
    intro i hi
    exact measurable_planeOneNorm.comp ((measurable_pi_apply i).comp measurable_snd)
  have hw : Measurable w := by
    dsimp [w]
    exact (measurable_const.mul hN).exp.ennreal_ofReal
  have hF : Measurable F := by
    dsimp [F]
    exact (hf.mul hw).pow_const 2
  have hG : Measurable G := by
    dsimp [G]
    exact (measurable_const.mul hN).exp.ennreal_ofReal
  have hexp (z : FusedConfiguration α) :
      Real.exp (a * fusedOneNorm α z) ^ 2 *
        Real.exp (-2 * a * fusedOneNorm α z) = 1 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    rw [show a * fusedOneNorm α z + a * fusedOneNorm α z +
      (-2 * a * fusedOneNorm α z) = 0 by ring, Real.exp_zero]
  have hfactor (z : FusedConfiguration α) : f z ^ (2 : ℝ) = F z * G z := by
    rw [ENNReal.rpow_two]
    dsimp [F, G, w]
    rw [mul_pow, ← ENNReal.ofReal_pow (Real.exp_nonneg _) 2, mul_assoc,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp (a * fusedOneNorm α z) ^ 2),
      hexp z, ENNReal.ofReal_one]
    simp
  have hFpow (z : FusedConfiguration α) : F z ^ r =
      (f z * ENNReal.ofReal (Real.exp (a * fusedOneNorm α z))) ^ p := by
    dsimp [F, w]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    dsimp [r]
    ring
  have hFint : (∫⁻ z, F z ^ r) =
      ∫⁻ z, (f z * ENNReal.ofReal (Real.exp (a * fusedOneNorm α z))) ^ p := by
    apply lintegral_congr
    exact hFpow
  have hGpow (z : FusedConfiguration α) : G z ^ q =
      fusedConfigurationExpDecayKernel α (2 * a * q) (fun _ => 0) z := by
    rw [fusedConfigurationExpDecayKernel_eq, configurationExpDecayKernel_apply]
    dsimp [G]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_nonneg _) (le_of_lt hq), ← Real.exp_mul]
    congr 1
    simp only [sub_zero, configurationOneNorm_collisionEmbedding]
    ring
  have hGint : (∫⁻ z, G z ^ q) ≤ ENNReal.ofReal M := by
    calc
      (∫⁻ z, G z ^ q) =
          ∫⁻ z, fusedConfigurationExpDecayKernel α (2 * a * q) (fun _ => 0) z := by
        apply lintegral_congr
        exact hGpow
      _ ≤ ENNReal.ofReal M := by
        dsimp [M]
        exact lintegral_fusedConfigurationExpDecayKernel_right α hb (fun _ => 0)
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hrq hF.aemeasurable hG.aemeasurable
  have hmain : (∫⁻ z, f z ^ (2 : ℝ)) ≤
      (∫⁻ z, F z ^ r) ^ (1 / r) * (∫⁻ z, G z ^ q) ^ (1 / q) := by
    calc
      (∫⁻ z, f z ^ (2 : ℝ)) = ∫⁻ z, F z * G z := by
        apply lintegral_congr
        intro z
        exact hfactor z
      _ ≤ (∫⁻ z, F z ^ r) ^ (1 / r) * (∫⁻ z, G z ^ q) ^ (1 / q) := hholder
  have hpexp : (1 / r) * (1 / 2 : ℝ) = 1 / p := by dsimp [r]; field_simp
  have hqexp : (1 / q) * (1 / 2) = 1 / (2 * q) := by ring
  have hrootprod (A B : ℝ≥0∞) : (A ^ (1 / r) * B ^ (1 / q)) ^ (1 / 2 : ℝ) =
      A ^ (1 / p) * B ^ (1 / (2 * q)) := by
    calc
      (A ^ (1 / r) * B ^ (1 / q)) ^ (1 / 2 : ℝ) =
          (A ^ (1 / r)) ^ (1 / 2 : ℝ) * (B ^ (1 / q)) ^ (1 / 2 : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (1 / 2 : ℝ))
      _ = A ^ (1 / p) * B ^ (1 / (2 * q)) := by
        rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hpexp, hqexp]
  have hMroot : (ENNReal.ofReal M) ^ (1 / (2 * q)) = ENNReal.ofReal c := by
    rw [ENNReal.ofReal_rpow_of_nonneg hM.le (by positivity)]
  have hrootExp : 0 ≤ 1 / (2 * q) := by positivity
  have hsqrt := ENNReal.rpow_le_rpow hmain (by norm_num : 0 ≤ (1 / 2 : ℝ))
  calc
    (∫⁻ z, f z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal c *
          (∫⁻ z, (f z * ENNReal.ofReal (Real.exp (a * fusedOneNorm α z))) ^ p) ^ (1 / p) := by
      calc
        _ ≤ ((∫⁻ z, F z ^ r) ^ (1 / r) * (∫⁻ z, G z ^ q) ^ (1 / q)) ^ (1 / 2) := hsqrt
        _ = (∫⁻ z, F z ^ r) ^ (1 / p) * (∫⁻ z, G z ^ q) ^ (1 / (2 * q)) :=
          hrootprod _ _
        _ ≤ (∫⁻ z, F z ^ r) ^ (1 / p) * ENNReal.ofReal c := by
          apply mul_le_mul' le_rfl
          calc
            _ ≤ (ENNReal.ofReal M) ^ (1 / (2 * q)) :=
              ENNReal.rpow_le_rpow hGint hrootExp
            _ = ENNReal.ofReal c := hMroot
        _ = _ := by rw [hFint, mul_comm]

/-- The incoming kernel maps weighted `Lᵖ` to weighted `Lᵖ` with norm at most `C t^{-1/p}` for `0 < t ≤ 1`. -/
theorem incomingWeightedLp_small {n : ℕ} (α : CollisionPair n) {p a : ℝ}
    (hp : 1 < p) (ha : 0 ≤ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∀ f : Configuration n → ℝ≥0∞, Measurable f →
        (∫⁻ z : FusedConfiguration α,
          ((∫⁻ x : Configuration n, ENNReal.ofReal (incomingKernel α t z x) * f x) *
            ENNReal.ofReal (Real.exp (a * fusedOneNorm α z))) ^ p ∂volume) ^ (1 / p) ≤
          ENNReal.ofReal (C * t ^ ((-1 : ℝ) / p)) *
            (∫⁻ x : Configuration n,
              (f x * ENNReal.ofReal (Real.exp (a * configurationOneNorm x))) ^ p ∂volume) ^ (1 / p) := by
  let D : ℝ := 2 ^ n * Real.exp (2 * n * a ^ 2)
  let C : ℝ := D * (8 * Real.pi) ^ ((-1 : ℝ) / p)
  let q : ℝ := p / (p - 1)
  have hpden : 0 < p - 1 := by linarith
  have hq : 1 < q := by
    dsimp [q]
    rw [lt_div_iff₀ hpden]
    linarith
  have hpq : p.HolderConjugate q := (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hDgrowth {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) : weightGrowth n a t ≤ D := by
    unfold weightGrowth
    dsimp [D]
    apply mul_le_mul_of_nonneg_left
    · apply Real.exp_le_exp.mpr
      have hcoef : 0 ≤ (2 : ℝ) * n * a ^ 2 := by positivity
      simpa only [mul_one] using mul_le_mul_of_nonneg_left ht1 hcoef
    · positivity
  have hBroot {t : ℝ} (ht : 0 < t) :
      ((ENNReal.ofReal (4 * Real.pi * (2 * t)))⁻¹) ^ (1 / p) =
        ENNReal.ofReal ((8 * Real.pi) ^ ((-1 : ℝ) / p) * t ^ ((-1 : ℝ) / p)) := by
    have hpos : 0 < 8 * Real.pi * t := by positivity
    have hbase : 0 < 8 * Real.pi := by positivity
    have hinv : (ENNReal.ofReal (8 * Real.pi * t))⁻¹ =
        ENNReal.ofReal ((8 * Real.pi * t)⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos hpos]
    rw [show 4 * Real.pi * (2 * t) = 8 * Real.pi * t by ring, hinv,
      ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ (8 * Real.pi * t)⁻¹)
        (by positivity)]
    congr 1
    calc
      (8 * Real.pi * t)⁻¹ ^ (1 / p) = (8 * Real.pi * t) ^ ((-1 : ℝ) / p) := by
        rw [Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity : 0 ≤ 8 * Real.pi * t)]
        congr 1
        ring
      _ = (8 * Real.pi) ^ ((-1 : ℝ) / p) * t ^ ((-1 : ℝ) / p) := by
        rw [Real.mul_rpow hbase.le ht.le]
  refine ⟨C, hC, ?_⟩
  intro t ht ht1 f hf
  let W : Configuration n → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.exp (a * configurationOneNorm x))
  let F : Configuration n → ℝ≥0∞ := fun x => f x * W x
  let K : FusedConfiguration α → Configuration n → ℝ≥0∞ := fun z x =>
    ENNReal.ofReal (incomingKernel α t z x)
  let A : FusedConfiguration α → ℝ≥0∞ := fun z => ∫⁻ x, K z x * f x ∂volume
  let V : FusedConfiguration α → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (a * fusedOneNorm α z))
  let K₂ : FusedConfiguration α → Configuration n → ℝ≥0∞ := fun z x =>
    ENNReal.ofReal (incomingKernel α (2 * t) z x)
  let B₂ : ℝ≥0∞ := (ENNReal.ofReal (4 * Real.pi * (2 * t)))⁻¹
  let A₂ : FusedConfiguration α → ℝ≥0∞ := fun z => ∫⁻ x, K₂ z x * F x ∂volume
  let Dₑ : ℝ≥0∞ := ENNReal.ofReal D
  have ht2 : 0 < 2 * t := by positivity
  have hK : Measurable (Function.uncurry K) := by
    change Measurable (fun p : FusedConfiguration α × Configuration n =>
      ENNReal.ofReal (incomingKernel α t p.1 p.2))
    exact ((measurable_incomingKernel α).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hK₂ : Measurable (Function.uncurry K₂) := by
    change Measurable (fun p : FusedConfiguration α × Configuration n =>
      ENNReal.ofReal (incomingKernel α (2 * t) p.1 p.2))
    exact ((measurable_incomingKernel α).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hF : Measurable F := by
    dsimp [F, W]
    exact hf.mul ((measurable_const.mul measurable_configurationOneNorm).exp.ennreal_ofReal)
  have hA₂ : Measurable A₂ := measurable_kernelAction volume hK₂ hF
  have hrow (z : FusedConfiguration α) : (∫⁻ x, K₂ z x ∂volume) ≤ 1 := by
    simpa only [K₂] using (lintegral_incomingKernel_full α ht2 z).le
  have hB₂ : B₂ = ENNReal.ofReal ((8 * Real.pi * t)⁻¹) := by
    dsimp [B₂]
    rw [show 4 * Real.pi * (2 * t) = 8 * Real.pi * t by ring,
      ENNReal.ofReal_inv_of_pos (by positivity : 0 < 8 * Real.pi * t)]
  have hcol (x : Configuration n) : (∫⁻ z, K₂ z x ∂volume) ≤ B₂ := by
    calc
      _ ≤ ENNReal.ofReal ((8 * Real.pi * t)⁻¹) := by
        simpa only [K₂, show 4 * Real.pi * (2 * t) = 8 * Real.pi * t by ring] using
          lintegral_incomingKernel_fused_le α ht2 x
      _ = B₂ := hB₂.symm
  have hSchur := lintegral_kernel_lp_schur hK₂ hpq hrow hcol hF
  have hpointReal (z : FusedConfiguration α) (x : Configuration n) :
      incomingKernel α t z x * Real.exp (a * fusedOneNorm α z) ≤
        D * incomingKernel α (2 * t) z x * Real.exp (a * configurationOneNorm x) := by
    have hweight := incomingKernel_mul_exp_weight_le α ha ht z x
    calc
      incomingKernel α t z x * Real.exp (a * fusedOneNorm α z) =
          (incomingKernel α t z x *
            Real.exp (a * (fusedOneNorm α z - configurationOneNorm x))) *
            Real.exp (a * configurationOneNorm x) := by
              rw [mul_assoc, ← Real.exp_add]
              congr 2
              ring
      _ ≤ weightGrowth n a t * incomingKernel α (2 * t) z x *
            Real.exp (a * configurationOneNorm x) :=
          mul_le_mul_of_nonneg_right hweight (Real.exp_nonneg _)
      _ ≤ D * incomingKernel α (2 * t) z x * Real.exp (a * configurationOneNorm x) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hDgrowth ht ht1) (incomingKernel_pos α ht2 z x).le)
            (Real.exp_nonneg _)
  have hpoint (z : FusedConfiguration α) (x : Configuration n) :
      K z x * V z * f x ≤ Dₑ * (K₂ z x * F x) := by
    have hrealENN := ENNReal.ofReal_le_ofReal (hpointReal z x)
    have hkernelENN : K z x * V z ≤ Dₑ * (K₂ z x * W x) := by
      calc
        K z x * V z = ENNReal.ofReal
            (incomingKernel α t z x * Real.exp (a * fusedOneNorm α z)) := by
              dsimp [K, V]
              rw [ENNReal.ofReal_mul (incomingKernel_pos α ht z x).le]
        _ ≤ ENNReal.ofReal
            (D * incomingKernel α (2 * t) z x * Real.exp (a * configurationOneNorm x)) := hrealENN
        _ = Dₑ * (K₂ z x * W x) := by
              dsimp [Dₑ, K₂, W]
              rw [ENNReal.ofReal_mul (mul_nonneg hD.le (incomingKernel_pos α ht2 z x).le),
                ENNReal.ofReal_mul hD.le]
              ac_rfl
    calc
      _ ≤ (Dₑ * (K₂ z x * W x)) * f x := mul_le_mul' hkernelENN le_rfl
      _ = Dₑ * (K₂ z x * F x) := by dsimp [F, W]; ac_rfl
  have hAweighted (z : FusedConfiguration α) : A z * V z ≤ Dₑ * A₂ z := by
    have hKf : Measurable (fun x : Configuration n => K z x * f x) := by
      have hKz : Measurable (K z) := by
        change Measurable (fun x : Configuration n =>
          ENNReal.ofReal (incomingKernel α t z x))
        exact ((measurable_incomingKernel α).comp
          (measurable_const.prodMk (measurable_const.prodMk measurable_id))).ennreal_ofReal
      exact hKz.mul hf
    calc
      A z * V z = ∫⁻ x, K z x * f x * V z ∂volume := by
        dsimp [A]
        rw [lintegral_mul_const _ hKf]
      _ ≤ ∫⁻ x, Dₑ * (K₂ z x * F x) ∂volume := by
        apply lintegral_mono
        intro x
        calc
          K z x * f x * V z = K z x * V z * f x := by ac_rfl
          _ ≤ Dₑ * (K₂ z x * F x) := hpoint z x
      _ = Dₑ * A₂ z := by
        calc
          _ = ∫⁻ x, (K₂ z x * F x) * Dₑ ∂volume := by
            apply lintegral_congr
            intro x
            ac_rfl
          _ = A₂ z * Dₑ := by
            dsimp [A₂]
            rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
          _ = Dₑ * A₂ z := by rw [mul_comm]
  have hpow :
      (∫⁻ z, (A z * V z) ^ p ∂volume) ≤ Dₑ ^ p * (B₂ * ∫⁻ x, F x ^ p ∂volume) := by
    calc
      _ ≤ Dₑ ^ p * ∫⁻ z, A₂ z ^ p ∂volume := by
        calc
          _ ≤ ∫⁻ z, (Dₑ * A₂ z) ^ p ∂volume := by
            apply lintegral_mono
            intro z
            exact ENNReal.rpow_le_rpow (hAweighted z) (by positivity)
          _ = ∫⁻ z, Dₑ ^ p * A₂ z ^ p ∂volume := by
            apply lintegral_congr
            intro z
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ p)]
          _ = Dₑ ^ p * ∫⁻ z, A₂ z ^ p ∂volume :=
            lintegral_const_mul _ (hA₂.pow_const p)
      _ ≤ Dₑ ^ p * (B₂ * ∫⁻ x, F x ^ p ∂volume) :=
        mul_le_mul' le_rfl hSchur
  have hB₂root : B₂ ^ (1 / p) =
      ENNReal.ofReal ((8 * Real.pi) ^ ((-1 : ℝ) / p) * t ^ ((-1 : ℝ) / p)) := by
    rw [hB₂, ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ (8 * Real.pi * t)⁻¹)
      (by positivity)]
    congr 1
    rw [Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity : 0 ≤ 8 * Real.pi * t)]
    rw [Real.mul_rpow (by positivity) ht.le]
    congr 1 <;> ring
  have hroot :
      (∫⁻ z, (A z * V z) ^ p ∂volume) ^ (1 / p) ≤
        Dₑ * B₂ ^ (1 / p) * (∫⁻ x, F x ^ p ∂volume) ^ (1 / p) := by
    calc
      _ ≤ (Dₑ ^ p * (B₂ * ∫⁻ x, F x ^ p ∂volume)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hpow (by positivity)
      _ = Dₑ * B₂ ^ (1 / p) * (∫⁻ x, F x ^ p ∂volume) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ (1 / p : ℝ)),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ (1 / p : ℝ)),
          ← ENNReal.rpow_mul]
        have he : p * (1 / p) = 1 := by field_simp [ne_of_gt hp]
        rw [he, ENNReal.rpow_one]
        ac_rfl
  calc
    _ ≤ ENNReal.ofReal (C * t ^ ((-1 : ℝ) / p)) *
          (∫⁻ x, F x ^ p ∂volume) ^ (1 / p) := by
      calc
        _ ≤ Dₑ * B₂ ^ (1 / p) * (∫⁻ x, F x ^ p ∂volume) ^ (1 / p) := hroot
        _ = ENNReal.ofReal (C * t ^ ((-1 : ℝ) / p)) *
              (∫⁻ x, F x ^ p ∂volume) ^ (1 / p) := by
          rw [hB₂root]
          dsimp [C, Dₑ]
          calc
            _ = ENNReal.ofReal (D * ((8 * Real.pi) ^ ((-1 : ℝ) / p) *
                t ^ ((-1 : ℝ) / p))) * (∫⁻ x, F x ^ p ∂volume) ^ (1 / p) := by
                  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ D)]
            _ = ENNReal.ofReal (C * t ^ ((-1 : ℝ) / p)) *
                  (∫⁻ x, F x ^ p ∂volume) ^ (1 / p) := by
                  congr 1
                  dsimp [C]
                  ring_nf
    _ = _ := by rfl

/-- The incoming `L²` trace gives the large-time weighted `Lᵖ` to `L²` estimate. -/
theorem incomingL2_large {n : ℕ} (α : CollisionPair n) {p a : ℝ}
    (hp : 2 < p) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → ∀ f : Configuration n → ℝ≥0∞,
      Measurable f →
        (∫⁻ z : FusedConfiguration α,
          (∫⁻ x : Configuration n, ENNReal.ofReal (incomingKernel α t z x) * f x) ^ (2 : ℝ) ∂volume) ^
            (1 / 2 : ℝ) ≤
          ENNReal.ofReal (C * t ^ ((-1 : ℝ) / p)) *
            (∫⁻ x : Configuration n,
              (f x * ENNReal.ofReal (Real.exp (a * configurationOneNorm x))) ^ p ∂volume) ^ (1 / p) := by
  obtain ⟨cInput, hcInput, hInput⟩ := lintegral_sq_le_weighted (n := n) hp ha
  let C : ℝ := cInput * (4 * Real.pi) ^ ((-1 : ℝ) / 2)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t ht1 f hf
  let W : Configuration n → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.exp (a * configurationOneNorm x))
  let F : Configuration n → ℝ≥0∞ := fun x => f x * W x
  let K : FusedConfiguration α → Configuration n → ℝ≥0∞ := fun z x =>
    ENNReal.ofReal (incomingKernel α t z x)
  let A : FusedConfiguration α → ℝ≥0∞ := fun z => ∫⁻ x, K z x * f x ∂volume
  have hIn := hInput f hf
  have hInF : (∫⁻ x, f x ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal cInput * (∫⁻ x, F x ^ p ∂volume) ^ (1 / p) := by
    simpa [F, W] using hIn
  have hTrace := incomingKernel_l2_sq_le α (lt_of_lt_of_le (by norm_num) ht1) hf
  have hTrace' : (∫⁻ z, A z ^ (2 : ℝ) ∂volume) ≤
      ENNReal.ofReal ((4 * Real.pi * t)⁻¹) * ∫⁻ x, f x ^ (2 : ℝ) ∂volume := by
    convert hTrace using 1 <;> simp [A, K]
  have hRoot := ENNReal.rpow_le_rpow hTrace' (by norm_num : 0 ≤ (1 / 2 : ℝ))
  have hBroot : (ENNReal.ofReal ((4 * Real.pi * t)⁻¹)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal ((4 * Real.pi) ^ ((-1 : ℝ) / 2) * t ^ ((-1 : ℝ) / 2)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : 0 ≤ (4 * Real.pi * t)⁻¹)
      (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    congr 1
    rw [Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity : 0 ≤ 4 * Real.pi * t),
      Real.mul_rpow (by positivity) (le_trans (by norm_num : (0 : ℝ) ≤ 1) ht1)]
    congr 1 <;> ring
  have htPow : t ^ ((-1 : ℝ) / 2) ≤ t ^ ((-1 : ℝ) / p) := by
    apply Real.rpow_le_rpow_of_exponent_le ht1
    have hp0 : 0 < p := lt_trans (by norm_num : (0 : ℝ) < 2) hp
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hp0]
    nlinarith
  calc
    (∫⁻ z, A z ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) ≤
        (ENNReal.ofReal ((4 * Real.pi * t)⁻¹)) ^ (1 / 2 : ℝ) *
                (∫⁻ x, f x ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) := by
            calc
              _ ≤ ((ENNReal.ofReal ((4 * Real.pi * t)⁻¹)) *
                ∫⁻ x, f x ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) := hRoot
              _ = _ := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ ≤ ENNReal.ofReal ((4 * Real.pi) ^ ((-1 : ℝ) / 2) * t ^ ((-1 : ℝ) / p)) *
          (ENNReal.ofReal cInput * (∫⁻ x, F x ^ p ∂volume) ^ (1 / p)) := by
            rw [hBroot]
            exact mul_le_mul'
              (ENNReal.ofReal_le_ofReal
                (mul_le_mul_of_nonneg_left htPow (by positivity))) hInF
    _ = ENNReal.ofReal (C * t ^ ((-1 : ℝ) / p)) *
          (∫⁻ x, F x ^ p ∂volume) ^ (1 / p) := by
            calc
              _ = (ENNReal.ofReal cInput *
                    ENNReal.ofReal ((4 * Real.pi) ^ ((-1 : ℝ) / 2) *
                      t ^ ((-1 : ℝ) / p))) *
                    (∫⁻ x, F x ^ p ∂volume) ^ (1 / p) := by ac_rfl
              _ = ENNReal.ofReal (cInput * ((4 * Real.pi) ^ ((-1 : ℝ) / 2) *
                    t ^ ((-1 : ℝ) / p))) *
                    (∫⁻ x, F x ^ p ∂volume) ^ (1 / p) := by
                    rw [ENNReal.ofReal_mul hcInput.le]
              _ = _ := by
                    congr 1
                    dsimp [C]
                    ring_nf

/-- The incoming kernel has a weighted `Lᵖ → L²` form bound of order `t^{-1/p}`, as in Tsai (2024), equation (2.10e). -/
theorem weightedFormBound_incoming_to_L2 {n : ℕ} (α : CollisionPair n) {p a : ℝ}
    (hp : 2 < p) (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 < t →
      WeightedFormBound volume volume (fun _ => 0) (fun x => a * configurationOneNorm x) p 2
        (fun (z : FusedConfiguration α) (x : Configuration n) =>
          ENNReal.ofReal (incomingKernel α t z x)) (ENNReal.ofReal (c * t ^ (-1 / p))) := by
  let q : ℝ := p / (p - 1)
  have hp1 : 1 < p := by linarith
  have hq : 1 < q := by
    dsimp [q]
    rw [lt_div_iff₀ (by linarith : 0 < p - 1)]
    linarith
  have hpq : p.HolderConjugate q := (Real.holderConjugate_iff_eq_conjExponent hp1).2 rfl
  obtain ⟨cFuse, hcFuse, hFuse⟩ := lintegral_sq_le_weighted_fused α hp ha
  obtain ⟨cSmall, hcSmall, hSmall⟩ := incomingWeightedLp_small α hp1 ha.le
  obtain ⟨cLarge, hcLarge, hLarge⟩ := incomingL2_large α hp ha
  let c : ℝ := cFuse * cSmall + cLarge
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro t ht f g hf hg
  let W : Configuration n → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.exp (a * configurationOneNorm x))
  let F : Configuration n → ℝ≥0∞ := fun x => f x * W x
  let K : FusedConfiguration α → Configuration n → ℝ≥0∞ := fun z x =>
    ENNReal.ofReal (incomingKernel α t z x)
  let A : FusedConfiguration α → ℝ≥0∞ := fun z => ∫⁻ x, K z x * f x ∂volume
  have hN : Measurable (configurationOneNorm : Configuration n → ℝ) :=
    measurable_configurationOneNorm
  have hW : Measurable W := by
    dsimp [W]
    exact (measurable_const.mul hN).exp.ennreal_ofReal
  have hF : Measurable F := by dsimp [F]; exact hf.mul hW
  have hK : Measurable (Function.uncurry K) := by
    change Measurable (fun z : FusedConfiguration α × Configuration n =>
      ENNReal.ofReal (incomingKernel α t z.1 z.2))
    exact ((measurable_incomingKernel α).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hA : Measurable A := measurable_kernelAction volume hK hf
  have hHolder2 := ENNReal.lintegral_mul_le_Lp_mul_Lq volume
    (by rw [Real.holderConjugate_iff_eq_conjExponent (by norm_num : (1 : ℝ) < 2)])
    hA.aemeasurable hg.aemeasurable
  have hBilinear :
      (∫⁻ z, g z * A z ∂volume) ≤
        (∫⁻ z, A z ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) *
          (∫⁻ z, g z ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) := by
    have hHolder2' :
        (∫⁻ z, A z * g z ∂volume) ≤
          (∫⁻ z, A z ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) *
            (∫⁻ z, g z ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) := by
      simpa only [show (2 : ℝ) / (2 - 1) = 2 by norm_num,
        show (1 : ℝ) / (2 / (2 - 1)) = 1 / 2 by norm_num, Pi.mul_apply] using hHolder2
    calc
      _ = ∫⁻ z, A z * g z ∂volume := by
        apply lintegral_congr
        intro z
        rw [mul_comm]
      _ ≤ _ := hHolder2'
      _ = _ := by rw [mul_comm]
  have hL2 : (∫⁻ z, A z ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (c * t ^ ((-1 : ℝ) / p)) * (∫⁻ x, F x ^ p ∂volume) ^ (1 / p) := by
    by_cases htSmall : t ≤ 1
    · have hEmb := hFuse A hA
      have hLp := hSmall t ht htSmall f hf
      calc
        _ ≤ ENNReal.ofReal cFuse *
            (∫⁻ z, (A z * ENNReal.ofReal (Real.exp (a * fusedOneNorm α z))) ^ p ∂volume) ^ (1 / p) := hEmb
        _ ≤ ENNReal.ofReal cFuse *
            (ENNReal.ofReal (cSmall * t ^ ((-1 : ℝ) / p)) *
              (∫⁻ x, F x ^ p ∂volume) ^ (1 / p)) := by
                apply mul_le_mul' le_rfl ?_
                simpa [A, F, W, K, Real.exp_zero] using hLp
        _ = ENNReal.ofReal ((cFuse * cSmall) * t ^ ((-1 : ℝ) / p)) *
              (∫⁻ x, F x ^ p ∂volume) ^ (1 / p) := by
                calc
                  _ = (ENNReal.ofReal cFuse *
                      ENNReal.ofReal (cSmall * t ^ ((-1 : ℝ) / p))) *
                      (∫⁻ x, F x ^ p ∂volume) ^ (1 / p) := by ac_rfl
                  _ = ENNReal.ofReal (cFuse * (cSmall * t ^ ((-1 : ℝ) / p))) *
                      (∫⁻ x, F x ^ p ∂volume) ^ (1 / p) := by
                        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ cFuse)]
                  _ = _ := by congr 1; ring
        _ ≤ ENNReal.ofReal (c * t ^ ((-1 : ℝ) / p)) *
              (∫⁻ x, F x ^ p ∂volume) ^ (1 / p) := by
                apply mul_le_mul' ?_ le_rfl
                apply ENNReal.ofReal_le_ofReal
                apply mul_le_mul_of_nonneg_right
                · have hcoef : cFuse * cSmall ≤ c := by
                    dsimp [c]
                    nlinarith [mul_nonneg hcFuse.le hcSmall.le]
                  exact hcoef
                · positivity
    · have ht1 : 1 ≤ t := le_of_not_ge htSmall
      have hLg := hLarge t ht1 f hf
      calc
        _ ≤ ENNReal.ofReal (cLarge * t ^ ((-1 : ℝ) / p)) *
              (∫⁻ x, F x ^ p ∂volume) ^ (1 / p) := by
                simpa [A, F, W, K, Real.exp_zero] using hLg
        _ ≤ ENNReal.ofReal (c * t ^ ((-1 : ℝ) / p)) *
              (∫⁻ x, F x ^ p ∂volume) ^ (1 / p) := by
                apply mul_le_mul' ?_ le_rfl
                apply ENNReal.ofReal_le_ofReal
                apply mul_le_mul_of_nonneg_right
                · have hcoef : cLarge ≤ c := by
                    dsimp [c]
                    nlinarith [mul_nonneg hcFuse.le hcSmall.le]
                  exact hcoef
                · positivity
  have hresult :
      (∫⁻ z, g z * A z ∂volume) ≤
        ENNReal.ofReal (c * t ^ ((-1 : ℝ) / p)) *
          (∫⁻ x, F x ^ p ∂volume) ^ (1 / p) *
          (∫⁻ z, g z ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ (∫⁻ z, A z ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) *
          (∫⁻ z, g z ^ (2 : ℝ) ∂volume) ^ (1 / 2 : ℝ) := hBilinear
      _ ≤ _ := mul_le_mul' hL2 le_rfl
  simpa [WeightedFormBound, A, F, W, Real.exp_zero, mul_assoc] using hresult

end Critical2DKPZ.SHF.Tsai

end
