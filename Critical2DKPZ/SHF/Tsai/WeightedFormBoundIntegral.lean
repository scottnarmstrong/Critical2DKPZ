/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.WeightedFormBound
public import Critical2DKPZ.SHF.DeltaBose.KernelCompositionL2
import Critical2DKPZ.SHF.Tsai.Tech
import Mathlib.MeasureTheory.Integral.Prod

/-! # Integration of weighted positive kernel bounds -/

@[expose] public section

open MeasureTheory Set Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Integrating a measurable family of positive kernels integrates its weighted bilinear bound. -/
theorem WeightedFormBound.lintegral_param {T X Y : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [MeasurableSpace Y]
    {κ : Measure T} {μ : Measure X} {ν : Measure Y}
    [SigmaFinite κ] [SFinite μ] [SigmaFinite ν]
    {wX : X → ℝ} {wY : Y → ℝ} {p p' : ℝ}
    {K : T → X → Y → ℝ≥0∞} {c : T → ℝ≥0∞}
    (hKm : Measurable (fun q : T × X × Y => K q.1 q.2.1 q.2.2))
    (hcm : Measurable c)
    (hbound : ∀ t, WeightedFormBound μ ν wX wY p p' (K t) (c t)) :
    WeightedFormBound μ ν wX wY p p'
      (fun x y => ∫⁻ t, K t x y ∂κ) (∫⁻ t, c t ∂κ) := by
  intro f g hf hg
  let NF : ℝ≥0∞ :=
    (∫⁻ y, (f y * ENNReal.ofReal (Real.exp (wY y))) ^ p ∂ν) ^ (1 / p : ℝ)
  let NG : ℝ≥0∞ :=
    (∫⁻ x, (g x * ENNReal.ofReal (Real.exp (wX x))) ^ p' ∂μ) ^ (1 / p' : ℝ)
  have hKprod : Measurable (fun q : (T × X) × Y => K q.1.1 q.1.2 q.2) := by
    exact hKm.comp (measurable_fst.fst.prodMk
      (measurable_fst.snd.prodMk measurable_snd))
  have hAct : Measurable (fun q : T × X =>
      ∫⁻ y, K q.1 q.2 y * f y ∂ν) := by
    exact (hKprod.mul (hf.comp measurable_snd)).lintegral_prod_right'
  have hInner (x : X) :
      (∫⁻ y, (∫⁻ t, K t x y ∂κ) * f y ∂ν) =
        ∫⁻ t, (∫⁻ y, K t x y * f y ∂ν) ∂κ := by
    have hKsec (y : Y) : Measurable (fun t : T => K t x y) :=
      hKm.comp (measurable_id.prodMk (measurable_const.prodMk measurable_const))
    have hF : Measurable (fun q : Y × T => K q.2 x q.1 * f q.1) := by
      exact (hKm.comp (measurable_snd.prodMk
        (measurable_const.prodMk measurable_fst))).mul (hf.comp measurable_fst)
    calc
      _ = ∫⁻ y, ∫⁻ t, K t x y * f y ∂κ ∂ν := by
            apply lintegral_congr
            intro y
            exact (lintegral_mul_const (f y) (hKsec y)).symm
      _ = _ := lintegral_lintegral_swap hF.aemeasurable
  have hOuter (x : X) : Measurable (fun t : T => ∫⁻ y, K t x y * f y ∂ν) :=
    hAct.comp (measurable_id.prodMk measurable_const)
  have hSwapMeas : Measurable (Function.uncurry (fun x t : _ => g x *
      (∫⁻ y, K t x y * f y ∂ν))) := by
    change Measurable (fun q : X × T => g q.1 *
      (∫⁻ y, K q.2 q.1 y * f y ∂ν))
    exact (hg.comp measurable_fst).mul
      (hAct.comp (measurable_snd.prodMk measurable_fst))
  calc
    (∫⁻ x, g x * (∫⁻ y, (∫⁻ t, K t x y ∂κ) * f y ∂ν) ∂μ) =
        ∫⁻ t, (∫⁻ x, g x * (∫⁻ y, K t x y * f y ∂ν) ∂μ) ∂κ := by
          have hSwap := lintegral_lintegral_swap (μ := μ) (ν := κ)
            hSwapMeas.aemeasurable
          calc
            _ = ∫⁻ x, ∫⁻ t, g x *
                  (∫⁻ y, K t x y * f y ∂ν) ∂κ ∂μ := by
                    apply lintegral_congr
                    intro x
                    rw [hInner x]
                    exact (lintegral_const_mul (g x) (hOuter x)).symm
            _ = _ := hSwap
    _ ≤ ∫⁻ t, c t * NF * NG ∂κ := by
          apply lintegral_mono
          intro t
          simpa [WeightedFormBound, NF, NG] using hbound t f g hf hg
    _ = (∫⁻ t, c t ∂κ) * NF * NG := by
          calc
            _ = ∫⁻ t, (NF * NG) * c t ∂κ := by
                  apply lintegral_congr
                  intro t
                  ac_rfl
            _ = (NF * NG) * (∫⁻ t, c t ∂κ) := lintegral_const_mul _ hcm
            _ = _ := by ac_rfl

/-- Integrating a measurable family of kernel compositions gives a weighted bilinear bound whose constant is the integral of the products of the two form constants. -/
theorem WeightedFormBound.lintegral_comp_param {T X Y Z : Type*}
    [MeasurableSpace T] [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {κ : Measure T} {μ : Measure X} {ν : Measure Y} {ρ : Measure Z}
    [SigmaFinite κ] [SFinite μ] [SigmaFinite ν] [SigmaFinite ρ]
    {wX : X → ℝ} {wZ : Z → ℝ} {p p' : ℝ}
    {K : T → X → Y → ℝ≥0∞} {L : T → Y → Z → ℝ≥0∞}
    {c d : T → ℝ≥0∞}
    (hKm : Measurable (fun q : T × X × Y => K q.1 q.2.1 q.2.2))
    (hLm : Measurable (fun q : T × Y × Z => L q.1 q.2.1 q.2.2))
    (hcm : Measurable c) (hdm : Measurable d)
    (hK : ∀ t, WeightedFormBound μ ν wX (fun _ => 0) 2 p' (K t) (c t))
    (hL : ∀ t, WeightedFormBound ν ρ (fun _ => 0) wZ p 2 (L t) (d t)) :
    WeightedFormBound μ ρ wX wZ p p'
      (fun x z => ∫⁻ t, spatialKernelComp ν (K t) (L t) x z ∂κ)
      (∫⁻ t, c t * d t ∂κ) := by
  let M : T → X → Z → ℝ≥0∞ := fun t x z => spatialKernelComp ν (K t) (L t) x z
  let e : T → ℝ≥0∞ := fun t => c t * d t
  have hKfam : Measurable (Function.uncurry (fun q : T × X => K q.1 q.2)) := by
    change Measurable (fun q : (T × X) × Y => K q.1.1 q.1.2 q.2)
    exact hKm.comp (measurable_fst.fst.prodMk
      (measurable_fst.snd.prodMk measurable_snd))
  have hLfam : Measurable (Function.uncurry
      (fun y : Y => fun q : T × Z => L q.1 y q.2)) := by
    change Measurable (fun q : Y × (T × Z) => L q.2.1 q.1 q.2.2)
    exact hLm.comp (measurable_snd.fst.prodMk
      (measurable_fst.prodMk measurable_snd.snd))
  have hM : Measurable (fun q : T × X × Z => M q.1 q.2.1 q.2.2) := by
    change Measurable (fun q : T × X × Z =>
      spatialKernelComp ν (K q.1) (L q.1) q.2.1 q.2.2)
    have hcomp := measurable_spatialKernelComp ν hKfam hLfam
    exact hcomp.comp ((measurable_fst.prodMk measurable_snd.fst).prodMk
      (measurable_fst.prodMk measurable_snd.snd))
  have hem : Measurable e := hcm.mul hdm
  have hKsection (t : T) : Measurable (Function.uncurry (K t)) := by
    change Measurable (fun q : X × Y => K t q.1 q.2)
    have hargs : Measurable (fun q : X × Y => (t, q.1, q.2)) := by fun_prop
    exact hKm.comp hargs
  have hLsection (t : T) : Measurable (Function.uncurry (L t)) := by
    change Measurable (fun q : Y × Z => L t q.1 q.2)
    have hargs : Measurable (fun q : Y × Z => (t, q.1, q.2)) := by fun_prop
    exact hLm.comp hargs
  have hBound (t : T) :
      WeightedFormBound μ ρ wX wZ p p' (M t) (e t) := by
    simpa [M, e] using WeightedFormBound.comp_two
      (hKsection t) (hLsection t) (hK t) (hL t)
  simpa only [M, e] using
    (WeightedFormBound.lintegral_param (κ := κ) (μ := μ) (ν := ρ)
      (K := M) (c := e) hM hem hBound)

/-- Integrating a weighted bilinear kernel composition with two integrable endpoint powers gives the Beta-function constant and integrability of the scalar majorant. -/
theorem WeightedFormBound.lintegral_comp_beta {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    {μ : Measure X} {ν : Measure Y} {ρ : Measure Z}
    [SFinite μ] [SigmaFinite ν] [SigmaFinite ρ]
    {wX : X → ℝ} {wZ : Z → ℝ} {p p' : ℝ}
    {H : ℝ → X → Y → ℝ≥0∞} {L : ℝ → Y → Z → ℝ≥0∞}
    (t c d b b' : ℝ) (ht : 0 < t) (hc : 0 < c) (hd : 0 < d)
    (hb : -1 < b) (hb' : -1 < b')
    (hHm : Measurable (fun q : ℝ × X × Y => H q.1 q.2.1 q.2.2))
    (hLm : Measurable (fun q : ℝ × Y × Z => L q.1 q.2.1 q.2.2))
    (hH : ∀ s ∈ Ioo (0 : ℝ) t,
      WeightedFormBound μ ν wX (fun _ => 0) 2 p' (H s)
        (ENNReal.ofReal (c * s ^ b)))
    (hL : ∀ s ∈ Ioo (0 : ℝ) t,
      WeightedFormBound ν ρ (fun _ => 0) wZ p 2 (L s)
        (ENNReal.ofReal (d * s ^ b'))) :
    IntegrableOn (fun s : ℝ => c * d * s ^ b * (t - s) ^ b') (Ioo 0 t) ∧
      WeightedFormBound μ ρ wX wZ p p'
        (fun x z => ∫⁻ s in Ioo (0 : ℝ) t,
          spatialKernelComp ν (H s) (L (t - s)) x z)
        (ENNReal.ofReal (c * d * t ^ (b + b' + 1) *
          (Real.Gamma (b + 1) * Real.Gamma (b' + 1) /
            Real.Gamma (b + b' + 2)))) := by
  let K : ℝ → X → Y → ℝ≥0∞ := fun s x y =>
    if s ∈ Ioo (0 : ℝ) t then H s x y else 0
  let M : ℝ → Y → Z → ℝ≥0∞ := fun s y z =>
    if s ∈ Ioo (0 : ℝ) t then L (t - s) y z else 0
  let cK : ℝ → ℝ≥0∞ := fun s =>
    if s ∈ Ioo (0 : ℝ) t then ENNReal.ofReal (c * s ^ b) else 0
  let cL : ℝ → ℝ≥0∞ := fun s =>
    if s ∈ Ioo (0 : ℝ) t then ENNReal.ofReal (d * (t - s) ^ b') else 0
  have hset : MeasurableSet (Ioo (0 : ℝ) t) := measurableSet_Ioo
  have hKmeas : Measurable (fun q : ℝ × X × Y => K q.1 q.2.1 q.2.2) := by
    change Measurable (fun q : ℝ × X × Y =>
      if q.1 ∈ Ioo (0 : ℝ) t then H q.1 q.2.1 q.2.2 else 0)
    exact Measurable.ite (hset.preimage measurable_fst) hHm measurable_const
  have hLtime : Measurable (fun q : ℝ × Y × Z =>
      L (t - q.1) q.2.1 q.2.2) := by
    have hargs : Measurable (fun q : ℝ × Y × Z => (t - q.1, q.2.1, q.2.2)) := by
      fun_prop
    exact hLm.comp hargs
  have hMmeas : Measurable (fun q : ℝ × Y × Z => M q.1 q.2.1 q.2.2) := by
    change Measurable (fun q : ℝ × Y × Z =>
      if q.1 ∈ Ioo (0 : ℝ) t then L (t - q.1) q.2.1 q.2.2 else 0)
    exact Measurable.ite (hset.preimage measurable_fst) hLtime measurable_const
  have hpK : Measurable (fun s : ℝ => s ^ b) := by
    have hargs : Measurable (fun s : ℝ => (s, b)) := by fun_prop
    exact measurable_real_rpow.comp hargs
  have hpL : Measurable (fun s : ℝ => (t - s) ^ b') := by
    have hargs : Measurable (fun s : ℝ => (t - s, b')) := by fun_prop
    exact measurable_real_rpow.comp hargs
  have hcKm : Measurable cK := by
    apply Measurable.ite hset
    · exact (measurable_const.mul hpK).ennreal_ofReal
    · exact measurable_const
  have hcLm : Measurable cL := by
    apply Measurable.ite hset
    · exact (measurable_const.mul hpL).ennreal_ofReal
    · exact measurable_const
  have hKbound (s : ℝ) :
      WeightedFormBound μ ν wX (fun _ => 0) 2 p' (K s) (cK s) := by
    by_cases hs : s ∈ Ioo (0 : ℝ) t
    · have hKeq : K s = H s := by
        funext x y
        change (if s ∈ Ioo (0 : ℝ) t then H s x y else 0) = H s x y
        rw [ite_eq_left hs]
      have hcKeq : cK s = ENNReal.ofReal (c * s ^ b) := by
        change (if s ∈ Ioo (0 : ℝ) t then ENNReal.ofReal (c * s ^ b) else 0) = _
        rw [ite_eq_left hs]
      rw [hKeq, hcKeq]
      exact hH s hs
    · have hKzero : K s = fun _ _ => 0 := by
        funext x y
        change (if s ∈ Ioo (0 : ℝ) t then H s x y else 0) = 0
        rw [ite_eq_right hs]
      have hcKzero : cK s = 0 := by
        change (if s ∈ Ioo (0 : ℝ) t then ENNReal.ofReal (c * s ^ b) else 0) = 0
        rw [ite_eq_right hs]
      simp [WeightedFormBound, hKzero, hcKzero]
  have hMbound (s : ℝ) :
      WeightedFormBound ν ρ (fun _ => 0) wZ p 2 (M s) (cL s) := by
    by_cases hs : s ∈ Ioo (0 : ℝ) t
    · have hs' : 0 < s ∧ s < t := by simpa only [mem_Ioo] using hs
      have hr0 : 0 < t - s := by linarith [hs'.2]
      have hrt : t - s < t := by linarith [hs'.1]
      have hr : t - s ∈ Ioo (0 : ℝ) t := by
        change 0 < t - s ∧ t - s < t
        exact ⟨hr0, hrt⟩
      have hMeq : M s = L (t - s) := by
        funext y z
        change (if s ∈ Ioo (0 : ℝ) t then L (t - s) y z else 0) = L (t - s) y z
        rw [ite_eq_left hs]
      have hcLeq : cL s = ENNReal.ofReal (d * (t - s) ^ b') := by
        change (if s ∈ Ioo (0 : ℝ) t then ENNReal.ofReal (d * (t - s) ^ b') else 0) = _
        rw [ite_eq_left hs]
      rw [hMeq, hcLeq]
      exact hL (t - s) hr
    · have hMzero : M s = fun _ _ => 0 := by
        funext y z
        change (if s ∈ Ioo (0 : ℝ) t then L (t - s) y z else 0) = 0
        rw [ite_eq_right hs]
      have hcLzero : cL s = 0 := by
        change (if s ∈ Ioo (0 : ℝ) t then ENNReal.ofReal (d * (t - s) ^ b') else 0) = 0
        rw [ite_eq_right hs]
      simp [WeightedFormBound, hMzero, hcLzero]
  have hcomp := WeightedFormBound.lintegral_comp_param
    (κ := volume) (μ := μ) (ν := ν) (ρ := ρ)
    (K := K) (L := M) (c := cK) (d := cL)
    hKmeas hMmeas hcKm hcLm hKbound hMbound
  have hkernel :
      (fun x z => ∫⁻ s, spatialKernelComp ν (K s) (M s) x z) =
        (fun x z => ∫⁻ s in Ioo (0 : ℝ) t,
          spatialKernelComp ν (H s) (L (t - s)) x z) := by
    funext x z
    rw [← lintegral_indicator hset]
    apply lintegral_congr
    intro s
    by_cases hs : s ∈ Ioo (0 : ℝ) t
    · rw [Set.indicator_of_mem hs]
      have hKeq : K s = H s := by
        funext x y
        change (if s ∈ Ioo (0 : ℝ) t then H s x y else 0) = H s x y
        rw [ite_eq_left hs]
      have hMeq : M s = L (t - s) := by
        funext y z
        change (if s ∈ Ioo (0 : ℝ) t then L (t - s) y z else 0) = L (t - s) y z
        rw [ite_eq_left hs]
      rw [hKeq, hMeq]
    · rw [Set.indicator_of_notMem hs]
      have hKzero : K s = fun _ _ => 0 := by
        funext x y
        change (if s ∈ Ioo (0 : ℝ) t then H s x y else 0) = 0
        rw [ite_eq_right hs]
      have hMzero : M s = fun _ _ => 0 := by
        funext y z
        change (if s ∈ Ioo (0 : ℝ) t then L (t - s) y z else 0) = 0
        rw [ite_eq_right hs]
      simp [hKzero, hMzero, spatialKernelComp]
  have hscalarInt :
      IntegrableOn (fun s : ℝ => c * d * (s ^ b * (t - s) ^ b')) (Ioo 0 t) := by
    change Integrable (fun s : ℝ => c * d * (s ^ b * (t - s) ^ b'))
      (volume.restrict (Ioo 0 t))
    simpa only [mul_assoc] using
      (integrableOn_rpow_mul_rpow_sub ht hb hb').const_mul (c * d)
  have hscalarNonneg : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) t)]
      (fun s : ℝ => c * d * (s ^ b * (t - s) ^ b')) := by
    filter_upwards [ae_restrict_mem hset] with s hs
    exact mul_nonneg (mul_nonneg hc.le hd.le)
      (mul_nonneg (Real.rpow_nonneg hs.1.le b)
        (Real.rpow_nonneg (sub_nonneg.mpr hs.2.le) b'))
  have hcoefficient :
      (∫⁻ s, cK s * cL s) = ENNReal.ofReal
        (c * d * t ^ (b + b' + 1) *
          (Real.Gamma (b + 1) * Real.Gamma (b' + 1) /
            Real.Gamma (b + b' + 2))) := by
    have hpointwise (s : ℝ) : cK s * cL s =
        (Ioo (0 : ℝ) t).indicator
          (fun r : ℝ => ENNReal.ofReal (c * d * (r ^ b * (t - r) ^ b'))) s := by
      by_cases hs : s ∈ Ioo (0 : ℝ) t
      · have hs' : 0 < s ∧ s < t := by simpa only [mem_Ioo] using hs
        have hleft : 0 ≤ c * s ^ b := mul_nonneg hc.le (Real.rpow_nonneg hs'.1.le b)
        have hright : 0 ≤ d * (t - s) ^ b' :=
          mul_nonneg hd.le (Real.rpow_nonneg (sub_nonneg.mpr hs'.2.le) b')
        simp only [cK, cL, ite_eq_left hs, Set.indicator_of_mem hs]
        rw [← ENNReal.ofReal_mul hleft]
        congr 1
        ring
      · simp only [cK, cL, ite_eq_right hs, Set.indicator_of_notMem hs]
        norm_num
    calc
      _ = ∫⁻ s, (Ioo (0 : ℝ) t).indicator
            (fun r : ℝ => ENNReal.ofReal (c * d * (r ^ b * (t - r) ^ b'))) s := by
          apply lintegral_congr
          exact hpointwise
      _ = ∫⁻ s in Ioo (0 : ℝ) t,
            ENNReal.ofReal (c * d * (s ^ b * (t - s) ^ b')) := by
              rw [lintegral_indicator hset]
    calc
      _ = ENNReal.ofReal
          (∫ s in Ioo (0 : ℝ) t, c * d * (s ^ b * (t - s) ^ b')) :=
            (ofReal_integral_eq_lintegral_ofReal hscalarInt hscalarNonneg).symm
      _ = _ := by
            rw [integral_const_mul, integral_rpow_mul_rpow_sub_eq t ht hb hb']
            congr 1
            ring
  have hfinal : WeightedFormBound μ ρ wX wZ p p'
      (fun x z => ∫⁻ s in Ioo (0 : ℝ) t,
        spatialKernelComp ν (H s) (L (t - s)) x z)
      (ENNReal.ofReal
        (c * d * t ^ (b + b' + 1) *
          (Real.Gamma (b + 1) * Real.Gamma (b' + 1) /
            Real.Gamma (b + b' + 2)))) := by
    have h := WeightedFormBound.mono hcomp
      (by intro x z; exact le_of_eq (congrFun (congrFun hkernel.symm x) z))
      (le_of_eq hcoefficient)
    exact h
  exact ⟨by simpa [mul_assoc] using hscalarInt, hfinal⟩

end Critical2DKPZ.SHF.Tsai

end
