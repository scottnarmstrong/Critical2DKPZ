/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.WeightedConvolution
public import Critical2DKPZ.Analysis.Sobolev.Localization
public import Critical2DKPZ.Analysis.Sobolev.FourierProduct
import Critical2DKPZ.Analysis.Sobolev.Rellich.FrozenNorm
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Pointwise representatives of weighted frequency translates

The Bochner-valued convolution argument needs a representative of a translated weighted
Fourier class that agrees almost everywhere with its scalar formula.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform InnerProductSpace SchwartzMap

namespace Critical2DKPZ.Analysis.Sobolev

/-- Translation of an `L²` class has the expected pointwise representative almost everywhere. -/
theorem translateL2_ae_eq_sub (η : Plane) (f : Lp ℂ 2 (volume : Measure Plane)) :
    translateL2 η f =ᵐ[volume] fun ξ : Plane => f (ξ - η) := by
  filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_l2TranslationMap η)]
    with ξ hξ
  simpa [translateL2, l2TranslationMap] using hξ

/-- The weighted translation operator has the scalar representative obtained by multiplying the
ordinary translated representative by the ratio of the two Sobolev weights. -/
theorem weightedTranslateL2_ae_eq (a : ℝ) (ha : 0 ≤ a) (η : Plane)
    (f : Lp ℂ 2 (volume : Measure Plane)) :
    weightedTranslateL2 ha η f =ᵐ[volume]
      fun ξ : Plane => (negSobolevTranslationMultiplier a η ξ : ℂ) * f (ξ - η) := by
  filter_upwards [
    MemLp.coeFn_toLp (memLp_weightedMultiplierL2 ha η (translateL2 η f)),
    translateL2_ae_eq_sub η f] with ξ hmul htranslate
  calc
    weightedTranslateL2 ha η f ξ = weightedMultiplierL2 ha η (translateL2 η f) ξ := rfl
    _ = (negSobolevTranslationMultiplier a η ξ : ℂ) * translateL2 η f ξ := hmul
    _ = (negSobolevTranslationMultiplier a η ξ : ℂ) * f (ξ - η) := by rw [htranslate]

/-- A Bochner integral of `L²` classes has the expected scalar set integral whenever its
pointwise representatives agree with a product-integrable scalar family. -/
theorem setIntegral_integrableLpFamily_eq_scalar
    (F : Plane → Lp ℂ 2 (volume : Measure Plane)) (hF : Integrable F)
    (s : Set Plane) (hs : MeasurableSet s) (hμs : volume s ≠ ∞)
    (H : Plane × Plane → ℂ)
    (hH : Integrable H (volume.prod (volume.restrict s)))
    (hrep : ∀ η : Plane, F η =ᵐ[volume] fun ξ => H (η, ξ)) :
    (∫ ξ in s, (∫ η : Plane, F η) ξ) =
      (∫ ξ in s, ∫ η : Plane, H (η, ξ)) := by
  let I : Lp ℂ 2 (volume : Measure Plane) :=
    indicatorConstLp 2 hs hμs (1 : ℂ)
  let L : Lp ℂ 2 (volume : Measure Plane) →L[ℂ] ℂ := innerSL ℂ I
  have hpair : (∫ η : Plane, L (F η)) = L (∫ η : Plane, F η) :=
    L.integral_comp_comm hF
  have hI (g : Lp ℂ 2 (volume : Measure Plane)) :
      L g = ∫ ξ in s, g ξ := by
    simpa [L, innerSL_apply_apply] using
      L2.inner_indicatorConstLp_one hs hμs g
  have hset (η : Plane) :
      (∫ ξ in s, H (η, ξ)) = L (F η) := by
    rw [hI]
    have hslice :
        (fun ξ => H (η, ξ)) =ᵐ[volume] fun ξ => F η ξ := by
      filter_upwards [hrep η] with ξ hξ
      exact hξ.symm
    exact setIntegral_congr_ae hs (hslice.mono fun ξ hξ _ => hξ)
  have hdouble :
      (∫ ξ in s, (∫ η : Plane, F η) ξ) =
        (∫ η : Plane, ∫ ξ in s, H (η, ξ)) := by
    calc
      (∫ ξ in s, (∫ η : Plane, F η) ξ) = L (∫ η : Plane, F η) := by
        exact (hI (∫ η : Plane, F η)).symm
      _ = ∫ η : Plane, L (F η) := hpair.symm
      _ = ∫ η : Plane, ∫ ξ in s, H (η, ξ) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun η => (hset η).symm
  calc
    (∫ ξ in s, (∫ η : Plane, F η) ξ) =
        (∫ η : Plane, ∫ ξ in s, H (η, ξ)) := hdouble
    _ = (∫ ξ in s, ∫ η : Plane, H (η, ξ)) := by
      have hProd : Integrable (Function.uncurry (fun η ξ => H (η, ξ)))
          (volume.prod (volume.restrict s)) := by
        convert hH using 1
        funext z
        cases z
        rfl
      simpa using
        (integral_integral_swap (f := fun η ξ => H (η, ξ)) hProd)

/-- The integral of an `L²`-valued translation family over a finite-measure set agrees with the
scalar convolution integral whenever the scalar representatives are integrable on the product.
The product-integrability premise is the Fubini condition. -/
theorem setIntegral_l2ConvolutionAction_eq_scalar
    (k : Plane → ℂ) (hk : Integrable k) (hkc : Continuous k)
    (f : Lp ℂ 2 (volume : Measure Plane)) (s : Set Plane)
    (hs : MeasurableSet s) (hμs : volume s ≠ ∞)
    (H : Plane × Plane → ℂ)
    (hH : Integrable H (volume.prod (volume.restrict s)))
    (hrep : ∀ η : Plane,
      (fun ξ => k η • translateL2 η f ξ) =ᵐ[volume] fun ξ => H (η, ξ)) :
    (∫ ξ in s, l2ConvolutionAction k f ξ) =
      (∫ ξ in s, ∫ η : Plane, H (η, ξ)) := by
  let I : Lp ℂ 2 (volume : Measure Plane) :=
    indicatorConstLp 2 hs hμs (1 : ℂ)
  let L : Lp ℂ 2 (volume : Measure Plane) →L[ℂ] ℂ := innerSL ℂ I
  let F : Plane → Lp ℂ 2 (volume : Measure Plane) :=
    fun η => k η • translateL2 η f
  have hF : Integrable F (volume : Measure Plane) := by
    have hbound := norm_l2ConvolutionAction_le hk hkc f
    exact hbound.1
  have hpair : (∫ η : Plane, L (F η)) = L (∫ η : Plane, F η) :=
    L.integral_comp_comm hF
  have hI (g : Lp ℂ 2 (volume : Measure Plane)) :
      L g = ∫ ξ in s, g ξ := by
    simpa [L, innerSL_apply_apply] using
      L2.inner_indicatorConstLp_one hs hμs g
  have hset (η : Plane) :
      (∫ ξ in s, H (η, ξ)) = L (F η) := by
    rw [hI]
    have hslice :
        (fun ξ => H (η, ξ)) =ᵐ[volume] fun ξ => F η ξ := by
      filter_upwards [hrep η, Lp.coeFn_smul (k η) (translateL2 η f)] with ξ hξ hsmul
      exact hξ.symm.trans hsmul.symm
    exact setIntegral_congr_ae hs (hslice.mono fun ξ hξ _ => hξ)
  have hdouble :
      (∫ ξ in s, l2ConvolutionAction k f ξ) =
        (∫ η : Plane, ∫ ξ in s, H (η, ξ)) := by
    calc
      (∫ ξ in s, l2ConvolutionAction k f ξ) = L (l2ConvolutionAction k f) := by
        exact (hI (l2ConvolutionAction k f)).symm
      _ = L (∫ η : Plane, F η) := by rfl
      _ = ∫ η : Plane, L (F η) := hpair.symm
      _ = ∫ η : Plane, ∫ ξ in s, H (η, ξ) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun η => (hset η).symm
  calc
      (∫ ξ in s, l2ConvolutionAction k f ξ) =
        (∫ η : Plane, ∫ ξ in s, H (η, ξ)) := hdouble
    _ = (∫ ξ in s, ∫ η : Plane, H (η, ξ)) := by
      have hProd : Integrable (Function.uncurry (fun η ξ => H (η, ξ)))
          (volume.prod (volume.restrict s)) := by
        convert hH using 1
        funext z
        cases z
        rfl
      simpa using
        (integral_integral_swap (f := fun η ξ => H (η, ξ)) hProd)

/-- Convolving a continuous square-integrable input with an integrable continuous kernel gives a product-integrable family on every finite-measure spatial set. -/
theorem integrable_scalarShiftProduct_on_finiteSet
    (k : Plane → ℂ) (hk : Integrable k) (hkc : Continuous k)
    (κ : Plane → Plane) (hκc : Continuous κ)
    (u : Plane → ℂ) (huC : Continuous u) (huLp : MemLp u 2 (volume : Measure Plane))
    (s : Set Plane) (hμs : volume s ≠ ∞) :
    Integrable (fun p : Plane × Plane => k p.1 * u (p.2 - κ p.1))
      (volume.prod (volume.restrict s)) := by
  let ν : Measure Plane := volume.restrict s
  have hνfinite : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    change (volume.restrict s) Set.univ < ∞
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr hμs
  have : IsFiniteMeasure ν := hνfinite
  let H : Plane × Plane → ℂ := fun p => k p.1 * u (p.2 - κ p.1)
  have hshiftMap : Continuous (fun p : Plane × Plane => p.2 - κ p.1) :=
    continuous_snd.sub (hκc.comp continuous_fst)
  have hHc : Continuous H := by
    dsimp [H]
    exact (hkc.comp continuous_fst).mul (huC.comp hshiftMap)
  have hHsm : AEStronglyMeasurable H (volume.prod ν) := hHc.aestronglyMeasurable
  have hOne : MemLp (fun _ : Plane => (1 : ℂ)) (2 : ENNReal) ν := memLp_const (1 : ℂ)
  have hOne' : MemLp (fun _ : Plane => (1 : ℂ)) (ENNReal.ofReal (2 : ℝ)) ν := by
    simpa using hOne
  let C : ℝ := ENNReal.toReal (eLpNorm u 2 (volume : Measure Plane)) *
    ENNReal.toReal (eLpNorm (fun _ : Plane => (1 : ℂ)) 2 ν)
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hshiftMem (η : Plane) :
      MemLp (fun ξ : Plane => u (ξ - κ η)) 2 (volume : Measure Plane) := by
    change MemLp (u ∘ l2TranslationMap (κ η)) 2 (volume : Measure Plane)
    exact huLp.comp_measurePreserving (measurePreserving_l2TranslationMap (κ η))
  have hshiftRestrict (η : Plane) :
      MemLp (fun ξ : Plane => u (ξ - κ η)) 2 ν := by
    exact (hshiftMem η).mono_measure Measure.restrict_le_self
  have hshiftRestrict' (η : Plane) :
      MemLp (fun ξ : Plane => u (ξ - κ η)) (ENNReal.ofReal (2 : ℝ)) ν := by
    simpa using hshiftRestrict η
  /- Companion integrability fact for the slice integral bound below. -/
  have hshiftNormIntegrable (η : Plane) :
      Integrable (fun ξ : Plane => ‖u (ξ - κ η)‖) ν := by
    have hshiftL1 : MemLp (fun ξ : Plane => u (ξ - κ η)) 1 ν :=
      (hshiftRestrict η).mono_exponent (by norm_num)
    exact (memLp_one_iff_integrable.mp hshiftL1).norm
  have hHolderBound (η : Plane) :
      (∫ ξ : Plane, ‖u (ξ - κ η)‖ ∂ν) ≤ C := by
    have hHolder := integral_mul_norm_le_Lp_mul_Lq
      (E := ℂ) (p := 2) (q := 2) Real.HolderConjugate.two_two
      (hshiftRestrict' η) hOne'
    have hshiftPow :
        (∫ ξ : Plane, ‖u (ξ - κ η)‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂ν) ^
            (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ =
          ENNReal.toReal (eLpNorm (fun ξ : Plane => u (ξ - κ η)) 2 ν) := by
      rw [(hshiftRestrict η).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
      have hx : 0 ≤
          (∫ ξ : Plane, ‖u (ξ - κ η)‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂ν) ^
            (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ := by positivity
      exact (ENNReal.toReal_ofReal hx).symm
    have hOnePow :
        (∫ ξ : Plane, ‖(1 : ℂ)‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂ν) ^
            (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ =
          ENNReal.toReal (eLpNorm (fun _ : Plane => (1 : ℂ)) 2 ν) := by
      rw [hOne.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
      have hx : 0 ≤
          (∫ ξ : Plane, ‖(1 : ℂ)‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂ν) ^
            (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ := by positivity
      exact (ENNReal.toReal_ofReal hx).symm
    have hshiftNorm :
        eLpNorm (fun ξ : Plane => u (ξ - κ η)) 2 ν ≤ eLpNorm u 2 volume := by
      calc
        eLpNorm (fun ξ : Plane => u (ξ - κ η)) 2 ν ≤
            eLpNorm (fun ξ : Plane => u (ξ - κ η)) 2 volume :=
          eLpNorm_mono_measure _ Measure.restrict_le_self
        _ = eLpNorm u 2 volume := by
          have hfun : (fun ξ : Plane => u (ξ - κ η)) =
              u ∘ l2TranslationMap (κ η) := by
            funext ξ
            rfl
          rw [hfun]
          exact eLpNorm_comp_measurePreserving huLp.aestronglyMeasurable
            (measurePreserving_l2TranslationMap (κ η))
    have hshiftNormReal :
        ENNReal.toReal (eLpNorm (fun ξ : Plane => u (ξ - κ η)) 2 ν) ≤
          ENNReal.toReal (eLpNorm u 2 volume) :=
      ENNReal.toReal_mono huLp.eLpNorm_ne_top hshiftNorm
    calc
      ∫ ξ : Plane, ‖u (ξ - κ η)‖ ∂ν =
          ∫ ξ : Plane, ‖u (ξ - κ η)‖ * ‖(1 : ℂ)‖ ∂ν := by simp
      _ ≤ (∫ ξ : Plane, ‖u (ξ - κ η)‖ ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) *
          (∫ ξ : Plane, ‖(1 : ℂ)‖ ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) := hHolder
      _ = ENNReal.toReal (eLpNorm (fun ξ : Plane => u (ξ - κ η)) 2 ν) *
          ENNReal.toReal (eLpNorm (fun _ : Plane => (1 : ℂ)) 2 ν) := by
        convert congrArg₂ (· * ·) hshiftPow hOnePow using 1; norm_num
      _ ≤ C := by
        dsimp [C]
        exact mul_le_mul_of_nonneg_right hshiftNormReal ENNReal.toReal_nonneg
  have hsliceInt (η : Plane) : Integrable (fun ξ : Plane => H (η, ξ)) ν := by
    change Integrable (fun ξ : Plane => k η * u (ξ - κ η)) ν
    exact (memLp_one_iff_integrable.mp
      ((hshiftRestrict η).mono_exponent (by norm_num))).const_mul (k η)
  have hJsm : AEStronglyMeasurable
      (fun η : Plane => ∫ ξ : Plane, ‖H (η, ξ)‖ ∂ν) (volume : Measure Plane) :=
    hHsm.norm.integral_prod_right'
  /- Integrability companion for the slice integral bound immediately below. -/
  have hsliceNormInt (η : Plane) :
      Integrable (fun ξ : Plane => ‖H (η, ξ)‖) ν := by
    have h := (hshiftNormIntegrable η).const_mul ‖k η‖
    convert h using 1
    funext ξ
    simp [H]
  have hJbound (η : Plane) :
      ∫ ξ : Plane, ‖H (η, ξ)‖ ∂ν ≤ ‖k η‖ * C := by
    calc
      ∫ ξ : Plane, ‖H (η, ξ)‖ ∂ν =
          ‖k η‖ * ∫ ξ : Plane, ‖u (ξ - κ η)‖ ∂ν := by
        dsimp [H]
        rw [show (fun ξ : Plane => ‖k η * u (ξ - κ η)‖) =
          fun ξ => ‖k η‖ * ‖u (ξ - κ η)‖ from by
            funext ξ
            rw [norm_mul]]
        rw [integral_const_mul]
      _ ≤ ‖k η‖ * C :=
        mul_le_mul_of_nonneg_left (hHolderBound η) (norm_nonneg _)
  have hJmajor : Integrable (fun η : Plane => ‖k η‖ * C) (volume : Measure Plane) :=
    hk.norm.mul_const C
  have hJint : Integrable
      (fun η : Plane => ∫ ξ : Plane, ‖H (η, ξ)‖ ∂ν) (volume : Measure Plane) := by
    refine hJmajor.mono' hJsm ?_
    filter_upwards with η
    have hnonneg : 0 ≤ ∫ ξ : Plane, ‖H (η, ξ)‖ ∂ν :=
      integral_nonneg fun ξ => norm_nonneg _
    rw [Real.norm_of_nonneg hnonneg]
    exact hJbound η
  have hHprod : Integrable H (volume.prod ν) := by
    apply (integrable_prod_iff hHsm).2
    refine ⟨?_, hJint⟩
    exact Filter.Eventually.of_forall hsliceInt
  exact hHprod

/-- Product integrability is preserved by a continuous multiplier with an integrable majorant uniform in the spatial variable. -/
theorem integrable_scalarMultiplierShiftProduct_on_finiteSet
    (k : Plane → ℂ) (M : Plane → ℝ)
    (hkM : Integrable (fun η : Plane => ‖k η‖ * M η)) (hkc : Continuous k)
    (κ : Plane → Plane) (hκc : Continuous κ)
    (m : Plane × Plane → ℂ) (hmC : Continuous m)
    (hMnonneg : ∀ η, 0 ≤ M η) (hmBound : ∀ η ξ, ‖m (η, ξ)‖ ≤ M η)
    (u : Plane → ℂ) (huC : Continuous u)
    (huLp : MemLp u 2 (volume : Measure Plane))
    (s : Set Plane) (hμs : volume s ≠ ∞) :
    Integrable (fun p : Plane × Plane => k p.1 * (m p * u (p.2 - κ p.1)))
      (volume.prod (volume.restrict s)) := by
  let ν : Measure Plane := volume.restrict s
  have hνfinite : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    change (volume.restrict s) Set.univ < ∞
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr hμs
  have : IsFiniteMeasure ν := hνfinite
  let H : Plane × Plane → ℂ :=
    fun p => k p.1 * (m p * u (p.2 - κ p.1))
  have hshiftMap : Continuous (fun p : Plane × Plane => p.2 - κ p.1) :=
    continuous_snd.sub (hκc.comp continuous_fst)
  have hHc : Continuous H := by
    dsimp [H]
    exact (hkc.comp continuous_fst).mul
      ((hmC).mul (huC.comp hshiftMap))
  have hHsm : AEStronglyMeasurable H (volume.prod ν) := hHc.aestronglyMeasurable
  have hOne : MemLp (fun _ : Plane => (1 : ℂ)) (2 : ENNReal) ν := memLp_const (1 : ℂ)
  have hOne' : MemLp (fun _ : Plane => (1 : ℂ)) (ENNReal.ofReal (2 : ℝ)) ν := by
    simpa using hOne
  let C : ℝ := ENNReal.toReal (eLpNorm u 2 (volume : Measure Plane)) *
    ENNReal.toReal (eLpNorm (fun _ : Plane => (1 : ℂ)) 2 ν)
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hshiftMem (η : Plane) :
      MemLp (fun ξ : Plane => u (ξ - κ η)) 2 (volume : Measure Plane) := by
    have hfun : (fun ξ : Plane => u (ξ - κ η)) = u ∘ l2TranslationMap (κ η) := by
      funext ξ
      rfl
    rw [hfun]
    exact huLp.comp_measurePreserving (measurePreserving_l2TranslationMap (κ η))
  have hshiftRestrict (η : Plane) :
      MemLp (fun ξ : Plane => u (ξ - κ η)) 2 ν :=
    (hshiftMem η).mono_measure Measure.restrict_le_self
  have hshiftRestrict' (η : Plane) :
      MemLp (fun ξ : Plane => u (ξ - κ η)) (ENNReal.ofReal (2 : ℝ)) ν := by
    simpa using hshiftRestrict η
  /- Integrability companion for the uniform Hölder integral bound. -/
  have hshiftNormIntegrable (η : Plane) :
      Integrable (fun ξ : Plane => ‖u (ξ - κ η)‖) ν := by
    have hshiftL1 : MemLp (fun ξ : Plane => u (ξ - κ η)) 1 ν :=
      (hshiftRestrict η).mono_exponent (by norm_num)
    exact (memLp_one_iff_integrable.mp hshiftL1).norm
  have hHolderBound (η : Plane) :
      (∫ ξ : Plane, ‖u (ξ - κ η)‖ ∂ν) ≤ C := by
    have hHolder := integral_mul_norm_le_Lp_mul_Lq
      (E := ℂ) (p := 2) (q := 2) Real.HolderConjugate.two_two
      (hshiftRestrict' η) hOne'
    have hshiftPow :
        (∫ ξ : Plane, ‖u (ξ - κ η)‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂ν) ^
            (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ =
          ENNReal.toReal (eLpNorm (fun ξ : Plane => u (ξ - κ η)) 2 ν) := by
      rw [(hshiftRestrict η).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
      have hx : 0 ≤
          (∫ ξ : Plane, ‖u (ξ - κ η)‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂ν) ^
            (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ := by positivity
      exact (ENNReal.toReal_ofReal hx).symm
    have hOnePow :
        (∫ ξ : Plane, ‖(1 : ℂ)‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂ν) ^
            (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ =
          ENNReal.toReal (eLpNorm (fun _ : Plane => (1 : ℂ)) 2 ν) := by
      rw [hOne.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
      have hx : 0 ≤
          (∫ ξ : Plane, ‖(1 : ℂ)‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂ν) ^
            (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ := by positivity
      exact (ENNReal.toReal_ofReal hx).symm
    have hshiftNorm :
        eLpNorm (fun ξ : Plane => u (ξ - κ η)) 2 ν ≤ eLpNorm u 2 volume := by
      calc
        eLpNorm (fun ξ : Plane => u (ξ - κ η)) 2 ν ≤
            eLpNorm (fun ξ : Plane => u (ξ - κ η)) 2 volume :=
          eLpNorm_mono_measure _ Measure.restrict_le_self
        _ = eLpNorm u 2 volume := by
          have hfun : (fun ξ : Plane => u (ξ - κ η)) =
              u ∘ l2TranslationMap (κ η) := by
            funext ξ
            rfl
          rw [hfun]
          exact eLpNorm_comp_measurePreserving huLp.aestronglyMeasurable
            (measurePreserving_l2TranslationMap (κ η))
    have hshiftNormReal :
        ENNReal.toReal (eLpNorm (fun ξ : Plane => u (ξ - κ η)) 2 ν) ≤
          ENNReal.toReal (eLpNorm u 2 volume) :=
      ENNReal.toReal_mono huLp.eLpNorm_ne_top hshiftNorm
    calc
      ∫ ξ : Plane, ‖u (ξ - κ η)‖ ∂ν =
          ∫ ξ : Plane, ‖u (ξ - κ η)‖ * ‖(1 : ℂ)‖ ∂ν := by simp
      _ ≤ (∫ ξ : Plane, ‖u (ξ - κ η)‖ ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) *
          (∫ ξ : Plane, ‖(1 : ℂ)‖ ^ (2 : ℝ) ∂ν) ^ (1 / 2 : ℝ) := hHolder
      _ = ENNReal.toReal (eLpNorm (fun ξ : Plane => u (ξ - κ η)) 2 ν) *
          ENNReal.toReal (eLpNorm (fun _ : Plane => (1 : ℂ)) 2 ν) := by
        convert congrArg₂ (· * ·) hshiftPow hOnePow using 1; norm_num
      _ ≤ C := by
        dsimp [C]
        exact mul_le_mul_of_nonneg_right hshiftNormReal ENNReal.toReal_nonneg
  have hmultiplierSliceInt (η : Plane) :
      Integrable (fun ξ : Plane => ‖m (η, ξ)‖ * ‖u (ξ - κ η)‖) ν := by
    have hmajor : Integrable (fun ξ : Plane => M η * ‖u (ξ - κ η)‖) ν :=
      (hshiftNormIntegrable η).const_mul (M η)
    have hmeas : AEStronglyMeasurable
        (fun ξ : Plane => ‖m (η, ξ)‖ * ‖u (ξ - κ η)‖) ν := by
      exact (((hmC.comp (continuous_const.prodMk continuous_id)).norm).mul
        (huC.comp (continuous_id.sub continuous_const)).norm).aestronglyMeasurable
    refine hmajor.mono' hmeas ?_
    filter_upwards with ξ
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg (m (η, ξ)))
      (norm_nonneg (u (ξ - κ η))))]
    exact mul_le_mul_of_nonneg_right (hmBound η ξ) (norm_nonneg (u (ξ - κ η)))
  have hsliceNormInt (η : Plane) :
      Integrable (fun ξ : Plane => ‖H (η, ξ)‖) ν := by
    have htarget : Integrable
        (fun ξ : Plane => ‖k η‖ * (‖m (η, ξ)‖ * ‖u (ξ - κ η)‖)) ν :=
      hmultiplierSliceInt η |>.const_mul ‖k η‖
    convert htarget using 1
    funext ξ
    simp [H]
  have hsliceInt (η : Plane) : Integrable (fun ξ : Plane => H (η, ξ)) ν := by
    have hsliceC : Continuous (fun ξ : Plane => H (η, ξ)) :=
      hHc.comp (continuous_const.prodMk continuous_id)
    exact (integrable_norm_iff hsliceC.aestronglyMeasurable).mp (hsliceNormInt η)
  have hJsm : AEStronglyMeasurable
      (fun η : Plane => ∫ ξ : Plane, ‖H (η, ξ)‖ ∂ν) (volume : Measure Plane) :=
    hHsm.norm.integral_prod_right'
  have hJbound (η : Plane) :
      ∫ ξ : Plane, ‖H (η, ξ)‖ ∂ν ≤ (‖k η‖ * M η) * C := by
    have hsliceBound :
        (∫ ξ : Plane, ‖m (η, ξ)‖ * ‖u (ξ - κ η)‖ ∂ν) ≤
          M η * ∫ ξ : Plane, ‖u (ξ - κ η)‖ ∂ν := by
      calc
        ∫ ξ : Plane, ‖m (η, ξ)‖ * ‖u (ξ - κ η)‖ ∂ν ≤
            ∫ ξ : Plane, M η * ‖u (ξ - κ η)‖ ∂ν := by
          apply integral_mono (hmultiplierSliceInt η)
            ((hshiftNormIntegrable η).const_mul (M η))
          intro ξ
          exact mul_le_mul_of_nonneg_right (hmBound η ξ) (norm_nonneg _)
        _ = M η * ∫ ξ : Plane, ‖u (ξ - κ η)‖ ∂ν := by
          rw [integral_const_mul]
    calc
      ∫ ξ : Plane, ‖H (η, ξ)‖ ∂ν =
          ‖k η‖ * ∫ ξ : Plane, ‖m (η, ξ)‖ * ‖u (ξ - κ η)‖ ∂ν := by
        dsimp [H]
        rw [show (fun ξ : Plane => ‖k η * (m (η, ξ) * u (ξ - κ η))‖) =
          fun ξ => ‖k η‖ * (‖m (η, ξ)‖ * ‖u (ξ - κ η)‖) from by
            funext ξ
            rw [norm_mul, norm_mul]]
        rw [integral_const_mul]
      _ ≤ ‖k η‖ * (M η * ∫ ξ : Plane, ‖u (ξ - κ η)‖ ∂ν) :=
          mul_le_mul_of_nonneg_left hsliceBound (norm_nonneg _)
      _ ≤ (‖k η‖ * M η) * C := by
          calc
            ‖k η‖ * (M η * ∫ ξ : Plane, ‖u (ξ - κ η)‖ ∂ν) =
                (‖k η‖ * M η) * ∫ ξ : Plane, ‖u (ξ - κ η)‖ ∂ν := by ring
            _ ≤ (‖k η‖ * M η) * C :=
              mul_le_mul_of_nonneg_left (hHolderBound η)
                (mul_nonneg (norm_nonneg (k η)) (hMnonneg η))
  have hJmajor : Integrable (fun η : Plane => (‖k η‖ * M η) * C) volume :=
    hkM.mul_const C
  have hJint : Integrable
      (fun η : Plane => ∫ ξ : Plane, ‖H (η, ξ)‖ ∂ν) volume := by
    refine hJmajor.mono' hJsm ?_
    filter_upwards with η
    have hnonneg : 0 ≤ ∫ ξ : Plane, ‖H (η, ξ)‖ ∂ν :=
      integral_nonneg fun ξ => norm_nonneg _
    rw [Real.norm_of_nonneg hnonneg]
    exact hJbound η
  have hHprod : Integrable H (volume.prod ν) := by
    apply (integrable_prod_iff hHsm).2
    exact ⟨Filter.Eventually.of_forall hsliceInt, hJint⟩
  exact hHprod

/-- The `L²`-valued average of weighted translates of `f`, with weights given by the Fourier
transform of the smooth cutoff `χ`. -/
noncomputable def scaledWeightedFourierConvolutionAction {a : ℝ} (ha : 0 ≤ a)
    (χ : TestFn) (f : Lp ℂ 2 (volume : Measure Plane)) : Lp ℂ 2 (volume : Measure Plane) :=
  ∫ η : Plane, (𝓕 (testFnSchwartz χ)) η •
    weightedTranslateL2 ha ((2 * Real.pi) • η) f

/-- The scaled weighted Bochner convolution agrees almost everywhere with the Fourier transform
of the localized distribution, multiplied by the square root Sobolev weight. -/
theorem scaledWeightedFourierConvolutionAction_ae_eq {a : ℝ} (ha : 0 ≤ a)
    (T : Distr) (ψ χ : TestFn)
    (hfinite : localNegSobolevSq a T ψ < ⊤) :
    (fun ξ : Plane => scaledWeightedFourierConvolutionAction ha χ
      ((memLp_negSobolevWeightedLocalizedFourier a T ψ hfinite).toLp
        (fun ξ : Plane => (negSobolevWeightSqrt a ξ : ℂ) * localizedFourier T ψ ξ)) ξ) =ᵐ[volume]
      fun ξ : Plane => (negSobolevWeightSqrt a ξ : ℂ) *
        localizedFourier T (testFnMul χ ψ) ξ := by
  let u : Plane → ℂ := fun ξ => (negSobolevWeightSqrt a ξ : ℂ) * localizedFourier T ψ ξ
  let hsource : MemLp u 2 (volume : Measure Plane) :=
    memLp_negSobolevWeightedLocalizedFourier a T ψ hfinite
  let f : Lp ℂ 2 (volume : Measure Plane) := hsource.toLp u
  let k : Plane → ℂ := fun η => (𝓕 (testFnSchwartz χ)) η
  let κ : Plane → Plane := fun η => (2 * Real.pi) • η
  let M : Plane → ℝ := fun η =>
    Real.sqrt (2 ^ a * (1 + ‖κ η‖ ^ 2) ^ a)
  let m : Plane × Plane → ℂ := fun p =>
    (negSobolevTranslationMultiplier a (κ p.1) p.2 : ℂ)
  let H : Plane × Plane → ℂ := fun p => k p.1 * (m p * u (p.2 - κ p.1))
  let F : Plane → Lp ℂ 2 (volume : Measure Plane) :=
    fun η => k η • weightedTranslateL2 ha (κ η) f
  let g : Lp ℂ 2 (volume : Measure Plane) := scaledWeightedFourierConvolutionAction ha χ f
  let V : Plane → ℂ := fun ξ => (negSobolevWeightSqrt a ξ : ℂ) *
    localizedFourier T (testFnMul χ ψ) ξ
  have hWpos (ξ : Plane) : 0 < negSobolevWeightSqrt a ξ := by
    unfold negSobolevWeightSqrt
    exact Real.sqrt_pos.2 (Real.rpow_pos_of_pos (by positivity) _)
  have hWcont : Continuous (negSobolevWeightSqrt a) := by
    have hbase : Continuous (fun ξ : Plane => (1 : ℝ) + ‖ξ‖ ^ 2) := by fun_prop
    have hp : Continuous (fun ξ : Plane => ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-a)) :=
      hbase.rpow_const fun ξ => Or.inl (by positivity)
    have hpPos : ∀ ξ : Plane, 0 < ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-a) :=
      fun ξ => Real.rpow_pos_of_pos (by positivity) _
    have hsqrt : Continuous (fun ξ : Plane =>
        (((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-a)) ^ (1 / 2 : ℝ)) :=
      hp.rpow_const fun ξ => Or.inl (ne_of_gt (hpPos ξ))
    have heq : negSobolevWeightSqrt a = fun ξ : Plane =>
        (((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-a)) ^ (1 / 2 : ℝ) := by
      funext ξ
      simp [negSobolevWeightSqrt, Real.sqrt_eq_rpow]
    exact heq ▸ hsqrt
  have huC : Continuous u := by
    dsimp [u]
    exact (Complex.continuous_ofReal.comp hWcont).mul (continuous_localizedFourier T ψ)
  have hkC : Continuous k := by
    dsimp [k]
    exact (𝓕 (testFnSchwartz χ)).continuous
  have hkM : Integrable (fun η : Plane => ‖k η‖ * M η) := by
    have heq : (fun η : Plane => ‖k η‖ * M η) =
        fun η : Plane => Real.sqrt (2 ^ a * (1 + (2 * Real.pi * ‖η‖) ^ 2) ^ a) *
          ‖(𝓕 (testFnSchwartz χ)) η‖ := by
      funext η
      dsimp [k, M, κ]
      have hnormκ : ‖(2 * Real.pi) • η‖ = 2 * Real.pi * ‖η‖ := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      rw [hnormκ]
      ring
    rw [heq]
    exact integrable_scaled_sqrt_negSobolevWeight_mul_norm_fourier_testFn ha χ
  have hκC : Continuous κ := by fun_prop
  have hMnonneg : ∀ η : Plane, 0 ≤ M η := fun η => Real.sqrt_nonneg _
  have hmC : Continuous m := by
    dsimp [m]
    have hnum : Continuous (fun p : Plane × Plane =>
        negSobolevWeightSqrt a p.2) := hWcont.comp continuous_snd
    have hden : Continuous (fun p : Plane × Plane =>
        negSobolevWeightSqrt a (p.2 - κ p.1)) :=
      hWcont.comp (continuous_snd.sub (hκC.comp continuous_fst))
    have hdenPos : ∀ p : Plane × Plane,
        negSobolevWeightSqrt a (p.2 - κ p.1) ≠ 0 :=
      fun p => ne_of_gt (hWpos (p.2 - κ p.1))
    exact Complex.continuous_ofReal.comp (hnum.div₀ hden hdenPos)
  have hmBound : ∀ η ξ, ‖m (η, ξ)‖ ≤ M η := by
    intro η ξ
    dsimp [m, M]
    rw [Complex.norm_real]
    have hratio : negSobolevTranslationMultiplier a (κ η) ξ ≤
        Real.sqrt (2 ^ a * (1 + ‖κ η‖ ^ 2) ^ a) := by
      have hden : 0 < negSobolevWeightSqrt a (ξ - κ η) := hWpos _
      apply (div_le_iff₀ hden).2
      have hshift := sqrt_negSobolevWeight_shift_le ha ξ (κ η)
      simpa [negSobolevTranslationMultiplier, negSobolevWeightSqrt] using hshift
    have hratio_nonneg : 0 ≤ negSobolevTranslationMultiplier a (κ η) ξ := by
      dsimp [negSobolevTranslationMultiplier]
      exact div_nonneg (le_of_lt (hWpos ξ)) (le_of_lt (hWpos (ξ - κ η)))
    rw [Real.norm_of_nonneg hratio_nonneg]
    exact hratio
  have hprod (s : Set Plane) (hs : MeasurableSet s) (hμs : volume s ≠ ∞) :
      Integrable H (volume.prod (volume.restrict s)) := by
    exact integrable_scalarMultiplierShiftProduct_on_finiteSet
      k M hkM hkC κ hκC m hmC hMnonneg hmBound u huC hsource s hμs
  have hFint : Integrable F := by
    have hbound := norm_integral_scaledFourier_weightedTranslateL2_le ha χ f
    exact hbound.1
  have hshiftSource (η : Plane) :
      (fun ξ : Plane => f (ξ - κ η)) =ᵐ[volume]
        fun ξ : Plane => u (ξ - κ η) := by
    change (f ∘ l2TranslationMap (κ η)) =ᵐ[volume] (u ∘ l2TranslationMap (κ η))
    exact (measurePreserving_l2TranslationMap (κ η)).quasiMeasurePreserving.ae_eq_comp
      hsource.coeFn_toLp
  have hrep (η : Plane) : F η =ᵐ[volume] fun ξ : Plane => H (η, ξ) := by
    dsimp [F]
    filter_upwards [weightedTranslateL2_ae_eq a ha (κ η) f, hshiftSource η,
      Lp.coeFn_smul (k η) (weightedTranslateL2 ha (κ η) f)]
      with ξ htranslate hsourceShift hsmul
    exact hsmul.trans (by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [htranslate, hsourceShift])
  have hcancel (η ξ : Plane) :
      m (η, ξ) * u (ξ - κ η) =
        (negSobolevWeightSqrt a ξ : ℂ) * localizedFourier T ψ (ξ - κ η) := by
    have hreal : negSobolevTranslationMultiplier a (κ η) ξ *
        negSobolevWeightSqrt a (ξ - κ η) = negSobolevWeightSqrt a ξ := by
      dsimp [negSobolevTranslationMultiplier]
      exact div_mul_cancel₀ _ (ne_of_gt (hWpos (ξ - κ η)))
    dsimp [m, u]
    calc
      (negSobolevTranslationMultiplier a (κ η) ξ : ℂ) *
          ((negSobolevWeightSqrt a (ξ - κ η) : ℂ) * localizedFourier T ψ (ξ - κ η)) =
        (((negSobolevTranslationMultiplier a (κ η) ξ *
            negSobolevWeightSqrt a (ξ - κ η) : ℝ) : ℂ) *
          localizedFourier T ψ (ξ - κ η)) := by push_cast; ring
      _ = (negSobolevWeightSqrt a ξ : ℂ) *
          localizedFourier T ψ (ξ - κ η) := by rw [hreal]
  have hpoint (ξ : Plane) : (∫ η : Plane, H (η, ξ)) = V ξ := by
    have hscalar := localizedFourier_testFnMul_eq_scaled_frequency_integral T χ ψ ξ
    calc
      (∫ η : Plane, H (η, ξ)) =
          ∫ η : Plane, (negSobolevWeightSqrt a ξ : ℂ) *
            (k η * localizedFourier T ψ (ξ - κ η)) := by
        apply integral_congr_ae
        filter_upwards with η
        dsimp [H]
        rw [hcancel η ξ]
        ring
      _ = (negSobolevWeightSqrt a ξ : ℂ) *
          ∫ η : Plane, k η * localizedFourier T ψ (ξ - κ η) := by
        rw [integral_const_mul]
      _ = V ξ := by
        dsimp [V]
        rw [hscalar.2]
  have hVcont : Continuous V := by
    dsimp [V]
    exact (Complex.continuous_ofReal.comp hWcont).mul
      (continuous_localizedFourier T (testFnMul χ ψ))
  have hOutLoc : LocallyIntegrable (fun ξ : Plane => g ξ) volume :=
    (Lp.memLp g).locallyIntegrable (by norm_num)
  have hVLoc : LocallyIntegrable V volume := hVcont.locallyIntegrable
  have hOutAE : (fun ξ : Plane => g ξ) =ᵐ[volume] V := by
    rw [← sub_ae_eq_zero]
    refine ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero'
      (hOutLoc.sub hVLoc) ?_
    intro s hs
    have hμs : volume s ≠ ∞ := hs.measure_ne_top
    have hset := setIntegral_integrableLpFamily_eq_scalar F hFint s hs.measurableSet
      hμs H (hprod s hs.measurableSet hμs) hrep
    have hsetG : (∫ ξ in s, g ξ) =
        (∫ ξ in s, ∫ η : Plane, H (η, ξ)) := by
      simpa [g, scaledWeightedFourierConvolutionAction, F, k, κ] using hset
    have hright : (∫ ξ in s, ∫ η : Plane, H (η, ξ)) = ∫ ξ in s, V ξ := by
      apply setIntegral_congr_ae hs.measurableSet
      filter_upwards with ξ hx
      exact hpoint ξ
    have houtInt : IntegrableOn (fun ξ : Plane => g ξ) s volume :=
      hOutLoc.integrableOn_isCompact hs
    have hVInt : IntegrableOn V s volume := hVLoc.integrableOn_isCompact hs
    calc
      ∫ ξ in s, (g ξ - V ξ) =
          (∫ ξ in s, g ξ) - (∫ ξ in s, V ξ) := integral_sub' houtInt hVInt
      _ = 0 := by rw [hsetG, hright]; simp
  exact hOutAE

/-- Finite negative energy is preserved by multiplication by a compactly supported smooth
cutoff: the weighted localized Fourier transform remains in `L²`. -/
theorem memLp_weightedLocalizedFourier_testFnMul {a : ℝ} (ha : 0 ≤ a)
    (T : Distr) (ψ χ : TestFn)
    (hfinite : localNegSobolevSq a T ψ < ⊤) :
    MemLp (fun ξ : Plane => (negSobolevWeightSqrt a ξ : ℂ) *
      localizedFourier T (testFnMul χ ψ) ξ) 2 (volume : Measure Plane) := by
  let g := scaledWeightedFourierConvolutionAction ha χ
    ((memLp_negSobolevWeightedLocalizedFourier a T ψ hfinite).toLp
      (fun ξ : Plane => (negSobolevWeightSqrt a ξ : ℂ) * localizedFourier T ψ ξ))
  have hAE := scaledWeightedFourierConvolutionAction_ae_eq ha T ψ χ hfinite
  have hWcont : Continuous (negSobolevWeightSqrt a) := by
    have hbase : Continuous (fun ξ : Plane => (1 : ℝ) + ‖ξ‖ ^ 2) := by fun_prop
    have hp : Continuous (fun ξ : Plane => ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-a)) :=
      hbase.rpow_const fun ξ => Or.inl (by positivity)
    have hpPos : ∀ ξ : Plane, 0 < ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-a) :=
      fun ξ => Real.rpow_pos_of_pos (by positivity) _
    have hsqrt : Continuous (fun ξ : Plane =>
        (((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-a)) ^ (1 / 2 : ℝ)) :=
      hp.rpow_const fun ξ => Or.inl (ne_of_gt (hpPos ξ))
    have heq : negSobolevWeightSqrt a = fun ξ : Plane =>
        (((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-a)) ^ (1 / 2 : ℝ) := by
      funext ξ
      simp [negSobolevWeightSqrt, Real.sqrt_eq_rpow]
    exact heq ▸ hsqrt
  have hVcont : Continuous (fun ξ : Plane =>
      (negSobolevWeightSqrt a ξ : ℂ) * localizedFourier T (testFnMul χ ψ) ξ) :=
    (Complex.continuous_ofReal.comp hWcont).mul
      (continuous_localizedFourier T (testFnMul χ ψ))
  have hnormAE : (fun ξ : Plane => ‖g ξ‖) =ᵐ[volume]
      fun ξ : Plane =>
        ‖(negSobolevWeightSqrt a ξ : ℂ) * localizedFourier T (testFnMul χ ψ) ξ‖ :=
    hAE.mono fun ξ hξ => congrArg norm hξ
  exact (Lp.memLp g).congr_norm hVcont.aestronglyMeasurable hnormAE

/-- The localized weighted Fourier transform obeys the continuous weighted Young bound. The
integrability of the scalar kernel weight is included beside the integral bound. -/
theorem norm_weightedLocalizedFourier_testFnMul_le {a : ℝ} (ha : 0 ≤ a)
    (T : Distr) (ψ χ : TestFn)
    (hfinite : localNegSobolevSq a T ψ < ⊤) :
    Integrable (fun η : Plane => ‖(𝓕 (testFnSchwartz χ)) η‖ *
      Real.sqrt (2 ^ a * (1 + (2 * Real.pi * ‖η‖) ^ 2) ^ a)) ∧
      ‖(memLp_weightedLocalizedFourier_testFnMul ha T ψ χ hfinite).toLp
          (fun ξ : Plane => (negSobolevWeightSqrt a ξ : ℂ) *
            localizedFourier T (testFnMul χ ψ) ξ)‖ ≤
        (∫ η : Plane, ‖(𝓕 (testFnSchwartz χ)) η‖ *
          Real.sqrt (2 ^ a * (1 + (2 * Real.pi * ‖η‖) ^ 2) ^ a)) *
          ‖(memLp_negSobolevWeightedLocalizedFourier a T ψ hfinite).toLp
            (fun ξ : Plane => (negSobolevWeightSqrt a ξ : ℂ) * localizedFourier T ψ ξ)‖ := by
  let u : Plane → ℂ := fun ξ =>
    (negSobolevWeightSqrt a ξ : ℂ) * localizedFourier T ψ ξ
  let hsource : MemLp u 2 (volume : Measure Plane) :=
    memLp_negSobolevWeightedLocalizedFourier a T ψ hfinite
  let f : Lp ℂ 2 (volume : Measure Plane) := hsource.toLp u
  let htarget : MemLp (fun ξ : Plane =>
      (negSobolevWeightSqrt a ξ : ℂ) * localizedFourier T (testFnMul χ ψ) ξ)
      2 (volume : Measure Plane) :=
    memLp_weightedLocalizedFourier_testFnMul ha T ψ χ hfinite
  let V : Plane → ℂ := fun ξ =>
    (negSobolevWeightSqrt a ξ : ℂ) * localizedFourier T (testFnMul χ ψ) ξ
  let g : Lp ℂ 2 (volume : Measure Plane) :=
    scaledWeightedFourierConvolutionAction ha χ f
  have hAE := scaledWeightedFourierConvolutionAction_ae_eq ha T ψ χ hfinite
  have hClass : htarget.toLp V = g := by
    calc
      htarget.toLp V = (Lp.memLp g).toLp (fun ξ : Plane => g ξ) :=
        MemLp.toLp_congr htarget (Lp.memLp g) hAE.symm
      _ = g := Lp.toLp_coeFn g (Lp.memLp g)
  have hKernel : Integrable (fun η : Plane => ‖(𝓕 (testFnSchwartz χ)) η‖ *
      Real.sqrt (2 ^ a * (1 + (2 * Real.pi * ‖η‖) ^ 2) ^ a)) := by
    simpa [mul_comm] using
      integrable_scaled_sqrt_negSobolevWeight_mul_norm_fourier_testFn ha χ
  have hbound := norm_integral_scaledFourier_weightedTranslateL2_le ha χ f
  refine ⟨hKernel, ?_⟩
  rw [hClass]
  change ‖scaledWeightedFourierConvolutionAction ha χ f‖ ≤
    (∫ η : Plane, ‖(𝓕 (testFnSchwartz χ)) η‖ *
      Real.sqrt (2 ^ a * (1 + (2 * Real.pi * ‖η‖) ^ 2) ^ a)) * ‖f‖
  simpa [scaledWeightedFourierConvolutionAction] using hbound.2

/-- The square is the normalized ordinary `L²` integral of the weighted angular
Fourier transform. This identity also holds when the energy is infinite. -/
theorem localNegSobolevSq_eq_weightedFourier_lintegral (a : ℝ) (T : Distr) (χ : TestFn) :
    localNegSobolevSq a T χ =
      ENNReal.ofReal ((2 * Real.pi)⁻¹ ^ 2) *
        (∫⁻ ξ : Plane, ENNReal.ofReal
          (‖(negSobolevWeightSqrt a ξ : ℂ) * localizedFourier T χ ξ‖ ^ 2)) := by
  let G : Plane → ℝ≥0∞ := fun ξ => ENNReal.ofReal
    (‖(negSobolevWeightSqrt a ξ : ℂ) * localizedFourier T χ ξ‖ ^ 2)
  have hWcont : Continuous (negSobolevWeightSqrt a) := by
    have hbase : Continuous (fun ξ : Plane => (1 : ℝ) + ‖ξ‖ ^ 2) := by fun_prop
    have hp : Continuous (fun ξ : Plane => ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-a)) :=
      hbase.rpow_const fun ξ => Or.inl (by positivity)
    have hpPos : ∀ ξ : Plane, 0 < ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-a) :=
      fun ξ => Real.rpow_pos_of_pos (by positivity) _
    have hsqrt : Continuous (fun ξ : Plane =>
        (((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-a)) ^ (1 / 2 : ℝ)) :=
      hp.rpow_const fun ξ => Or.inl (ne_of_gt (hpPos ξ))
    have heq : negSobolevWeightSqrt a = fun ξ : Plane =>
        (((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-a)) ^ (1 / 2 : ℝ) := by
      funext ξ
      simp [negSobolevWeightSqrt, Real.sqrt_eq_rpow]
    exact heq ▸ hsqrt
  have hG : Measurable G := by
    dsimp [G]
    exact (((Complex.continuous_ofReal.comp hWcont).mul
      (continuous_localizedFourier T χ)).norm.pow 2).measurable.ennreal_ofReal
  have hGscale : Measurable (fun ξ : Plane => G ((2 * Real.pi) • ξ)) := by
    exact hG.comp (by fun_prop)
  have hscale := lintegral_angular_frequency_scaling
    (H := fun ξ : Plane => G ((2 * Real.pi) • ξ)) hGscale
  have hscale' : ENNReal.ofReal ((2 * Real.pi)⁻¹ ^ 2) *
      (∫⁻ ξ : Plane, G ξ) = ∫⁻ ξ : Plane, G ((2 * Real.pi) • ξ) := by
    simpa only [smul_smul, mul_inv_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_smul]
      using hscale
  rw [Critical2DKPZ.Analysis.Sobolev.Rellich.localNegSobolevSq_eq_scaled_localizedFourier]
  change (∫⁻ η : Plane, ENNReal.ofReal
      ((1 + (2 * Real.pi * ‖η‖) ^ 2) ^ (-a) *
        ‖localizedFourier T χ ((2 * Real.pi) • η)‖ ^ 2)) = _
  calc
    (∫⁻ η : Plane, ENNReal.ofReal
        ((1 + (2 * Real.pi * ‖η‖) ^ 2) ^ (-a) *
          ‖localizedFourier T χ ((2 * Real.pi) • η)‖ ^ 2)) =
        ∫⁻ η : Plane, G ((2 * Real.pi) • η) := by
      apply lintegral_congr
      intro η
      let ξ := (2 * Real.pi) • η
      have hnormScale : ‖ξ‖ = 2 * Real.pi * ‖η‖ := by
        dsimp [ξ]
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      have hweight : (1 + (2 * Real.pi * ‖η‖) ^ 2) ^ (-a) =
          negSobolevWeightSqrt a ξ ^ 2 := by
        rw [negSobolevWeightSqrt, Real.sq_sqrt
          (Real.rpow_nonneg (by positivity) _), hnormScale]
      have hnorm : ‖(negSobolevWeightSqrt a ξ : ℂ) *
          localizedFourier T χ ξ‖ ^ 2 = negSobolevWeightSqrt a ξ ^ 2 *
            ‖localizedFourier T χ ξ‖ ^ 2 := by
        unfold negSobolevWeightSqrt
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
      dsimp [G]
      change ENNReal.ofReal ((1 + (2 * Real.pi * ‖η‖) ^ 2) ^ (-a) *
          ‖localizedFourier T χ ξ‖ ^ 2) =
        ENNReal.ofReal (‖(negSobolevWeightSqrt a ξ : ℂ) *
          localizedFourier T χ ξ‖ ^ 2)
      rw [hweight, hnorm]
    _ = ENNReal.ofReal ((2 * Real.pi)⁻¹ ^ 2) * (∫⁻ ξ : Plane, G ξ) := hscale'.symm

private theorem ofReal_norm_sq_eq_enorm_sq (z : ℂ) :
    ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg z)]
  simp

private theorem weightedFourier_lintegral_eq_eLpNorm_sq {f : Plane → ℂ}
    (hf : MemLp f 2 (volume : Measure Plane)) :
    (∫⁻ ξ : Plane, ENNReal.ofReal (‖f ξ‖ ^ 2)) =
      eLpNorm f 2 (volume : Measure Plane) ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := f) (p := (2 : NNReal))
    (by norm_num) hf.aestronglyMeasurable
  simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two,
    ofReal_norm_sq_eq_enorm_sq] using h.symm

/-- Multiplication by a compactly supported smooth cutoff is bounded in the local
negative Sobolev square. The displayed integrability conjunct ensures the kernel integral in the
uniform constant is an actual finite integral. -/
theorem localNegSobolevSq_testFnMul_le {a : ℝ} (ha : 0 ≤ a)
    (T : Distr) (ψ χ : TestFn)
    (hfinite : localNegSobolevSq a T ψ < ⊤) :
    Integrable (fun η : Plane => ‖(𝓕 (testFnSchwartz χ)) η‖ *
      Real.sqrt (2 ^ a * (1 + (2 * Real.pi * ‖η‖) ^ 2) ^ a)) ∧
      localNegSobolevSq a T (testFnMul χ ψ) ≤
        ENNReal.ofReal ((∫ η : Plane, ‖(𝓕 (testFnSchwartz χ)) η‖ *
          Real.sqrt (2 ^ a * (1 + (2 * Real.pi * ‖η‖) ^ 2) ^ a)) ^ 2) *
          localNegSobolevSq a T ψ := by
  let u : Plane → ℂ := fun ξ => (negSobolevWeightSqrt a ξ : ℂ) *
    localizedFourier T ψ ξ
  let v : Plane → ℂ := fun ξ => (negSobolevWeightSqrt a ξ : ℂ) *
    localizedFourier T (testFnMul χ ψ) ξ
  have hu : MemLp u 2 (volume : Measure Plane) :=
    memLp_negSobolevWeightedLocalizedFourier a T ψ hfinite
  have hv : MemLp v 2 (volume : Measure Plane) :=
    memLp_weightedLocalizedFourier_testFnMul ha T ψ χ hfinite
  let f : Lp ℂ 2 (volume : Measure Plane) := hu.toLp u
  let g : Lp ℂ 2 (volume : Measure Plane) := hv.toLp v
  let K : ℝ := ∫ η : Plane, ‖(𝓕 (testFnSchwartz χ)) η‖ *
    Real.sqrt (2 ^ a * (1 + (2 * Real.pi * ‖η‖) ^ 2) ^ a)
  have hYoung := norm_weightedLocalizedFourier_testFnMul_le ha T ψ χ hfinite
  have hKint : Integrable (fun η : Plane => ‖(𝓕 (testFnSchwartz χ)) η‖ *
      Real.sqrt (2 ^ a * (1 + (2 * Real.pi * ‖η‖) ^ 2) ^ a)) := hYoung.1
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    exact integral_nonneg fun η => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hNormF : ENNReal.ofReal ‖f‖ = eLpNorm u 2 (volume : Measure Plane) := by
    change ENNReal.ofReal ‖hu.toLp u‖ = eLpNorm u 2 (volume : Measure Plane)
    rw [ofReal_norm, Lp.enorm_toLp hu]
  have hYoungReal : ‖g‖ ≤ K * ‖f‖ := by
    simpa [K, f, g, u, v] using hYoung.2
  have hYoungENN : eLpNorm v 2 (volume : Measure Plane) ≤
      ENNReal.ofReal K * eLpNorm u 2 (volume : Measure Plane) := by
    calc
      eLpNorm v 2 (volume : Measure Plane) = ‖g‖ₑ := (Lp.enorm_toLp hv).symm
      _ = ENNReal.ofReal ‖g‖ := by rw [ofReal_norm]
      _ ≤ ENNReal.ofReal (K * ‖f‖) := ENNReal.ofReal_le_ofReal hYoungReal
      _ = ENNReal.ofReal K * eLpNorm u 2 (volume : Measure Plane) := by
        rw [ENNReal.ofReal_mul hKnonneg, hNormF]
  have hIntegralBound :
      (∫⁻ ξ : Plane, ENNReal.ofReal (‖v ξ‖ ^ 2)) ≤
        ENNReal.ofReal K ^ 2 * (∫⁻ ξ : Plane, ENNReal.ofReal (‖u ξ‖ ^ 2)) := by
    rw [weightedFourier_lintegral_eq_eLpNorm_sq hv,
      weightedFourier_lintegral_eq_eLpNorm_sq hu]
    calc
      eLpNorm v 2 (volume : Measure Plane) ^ 2 ≤
          (ENNReal.ofReal K * eLpNorm u 2 (volume : Measure Plane)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hYoungENN 2
      _ = ENNReal.ofReal K ^ 2 * eLpNorm u 2 (volume : Measure Plane) ^ 2 := by
        rw [mul_pow]
  refine ⟨hKint, ?_⟩
  rw [localNegSobolevSq_eq_weightedFourier_lintegral,
    localNegSobolevSq_eq_weightedFourier_lintegral]
  calc
    ENNReal.ofReal ((2 * Real.pi)⁻¹ ^ 2) *
        (∫⁻ ξ : Plane, ENNReal.ofReal (‖v ξ‖ ^ 2)) ≤
      ENNReal.ofReal ((2 * Real.pi)⁻¹ ^ 2) *
        (ENNReal.ofReal K ^ 2 * ∫⁻ ξ : Plane, ENNReal.ofReal (‖u ξ‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hIntegralBound (by positivity)
    _ = ENNReal.ofReal (K ^ 2) *
        (ENNReal.ofReal ((2 * Real.pi)⁻¹ ^ 2) *
          ∫⁻ ξ : Plane, ENNReal.ofReal (‖u ξ‖ ^ 2)) := by
      rw [ENNReal.ofReal_pow hKnonneg]
      ac_rfl

end Critical2DKPZ.Analysis.Sobolev

end
