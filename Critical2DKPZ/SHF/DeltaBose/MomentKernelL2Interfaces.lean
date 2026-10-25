/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.MomentKernelFinite
public import Critical2DKPZ.SHF.DeltaBose.Measurability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

/-! # Real `L²` form bounds for the moment kernel -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- The positive form estimate yields an integrable real `L²` bilinear form
for the full moment kernel. -/
theorem momentKernel_L2_form_bounded (n : ℕ) (hn : n ≤ 4) (θ : ℝ)
    {h : ℝ} (hh : 0 < h) :
    ∃ C : ℝ, ∀ F G : Configuration n → ℝ,
      MemLp F 2 volume → MemLp G 2 volume →
      Integrable (fun xy : Configuration n × Configuration n =>
        F xy.1 * (momentKernel n θ h xy.1 xy.2).toReal * G xy.2) (volume.prod volume) ∧
      |∫ xy : Configuration n × Configuration n,
          F xy.1 * (momentKernel n θ h xy.1 xy.2).toReal * G xy.2
            ∂(volume.prod volume)| ≤
        C * (eLpNorm F 2 volume).toReal * (eLpNorm G 2 volume).toReal := by
  have hsmall : n ≤ 4 := hn
  obtain ⟨C₀, rate, hC₀, hForm⟩ := exists_formBound_momentKernel n θ
  let D : ℝ≥0∞ := ENNReal.ofReal
    (C₀ * Real.exp (rate * h) * min h 1 ^ (-(n : ℝ)))
  have hD : D ≠ ⊤ := by
    dsimp [D]
    exact ENNReal.ofReal_ne_top
  refine ⟨D.toReal, fun F G hF hG => ?_⟩
  let K : Configuration n → Configuration n → ℝ≥0∞ := fun x y => momentKernel n θ h x y
  let u : Configuration n → ℝ≥0∞ := fun x => ‖F x‖ₑ
  let v : Configuration n → ℝ≥0∞ := fun y => ‖G y‖ₑ
  let um : Configuration n → ℝ≥0∞ := hF.enorm.aemeasurable.mk u
  let vm : Configuration n → ℝ≥0∞ := hG.enorm.aemeasurable.mk v
  let H : Configuration n × Configuration n → ℝ :=
    fun xy => F xy.1 * (K xy.1 xy.2).toReal * G xy.2
  have hK : Measurable (Function.uncurry K) := by
    have hmap : Measurable (fun p : Configuration n × Configuration n => ((θ, h), p)) :=
      (measurable_const : Measurable (fun _ : Configuration n × Configuration n =>
        (θ, h))).prodMk measurable_id
    have hcomp := (measurable_momentKernel n).comp hmap
    convert hcomp using 1
    funext p
    rfl
  have hKreal : Measurable (fun p : Configuration n × Configuration n =>
      (K p.1 p.2).toReal) := hK.ennreal_toReal
  have hu : AEMeasurable u volume := hF.enorm.aestronglyMeasurable.aemeasurable
  have hv : AEMeasurable v volume := hG.enorm.aestronglyMeasurable.aemeasurable
  have hum : Measurable um := hF.enorm.aemeasurable.measurable_mk
  have hvm : Measurable vm := hG.enorm.aemeasurable.measurable_mk
  have huEq : u =ᵐ[volume] um := by
    exact hF.enorm.aemeasurable.ae_eq_mk
  have hvEq : v =ᵐ[volume] vm := by
    exact hG.enorm.aemeasurable.ae_eq_mk
  have hH : AEStronglyMeasurable H (volume.prod volume) := by
    exact ((hF.aestronglyMeasurable.comp_fst.mul
      hKreal.aestronglyMeasurable).mul hG.aestronglyMeasurable.comp_snd)
  have hneTop : ∀ᵐ xy : Configuration n × Configuration n ∂(volume.prod volume),
      K xy.1 xy.2 ≠ ⊤ := by
    simpa only [K] using momentKernel_ne_top n hn θ hh
  have hpoint (xy : Configuration n × Configuration n) (hfinite : K xy.1 xy.2 ≠ ⊤) :
      ENNReal.ofReal |H xy| = (K xy.1 xy.2 * v xy.2) * u xy.1 := by
    have hk : 0 ≤ (K xy.1 xy.2).toReal := ENNReal.toReal_nonneg
    calc
      ENNReal.ofReal |H xy| =
          ENNReal.ofReal (|F xy.1| * (K xy.1 xy.2).toReal * |G xy.2|) := by
            simp only [H, abs_mul, abs_of_nonneg hk]
      _ = (ENNReal.ofReal |F xy.1| * ENNReal.ofReal (K xy.1 xy.2).toReal) *
          ENNReal.ofReal |G xy.2| := by
            rw [ENNReal.ofReal_mul
              (mul_nonneg (abs_nonneg _) ENNReal.toReal_nonneg),
              ENNReal.ofReal_mul (abs_nonneg _)]
      _ = (K xy.1 xy.2 * v xy.2) * u xy.1 := by
            rw [ENNReal.ofReal_toReal hfinite]
            simp [u, v, Real.enorm_eq_ofReal_abs, mul_comm, mul_left_comm]
  have hAbsMeas : AEMeasurable (fun xy : Configuration n × Configuration n =>
      ENNReal.ofReal |H xy|) (volume.prod volume) := by
    have hnorm : AEMeasurable (fun xy : Configuration n × Configuration n =>
        ENNReal.ofReal ‖H xy‖) (volume.prod volume) :=
      hH.norm.aemeasurable.ennreal_ofReal
    convert hnorm using 1
  have hrootF : (∫⁻ x : Configuration n, u x ^ (2 : ℕ)) ^ (1 / 2 : ℝ) =
      eLpNorm F 2 volume := by
    simpa only [u, ENNReal.toReal_ofNat, ENNReal.rpow_two, pow_two] using
      (eLpNorm_eq_lintegral_rpow_enorm_toReal
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
        hF.aestronglyMeasurable).symm
  have hrootG : (∫⁻ y : Configuration n, v y ^ (2 : ℕ)) ^ (1 / 2 : ℝ) =
      eLpNorm G 2 volume := by
    simpa only [v, ENNReal.toReal_ofNat, ENNReal.rpow_two, pow_two] using
      (eLpNorm_eq_lintegral_rpow_enorm_toReal
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
        hG.aestronglyMeasurable).symm
  have hpositiveForm : FormBound volume volume K D := by
    have h := hForm θ le_rfl h hh
    simpa [K, D] using h
  have huSq : (∫⁻ x : Configuration n, u x ^ (2 : ℝ)) =
      ∫⁻ x : Configuration n, um x ^ (2 : ℝ) := by
    apply lintegral_congr_ae
    exact huEq.mono fun x hx => by
      change u x ^ (2 : ℝ) = um x ^ (2 : ℝ)
      rw [hx]
  have hvSq : (∫⁻ y : Configuration n, v y ^ (2 : ℝ)) =
      ∫⁻ y : Configuration n, vm y ^ (2 : ℝ) := by
    apply lintegral_congr_ae
    exact hvEq.mono fun y hy => by
      change v y ^ (2 : ℝ) = vm y ^ (2 : ℝ)
      rw [hy]
  have hActionEq (x : Configuration n) :
      (∫⁻ y : Configuration n, K x y * v y) =
        ∫⁻ y : Configuration n, K x y * vm y := by
    apply lintegral_congr_ae
    exact hvEq.mono fun y hy => by
      change K x y * v y = K x y * vm y
      rw [hy]
  have hpositiveRaw :
      (∫⁻ x : Configuration n, u x *
        (∫⁻ y : Configuration n, K x y * v y)) ≤
        D * (∫⁻ y : Configuration n, v y ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫⁻ x : Configuration n, u x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    calc
      _ = ∫⁻ x : Configuration n, um x *
          (∫⁻ y : Configuration n, K x y * vm y) := by
            apply lintegral_congr_ae
            exact huEq.mono fun x hx => by
              change u x * (∫⁻ y : Configuration n, K x y * v y) =
                um x * (∫⁻ y : Configuration n, K x y * vm y)
              rw [hx, hActionEq x]
      _ ≤ D * (∫⁻ y : Configuration n, vm y ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
            (∫⁻ x : Configuration n, um x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
              hpositiveForm vm um hvm hum
      _ = D * (∫⁻ y : Configuration n, v y ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
            (∫⁻ x : Configuration n, u x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
              rw [← hvSq, ← huSq]
  have hrowAEMeas (x : Configuration n) :
      AEMeasurable (fun y : Configuration n => K x y * v y) volume :=
    ((hK.comp (measurable_const.prodMk measurable_id)).aemeasurable).mul hv
  have hAbsEq :
      (∫⁻ xy : Configuration n × Configuration n,
        ENNReal.ofReal |H xy| ∂(volume.prod volume)) =
      ∫⁻ xy : Configuration n × Configuration n,
        (K xy.1 xy.2 * v xy.2) * u xy.1 ∂(volume.prod volume) := by
    apply lintegral_congr_ae
    filter_upwards [hneTop] with xy hfinite
    exact hpoint xy hfinite
  have hProductMeas : AEMeasurable (fun xy : Configuration n × Configuration n =>
      (K xy.1 xy.2 * v xy.2) * u xy.1) (volume.prod volume) :=
    ((hK.aemeasurable.mul (hv.comp_snd)).mul hu.comp_fst)
  have hAbsolute :
      (∫⁻ xy : Configuration n × Configuration n,
        ENNReal.ofReal |H xy| ∂(volume.prod volume)) ≤
        D * eLpNorm G 2 volume * eLpNorm F 2 volume := by
    rw [hAbsEq, lintegral_prod _ hProductMeas]
    calc
      (∫⁻ x : Configuration n,
          ∫⁻ y : Configuration n, (K x y * v y) * u x) =
        ∫⁻ x : Configuration n, (∫⁻ y : Configuration n, K x y * v y) * u x := by
          apply lintegral_congr
          intro x
          exact lintegral_mul_const'' (u x) (hrowAEMeas x)
      _ = ∫⁻ x : Configuration n, u x *
            (∫⁻ y : Configuration n, K x y * v y) := by
              apply lintegral_congr
              intro x
              ac_rfl
      _ ≤ D * (∫⁻ y : Configuration n, v y ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
            (∫⁻ x : Configuration n, u x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hpositiveRaw
      _ = D * eLpNorm G 2 volume * eLpNorm F 2 volume := by
            rw [show (∫⁻ y : Configuration n, v y ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
                eLpNorm G 2 volume by simpa only [ENNReal.rpow_two] using hrootG,
              show (∫⁻ x : Configuration n, u x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
                eLpNorm F 2 volume by simpa only [ENNReal.rpow_two] using hrootF]
  have hHabs_integrable : Integrable (fun xy : Configuration n × Configuration n => |H xy|)
      (volume.prod volume) := by
    have hnormIntegral :
        (∫⁻ xy : Configuration n × Configuration n,
          ENNReal.ofReal ‖H xy‖ ∂(volume.prod volume)) ≤
          D * eLpNorm G 2 volume * eLpNorm F 2 volume := by
      simpa only [Real.norm_eq_abs] using hAbsolute
    have hnormIntegrable : Integrable (fun xy : Configuration n × Configuration n => ‖H xy‖)
        (volume.prod volume) :=
      (lintegral_ofReal_ne_top_iff_integrable hH.norm
        (Filter.Eventually.of_forall fun xy => norm_nonneg (H xy))).1 <|
          ne_top_of_le_ne_top
            (ENNReal.mul_ne_top (ENNReal.mul_ne_top hD hG.eLpNorm_ne_top)
              hF.eLpNorm_ne_top) hnormIntegral
    simpa only [Real.norm_eq_abs] using hnormIntegrable
  have hHint : Integrable H (volume.prod volume) := by
    apply (integrable_norm_iff hH).mp
    simpa only [Real.norm_eq_abs] using hHabs_integrable
  refine ⟨hHint, ?_⟩
  have hreal : ENNReal.ofReal |∫ xy, H xy ∂(volume.prod volume)| ≤
      D * eLpNorm F 2 volume * eLpNorm G 2 volume := by
    calc
      ENNReal.ofReal |∫ xy, H xy ∂(volume.prod volume)| =
          ENNReal.ofReal ‖∫ xy, H xy ∂(volume.prod volume)‖ := by rw [Real.norm_eq_abs]
      _ ≤ ENNReal.ofReal (∫ xy, ‖H xy‖ ∂(volume.prod volume)) :=
            ENNReal.ofReal_le_ofReal (norm_integral_le_integral_norm H)
      _ = ∫⁻ xy, ‖H xy‖ₑ ∂(volume.prod volume) := ofReal_integral_norm_eq_lintegral_enorm hHint
      _ = ∫⁻ xy, ENNReal.ofReal |H xy| ∂(volume.prod volume) := by
            apply lintegral_congr_ae
            filter_upwards [] with xy
            rw [Real.enorm_eq_ofReal_abs]
      _ ≤ D * eLpNorm G 2 volume * eLpNorm F 2 volume := hAbsolute
      _ = D * eLpNorm F 2 volume * eLpNorm G 2 volume := by ring
  have hProductTop : D * eLpNorm F 2 volume * eLpNorm G 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hD hF.eLpNorm_ne_top) hG.eLpNorm_ne_top
  have hreal' : |∫ xy, H xy ∂(volume.prod volume)| ≤
      (D * eLpNorm F 2 volume * eLpNorm G 2 volume).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hProductTop).1 hreal
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at hreal'
  simpa only [H, D, mul_assoc] using hreal'

end Critical2DKPZ.DeltaBose
