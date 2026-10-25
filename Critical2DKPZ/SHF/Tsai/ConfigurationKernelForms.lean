/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.FormBounds
public import Critical2DKPZ.SHF.DeltaBose.SupBlockBounds
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic

/-! # Integrable forms of positive configuration kernels

A positive kernel with a finite `L²` form bound is finite almost everywhere and has
absolutely integrable bilinear forms on `L²` tests, controlled by the same form constant.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- A positive configuration kernel with a finite form bound is finite almost everywhere. -/
theorem configurationKernel_ne_top_of_formBound {n : ℕ}
    {K : Configuration n → Configuration n → ℝ≥0∞}
    (hKm : Measurable (Function.uncurry K)) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hForm : FormBound volume volume K c) :
    ∀ᵐ xy : Configuration n × Configuration n ∂(volume.prod volume), K xy.1 xy.2 ≠ ⊤ := by
  let o : Configuration n := fun _ => 0
  let w : Configuration n → ℝ≥0∞ := configurationExpDecayKernel 1 o
  let F : Configuration n × Configuration n → ℝ≥0∞ :=
    fun xy => w xy.1 * (K xy.1 xy.2 * w xy.2)
  have hw : Measurable w := by
    dsimp [w]
    exact (measurable_configurationExpDecayKernel 1).comp
      (measurable_const.prodMk measurable_id)
  have hwpos (x : Configuration n) : w x ≠ 0 := by
    change configurationExpDecayKernel 1 o x ≠ 0
    rw [configurationExpDecayKernel_apply]
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hwtop (x : Configuration n) : w x ≠ ⊤ := by
    change configurationExpDecayKernel 1 o x ≠ ⊤
    rw [configurationExpDecayKernel_apply]
    exact ENNReal.ofReal_ne_top
  have hwle (x : Configuration n) : w x ≤ 1 := by
    change configurationExpDecayKernel 1 o x ≤ 1
    rw [configurationExpDecayKernel_apply, ← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_one_iff.mpr
    have hnorm : 0 ≤ configurationOneNorm x := by
      unfold configurationOneNorm
      apply Finset.sum_nonneg
      intro i hi
      exact planeOneNorm_nonneg _
    simpa [o, sub_zero] using neg_nonpos.mpr hnorm
  have hwSq :
      (∫⁻ x : Configuration n, w x ^ (2 : ℝ)) ≤
        ENNReal.ofReal (((2 / (1 : ℝ)) ^ 2) ^ n) := by
    calc
      (∫⁻ x : Configuration n, w x ^ (2 : ℝ)) ≤ ∫⁻ x, w x := by
        apply lintegral_mono
        intro x
        change w x ^ (2 : ℝ) ≤ w x
        calc
          w x ^ (2 : ℝ) = w x * w x := by rw [ENNReal.rpow_two, pow_two]
          _ ≤ 1 * w x := mul_le_mul_of_nonneg_right (hwle x) (bot_le)
          _ = w x := one_mul _
      _ = ENNReal.ofReal (((2 / (1 : ℝ)) ^ 2) ^ n) := by
        exact lintegral_configurationExpDecayKernel_right (by norm_num) o
  have hwSqNe : (∫⁻ x : Configuration n, w x ^ (2 : ℝ)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hwSq
  have hwRootNe :
      ((∫⁻ x : Configuration n, w x ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg (x := ∫⁻ x : Configuration n, w x ^ (2 : ℝ))
      (y := (1 / 2 : ℝ)) (by norm_num) hwSqNe).ne
  have hK : Measurable (Function.uncurry K) := hKm
  have hF : Measurable F := by
    dsimp [F]
    exact (hw.comp measurable_fst).mul
      (hK.mul (hw.comp measurable_snd))
  have hpositiveForm := hForm
  have hcoeff :
      c *
        (∫⁻ y : Configuration n, w y ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∫⁻ x : Configuration n, w x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hc hwRootNe) hwRootNe
  have hweightedFinite :
      (∫⁻ x : Configuration n, w x *
        (∫⁻ y : Configuration n, K x y * w y) ∂volume) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hcoeff
    exact hpositiveForm w w hw hw
  have hdouble :
      (∫⁻ xy : Configuration n × Configuration n, F xy ∂(volume.prod volume)) =
        ∫⁻ x : Configuration n, w x *
          (∫⁻ y : Configuration n, K x y * w y ∂volume) ∂volume := by
    rw [lintegral_prod _ hF.aemeasurable]
    apply lintegral_congr
    intro x
    calc
      (∫⁻ y : Configuration n, F (x, y)) =
          w x * ∫⁻ y : Configuration n, K x y * w y := by
            rw [show (fun y : Configuration n => F (x, y)) =
                fun y => w x * (K x y * w y) by
                  funext y
                  rfl,
              lintegral_const_mul' _ _ (hwtop x)]
      _ = w x * (∫⁻ y : Configuration n, K x y * w y) := rfl
  have hFfinite :
      (∫⁻ xy : Configuration n × Configuration n, F xy ∂(volume.prod volume)) ≠ ⊤ := by
    rw [hdouble]
    exact hweightedFinite
  have hFae : ∀ᵐ xy : Configuration n × Configuration n ∂(volume.prod volume),
      F xy < ⊤ := ae_lt_top hF hFfinite
  filter_upwards [hFae] with xy hFlt
  intro hKtop
  have hinner : K xy.1 xy.2 * w xy.2 = ⊤ := by
    rw [hKtop]
    exact ENNReal.top_mul (hwpos xy.2)
  have hFtop : F xy = ⊤ := by
    dsimp [F]
    rw [hinner]
    exact ENNReal.mul_top (hwpos xy.1)
  exact (ne_of_lt hFlt) hFtop

/-- A finite positive form bound gives absolute integrability and the real bilinear bound. -/
theorem configurationKernel_real_form_bound {n : ℕ}
    {K : Configuration n → Configuration n → ℝ≥0∞}
    (hKm : Measurable (Function.uncurry K)) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hForm : FormBound volume volume K c) (F G : Configuration n → ℝ)
    (hF : MemLp F 2) (hG : MemLp G 2) :
    Integrable (fun xy : Configuration n × Configuration n =>
      F xy.1 * (K xy.1 xy.2).toReal * G xy.2) (volume.prod volume) ∧
    |∫ xy : Configuration n × Configuration n,
      F xy.1 * (K xy.1 xy.2).toReal * G xy.2 ∂(volume.prod volume)| ≤
      c.toReal * (eLpNorm F 2).toReal * (eLpNorm G 2).toReal := by
  let u : Configuration n → ℝ≥0∞ := fun x => ‖F x‖ₑ
  let v : Configuration n → ℝ≥0∞ := fun y => ‖G y‖ₑ
  let um : Configuration n → ℝ≥0∞ := hF.enorm.aemeasurable.mk u
  let vm : Configuration n → ℝ≥0∞ := hG.enorm.aemeasurable.mk v
  let H : Configuration n × Configuration n → ℝ :=
    fun xy => F xy.1 * (K xy.1 xy.2).toReal * G xy.2
  have hK : Measurable (Function.uncurry K) := hKm
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
    exact configurationKernel_ne_top_of_formBound hKm hc hForm
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
  have hpositiveForm : FormBound volume volume K c := hForm
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
        c * (∫⁻ y : Configuration n, v y ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫⁻ x : Configuration n, u x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    calc
      _ = ∫⁻ x : Configuration n, um x *
          (∫⁻ y : Configuration n, K x y * vm y) := by
            apply lintegral_congr_ae
            exact huEq.mono fun x hx => by
              change u x * (∫⁻ y : Configuration n, K x y * v y) =
                um x * (∫⁻ y : Configuration n, K x y * vm y)
              rw [hx, hActionEq x]
      _ ≤ c * (∫⁻ y : Configuration n, vm y ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
            (∫⁻ x : Configuration n, um x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
              hpositiveForm vm um hvm hum
      _ = c * (∫⁻ y : Configuration n, v y ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
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
        c * eLpNorm G 2 volume * eLpNorm F 2 volume := by
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
      _ ≤ c * (∫⁻ y : Configuration n, v y ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
            (∫⁻ x : Configuration n, u x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hpositiveRaw
      _ = c * eLpNorm G 2 volume * eLpNorm F 2 volume := by
            rw [show (∫⁻ y : Configuration n, v y ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
                eLpNorm G 2 volume by simpa only [ENNReal.rpow_two] using hrootG,
              show (∫⁻ x : Configuration n, u x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
                eLpNorm F 2 volume by simpa only [ENNReal.rpow_two] using hrootF]
  have hHabs_integrable : Integrable (fun xy : Configuration n × Configuration n => |H xy|)
      (volume.prod volume) := by
    have hnormIntegral :
        (∫⁻ xy : Configuration n × Configuration n,
          ENNReal.ofReal ‖H xy‖ ∂(volume.prod volume)) ≤
          c * eLpNorm G 2 volume * eLpNorm F 2 volume := by
      simpa only [Real.norm_eq_abs] using hAbsolute
    have hnormIntegrable : Integrable (fun xy : Configuration n × Configuration n => ‖H xy‖)
        (volume.prod volume) :=
      (lintegral_ofReal_ne_top_iff_integrable hH.norm
        (Filter.Eventually.of_forall fun xy => norm_nonneg (H xy))).1 <|
          ne_top_of_le_ne_top
            (ENNReal.mul_ne_top (ENNReal.mul_ne_top hc hG.eLpNorm_ne_top)
              hF.eLpNorm_ne_top) hnormIntegral
    simpa only [Real.norm_eq_abs] using hnormIntegrable
  have hHint : Integrable H (volume.prod volume) := by
    apply (integrable_norm_iff hH).mp
    simpa only [Real.norm_eq_abs] using hHabs_integrable
  refine ⟨hHint, ?_⟩
  have hreal : ENNReal.ofReal |∫ xy, H xy ∂(volume.prod volume)| ≤
      c * eLpNorm F 2 volume * eLpNorm G 2 volume := by
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
      _ ≤ c * eLpNorm G 2 volume * eLpNorm F 2 volume := hAbsolute
      _ = c * eLpNorm F 2 volume * eLpNorm G 2 volume := by ring
  have hProductTop : c * eLpNorm F 2 volume * eLpNorm G 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hc hF.eLpNorm_ne_top) hG.eLpNorm_ne_top
  have hreal' : |∫ xy, H xy ∂(volume.prod volume)| ≤
      (c * eLpNorm F 2 volume * eLpNorm G 2 volume).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hProductTop).1 hreal
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at hreal'
  simpa only [H, mul_assoc] using hreal'

end Critical2DKPZ.SHF.Tsai

end
