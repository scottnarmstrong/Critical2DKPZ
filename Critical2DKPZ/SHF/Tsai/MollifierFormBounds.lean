/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.MollifierOperators
public import Critical2DKPZ.SHF.DeltaBose.FormBounds
import Critical2DKPZ.SHF.Tsai.L2ProductHelpers
import Critical2DKPZ.SHF.Tsai.PositiveApproximation
import Critical2DKPZ.SHF.Tsai.PositiveMonotoneProducts

/-! # Positive form bounds of applicable mollifiers

The defining real `L²` convolution bound first controls bounded, finite-volume
positive tests. Increasing truncations give the extended positive action bound,
and hence a positive form bound. Banach–Steinhaus makes its constant uniform
along the applicable mollifier family.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- A real `L²` bound for a nonnegative convolution kernel gives its positive form bound. -/
theorem formBound_of_mollifierAction_bound {w : Plane → ℝ} (hw0 : ∀ x, 0 ≤ w x)
    (hwm : Measurable w) (hw : MemLp w 2) {M : ℝ≥0∞}
    (hM : ∀ (φ : Plane → ℝ), MemLp φ 2 → eLpNorm (mollifierAction w φ) 2 ≤ M * eLpNorm φ 2) :
    FormBound volume volume (fun x y : Plane => ENNReal.ofReal (w (x - y))) M := by
  let K (x y : Plane) := ENNReal.ofReal (w (x - y))
  have hK : Measurable (Function.uncurry K) :=
    (hwm.comp (measurable_fst.sub measurable_snd)).ennreal_ofReal
  apply (formBound_iff_l2_sq_le volume volume hK M).2
  intro f hf
  let A (N : ℕ) (x : Plane) := ∫⁻ y, K x y * positiveTruncation f N y
  have hAm (N) : Measurable (A N) :=
    measurable_kernelAction volume hK (measurable_positiveTruncation hf N)
  have hAmono (x) : Monotone (fun N => A N x) := fun N N' hNN' =>
    lintegral_mono fun y => mul_le_mul' le_rfl (monotone_positiveTruncation f hNN' y)
  have hAsup (x : Plane) : (⨆ N, A N x) = ∫⁻ y, K x y * f y := by
    rw [← lintegral_iSup (f := fun N y => K x y * positiveTruncation f N y)
      (fun N => ((hK.comp (measurable_const.prodMk measurable_id)).mul
        (measurable_positiveTruncation hf N)))
      (fun N N' hNN' y => mul_le_mul' le_rfl (monotone_positiveTruncation f hNN' y))]
    apply lintegral_congr
    intro y
    rw [← ENNReal.mul_iSup, iSup_positiveTruncation]
  have hsq (N : ℕ) : (∫⁻ x, A N x ^ (2 : ℕ)) ≤ M ^ 2 * ∫⁻ y, f y ^ (2 : ℕ) := by
    let φ (x : Plane) := (positiveTruncation f N x).toReal
    have hφ : MemLp φ 2 := memLp_positiveTruncation_toReal hf N
    have hφ0 (x) : 0 ≤ φ x := ENNReal.toReal_nonneg
    have hconv0 (x) : 0 ≤ mollifierAction w φ x :=
      integral_nonneg fun y => mul_nonneg (hw0 _) (hφ0 y)
    have hconv (x) : ENNReal.ofReal (mollifierAction w φ x) = A N x := by
      change ENNReal.ofReal (∫ y, w (x - y) * φ y) = _
      rw [ofReal_integral_eq_lintegral_ofReal (integrable_mollifierAction_integrand hw hφ x)
        (Filter.Eventually.of_forall fun y => mul_nonneg (hw0 _) (hφ0 y))]
      apply lintegral_congr
      intro y
      rw [ENNReal.ofReal_mul (hw0 _), show ENNReal.ofReal (φ y) = positiveTruncation f N y from
        ofReal_positiveTruncation_toReal f N y]
    have hconvM : AEStronglyMeasurable (mollifierAction w φ) volume :=
      (((hwm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable).mul
        hφ.aestronglyMeasurable.comp_snd).integral_prod_right'
    have hbound := pow_le_pow_left₀ (bot_le : (0 : ℝ≥0∞) ≤ eLpNorm (mollifierAction w φ) 2)
      (hM φ hφ) 2
    rw [mul_pow, sq_eLpNorm_two_eq_lintegral_enorm hconvM, sq_eLpNorm_two_eq_lintegral_enorm hφ.aestronglyMeasurable] at hbound
    have hφnorm (x) : ‖φ x‖ₑ = positiveTruncation f N x := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hφ0 x)]
      exact ofReal_positiveTruncation_toReal f N x
    have hconvnorm (x) : ‖mollifierAction w φ x‖ₑ = A N x := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hconv0 x), hconv x]
    simp_rw [hφnorm, hconvnorm] at hbound
    apply hbound.trans
    apply mul_le_mul' le_rfl
    apply lintegral_mono
    intro y
    have hle : positiveTruncation f N y ≤ f y := by
      rw [← iSup_positiveTruncation f y]
      exact le_iSup (fun j => positiveTruncation f j y) N
    exact pow_le_pow_left₀ bot_le hle 2
  have hsupSq (x : Plane) : (∫⁻ y, K x y * f y) ^ (2 : ℕ) = ⨆ N, A N x ^ (2 : ℕ) := by
    rw [← hAsup x, pow_two, iSup_mul_of_monotone (hAmono x) (hAmono x)]
    simp only [pow_two]
  simp only [ENNReal.rpow_two]
  simp_rw [hsupSq]
  rw [lintegral_iSup (fun N => (hAm N).pow_const (2 : ℕ))
    (fun N N' hNN' x => pow_le_pow_left₀ bot_le (hAmono x hNN') 2)]
  exact iSup_le hsq

/-- An applicable family has one finite positive form constant for every index. -/
theorem exists_formBound_mollifier_uniform {w : ℕ → Plane → ℝ} (hw : IsL2ApplicableMollifier w) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ j,
      FormBound volume volume (fun x y : Plane => ENNReal.ofReal (w j (x - y))) M := by
  obtain ⟨M, hMfin, hM⟩ := exists_mollifierAction_uniform_bound hw
  exact ⟨M, hMfin, fun j => formBound_of_mollifierAction_bound (hw.1 j)
    (hw.2.1 j).measurable (hw.2.2.1 j) (fun φ hφ => hM j φ hφ)⟩

end Critical2DKPZ.SHF.Tsai

end
