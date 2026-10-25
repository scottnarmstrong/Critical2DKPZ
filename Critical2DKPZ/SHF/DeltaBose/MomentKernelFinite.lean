/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.MomentKernelFormBounds
public import Critical2DKPZ.SHF.DeltaBose.SupBlockBounds
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic

/-! # Almost-everywhere finiteness of the full moment kernel -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- The positive form bound implies that the full moment kernel is finite for
almost every pair of endpoints. -/
theorem momentKernel_ne_top (n : ℕ) (hn : n ≤ 4) (θ : ℝ) {h : ℝ} (hh : 0 < h) :
    ∀ᵐ xy : Configuration n × Configuration n ∂(volume.prod volume),
      momentKernel n θ h xy.1 xy.2 ≠ ⊤ := by
  have hsmall : n ≤ 4 := hn
  obtain ⟨C, rate, hC, hForm⟩ := exists_formBound_momentKernel n θ
  let o : Configuration n := fun _ => 0
  let w : Configuration n → ℝ≥0∞ := configurationExpDecayKernel 1 o
  let K : Configuration n → Configuration n → ℝ≥0∞ := momentKernel n θ h
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
  have hK : Measurable (Function.uncurry K) := by
    have hmap : Measurable (fun p : Configuration n × Configuration n => ((θ, h), p)) :=
      (measurable_const : Measurable (fun _ : Configuration n × Configuration n =>
        (θ, h))).prodMk measurable_id
    have hcomp := (measurable_momentKernel n).comp hmap
    convert hcomp using 1
    funext p
    rfl
  have hF : Measurable F := by
    dsimp [F]
    exact (hw.comp measurable_fst).mul
      (hK.mul (hw.comp measurable_snd))
  have hpositiveForm := hForm θ le_rfl h hh
  have hcoeff :
      ENNReal.ofReal (C * Real.exp (rate * h) * min h 1 ^ (-(n : ℝ))) *
        (∫⁻ y : Configuration n, w y ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∫⁻ x : Configuration n, w x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwRootNe) hwRootNe
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
    change momentKernel n θ h xy.1 xy.2 * w xy.2 = ⊤
    rw [hKtop]
    exact ENNReal.top_mul (hwpos xy.2)
  have hFtop : F xy = ⊤ := by
    dsimp [F]
    rw [hinner]
    exact ENNReal.mul_top (hwpos xy.1)
  exact (ne_of_lt hFlt) hFtop

end Critical2DKPZ.DeltaBose
