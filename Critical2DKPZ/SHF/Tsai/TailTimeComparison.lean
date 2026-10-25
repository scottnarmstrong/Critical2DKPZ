/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.HeadTail
public import Critical2DKPZ.SHF.Tsai.ConjugatedDiagramTimeComparison
import Mathlib.Tactic

/-! # Time comparison for literal tail words -/

@[expose] public section

open MeasureTheory Set Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Dilating all collision times compares the literal tail word at nearby
positive durations, with a factor exponential in its length. -/
theorem tailWordKernel_le_time_dilate {n : ℕ} (θ : ℝ) (β : CollisionPair n)
    (w : List (CollisionPair n)) {a t : ℝ} (ha : 1 ≤ a)
    (z : FusedConfiguration β) (y : Configuration n) :
    tailWordKernel θ β w t z y ≤
      ENNReal.ofReal (a ^ (n * (2 * w.length + 2))) *
        tailWordKernel θ β w (a * t) z y := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  let C : ℝ≥0∞ := ENNReal.ofReal (a ^ (n * (2 * w.length + 2)))
  let J : ℝ≥0∞ := ∫⁻ u in Ioo 0 t, ∫⁻ z' : FusedConfiguration β,
    ENNReal.ofReal (collisionKernel β θ (a * u) z z') *
      diagramKernel θ w (a * (t - u)) (collisionEmbedding β z') y
  have hC : C ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfactor : ENNReal.ofReal (a ^ n) *
      ENNReal.ofReal (a ^ (n * (2 * w.length + 1))) = C := by
    rw [← ENNReal.ofReal_mul (pow_nonneg ha0.le _), ← pow_add]
    congr 1
    congr 1
    ring
  have hpoint (u : ℝ) (hu : u ∈ Ioo 0 t) (z' : FusedConfiguration β) :
      ENNReal.ofReal (collisionKernel β θ u z z') *
          diagramKernel θ w (t - u) (collisionEmbedding β z') y ≤
        C * (ENNReal.ofReal (collisionKernel β θ (a * u) z z') *
          diagramKernel θ w (a * (t - u)) (collisionEmbedding β z') y) := by
    have hJ : ENNReal.ofReal (collisionKernel β θ u z z') ≤
        ENNReal.ofReal (a ^ n) * ENNReal.ofReal (collisionKernel β θ (a * u) z z') := by
      rw [← ENNReal.ofReal_mul (pow_nonneg ha0.le _)]
      exact ENNReal.ofReal_le_ofReal (collisionKernel_le_time_dilate β θ ha hu.1 z z')
    have hD := diagramKernel_le_time_dilate θ ha w (sub_pos.mpr hu.2)
      (collisionEmbedding β z') y
    calc
      _ ≤ (ENNReal.ofReal (a ^ n) * ENNReal.ofReal (collisionKernel β θ (a * u) z z')) *
          (ENNReal.ofReal (a ^ (n * (2 * w.length + 1))) *
            diagramKernel θ w (a * (t - u)) (collisionEmbedding β z') y) :=
        mul_le_mul' hJ hD
      _ = _ := by rw [← hfactor]; ac_rfl
  have hdom : tailWordKernel θ β w t z y ≤ C * J := by
    unfold tailWordKernel
    calc
      _ ≤ ∫⁻ u in Ioo 0 t, ∫⁻ z' : FusedConfiguration β,
          C * (ENNReal.ofReal (collisionKernel β θ (a * u) z z') *
            diagramKernel θ w (a * (t - u)) (collisionEmbedding β z') y) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
        exact lintegral_mono (hpoint u hu)
      _ = C * J := by simp_rw [lintegral_const_mul' C _ hC]; rfl
  have hscale : tailWordKernel θ β w (a * t) z y = ENNReal.ofReal a * J := by
    unfold tailWordKernel
    rw [lintegral_Ioo_zero_mul ha0 t]
    congr 1
    apply lintegral_congr
    intro u
    rw [show a * t - a * u = a * (t - u) by ring]
  have hJle : J ≤ ENNReal.ofReal a * J :=
    le_mul_of_one_le_left zero_le (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal ha)
  exact hdom.trans (mul_le_mul' le_rfl (hJle.trans_eq hscale.symm))

/-- A uniform comparison on the doubled time interval. -/
theorem tailWordKernel_le_on_double_time_interval {n : ℕ} (θ : ℝ)
    (β : CollisionPair n) (w : List (CollisionPair n)) {t s : ℝ}
    (ht : 0 < t) (hts : t ≤ s) (hst : s ≤ 2 * t)
    (z : FusedConfiguration β) (y : Configuration n) :
    tailWordKernel θ β w t z y ≤
      ENNReal.ofReal ((2 : ℝ) ^ (n * (2 * w.length + 2))) *
        tailWordKernel θ β w s z y := by
  have ha : 1 ≤ s / t := (le_div_iff₀ ht).mpr (by simpa only [one_mul] using hts)
  have ha2 : s / t ≤ 2 := (div_le_iff₀ ht).mpr hst
  have h := tailWordKernel_le_time_dilate θ β w (t := t) ha z y
  rw [div_mul_cancel₀ s ht.ne'] at h
  exact h.trans (mul_le_mul'
    (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (zero_le_one.trans ha) ha2 _)) le_rfl)

end Critical2DKPZ.SHF.Tsai

end
