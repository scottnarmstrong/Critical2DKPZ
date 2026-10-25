/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedBlockTimeComparison
import Mathlib.Tactic

/-! # Time averaging of concrete delta-Bose diagrams -/

@[expose] public section

open MeasureTheory Set Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Time dilation in the two first-collision variables, leaving every spatial
coordinate fixed. The two positive Jacobians are retained explicitly. -/
theorem diagramKernel_cons_time_dilate {n : ℕ} (α : CollisionPair n)
    (w : List (CollisionPair n)) (θ : ℝ) {a : ℝ} (ha : 0 < a) (t : ℝ)
    (x y : Configuration n) :
    diagramKernel θ (α :: w) (a * t) x y =
      ENNReal.ofReal a * (ENNReal.ofReal a *
        ∫⁻ r in Ioo 0 t, ∫⁻ u in Ioo r t,
          ∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
            ENNReal.ofReal (incomingKernel α (a * r) z x) *
            ENNReal.ofReal (collisionKernel α θ (a * (u - r)) z z') *
            diagramKernel θ w (a * (t - u)) (collisionEmbedding α z') y) := by
  calc
    _ = ENNReal.ofReal a *
        ∫⁻ r in Ioo 0 t, ∫⁻ u in Ioo (a * r) (a * t),
          ∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
            ENNReal.ofReal (incomingKernel α (a * r) z x) *
            ENNReal.ofReal (collisionKernel α θ (u - a * r) z z') *
            diagramKernel θ w (a * t - u) (collisionEmbedding α z') y := by
      rw [diagramKernel, lintegral_Ioo_zero_mul ha t]
    _ = ENNReal.ofReal a *
        ∫⁻ r in Ioo 0 t, ENNReal.ofReal a *
          ∫⁻ u in Ioo r t, ∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
            ENNReal.ofReal (incomingKernel α (a * r) z x) *
            ENNReal.ofReal (collisionKernel α θ (a * (u - r)) z z') *
            diagramKernel θ w (a * (t - u)) (collisionEmbedding α z') y := by
      congr 1
      apply lintegral_congr
      intro r
      rw [lintegral_Ioo_mul ha r t]
      congr 1
      apply lintegral_congr
      intro u
      rw [show a * u - a * r = a * (u - r) by ring,
        show a * t - a * u = a * (t - u) by ring]
    _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Increasing a diagram's time by a bounded factor costs at most an
exponential in its word length. This concrete kernel comparison is the
positivity input for Laplace averaging. -/
theorem diagramKernel_le_time_dilate {n : ℕ} (θ : ℝ) {a : ℝ} (ha : 1 ≤ a)
    (w : List (CollisionPair n)) {t : ℝ} (ht : 0 < t) (x y : Configuration n) :
    diagramKernel θ w t x y ≤ ENNReal.ofReal (a ^ (n * (2 * w.length + 1))) *
      diagramKernel θ w (a * t) x y := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  induction w generalizing t x y with
  | nil =>
    simp only [List.length_nil, mul_zero, zero_add, mul_one, diagramKernel]
    rw [← ENNReal.ofReal_mul (pow_nonneg ha0.le _)]
    exact ENNReal.ofReal_le_ofReal (freeKernel_le_time_dilate n ha ht x y)
  | cons α w ih =>
    let C : ℝ≥0∞ := ENNReal.ofReal (a ^ (n * (2 * (w.length + 1) + 1)))
    let A : ℝ≥0∞ := ENNReal.ofReal a
    let J : ℝ≥0∞ := ∫⁻ r in Ioo 0 t, ∫⁻ u in Ioo r t,
      ∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
        ENNReal.ofReal (incomingKernel α (a * r) z x) *
        ENNReal.ofReal (collisionKernel α θ (a * (u - r)) z z') *
        diagramKernel θ w (a * (t - u)) (collisionEmbedding α z') y
    have hCt : C ≠ ⊤ := ENNReal.ofReal_ne_top
    have hc : ENNReal.ofReal (a ^ n) * ENNReal.ofReal (a ^ n) *
        ENNReal.ofReal (a ^ (n * (2 * w.length + 1))) = C := by
      rw [← ENNReal.ofReal_mul (pow_nonneg ha0.le _),
        ← ENNReal.ofReal_mul (mul_nonneg (pow_nonneg ha0.le _) (pow_nonneg ha0.le _)),
        ← pow_add, ← pow_add]
      congr 1
      congr 1
      ring
    have hpoint (r : ℝ) (hr : r ∈ Ioo 0 t) (u : ℝ) (hu : u ∈ Ioo r t)
        (z z' : FusedConfiguration α) :
        ENNReal.ofReal (incomingKernel α r z x) *
          ENNReal.ofReal (collisionKernel α θ (u - r) z z') *
          diagramKernel θ w (t - u) (collisionEmbedding α z') y ≤
        C * (ENNReal.ofReal (incomingKernel α (a * r) z x) *
          ENNReal.ofReal (collisionKernel α θ (a * (u - r)) z z') *
          diagramKernel θ w (a * (t - u)) (collisionEmbedding α z') y) := by
      have hi : ENNReal.ofReal (incomingKernel α r z x) ≤
          ENNReal.ofReal (a ^ n) * ENNReal.ofReal (incomingKernel α (a * r) z x) := by
        rw [← ENNReal.ofReal_mul (pow_nonneg ha0.le _)]
        exact ENNReal.ofReal_le_ofReal (freeKernel_le_time_dilate n ha hr.1 x (collisionEmbedding α z))
      have hj : ENNReal.ofReal (collisionKernel α θ (u - r) z z') ≤
          ENNReal.ofReal (a ^ n) * ENNReal.ofReal (collisionKernel α θ (a * (u - r)) z z') := by
        rw [← ENNReal.ofReal_mul (pow_nonneg ha0.le _)]
        exact ENNReal.ofReal_le_ofReal (collisionKernel_le_time_dilate α θ ha (sub_pos.mpr hu.1) z z')
      have hrec := ih (sub_pos.mpr hu.2) (collisionEmbedding α z') y
      calc
        _ ≤ (ENNReal.ofReal (a ^ n) * ENNReal.ofReal (incomingKernel α (a * r) z x)) *
            (ENNReal.ofReal (a ^ n) * ENNReal.ofReal (collisionKernel α θ (a * (u - r)) z z')) *
            (ENNReal.ofReal (a ^ (n * (2 * w.length + 1))) *
              diagramKernel θ w (a * (t - u)) (collisionEmbedding α z') y) :=
          mul_le_mul' (mul_le_mul' hi hj) hrec
        _ = (ENNReal.ofReal (a ^ n) * ENNReal.ofReal (a ^ n) *
            ENNReal.ofReal (a ^ (n * (2 * w.length + 1)))) *
            (ENNReal.ofReal (incomingKernel α (a * r) z x) *
              ENNReal.ofReal (collisionKernel α θ (a * (u - r)) z z') *
              diagramKernel θ w (a * (t - u)) (collisionEmbedding α z') y) := by ac_rfl
        _ = _ := by rw [hc]
    have hdom : diagramKernel θ (α :: w) t x y ≤ C * J := by
      calc
        _ ≤ ∫⁻ r in Ioo 0 t, ∫⁻ u in Ioo r t,
            ∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
              C * (ENNReal.ofReal (incomingKernel α (a * r) z x) *
                ENNReal.ofReal (collisionKernel α θ (a * (u - r)) z z') *
                diagramKernel θ w (a * (t - u)) (collisionEmbedding α z') y) := by
          change (∫⁻ r in Ioo 0 t, ∫⁻ u in Ioo r t,
            ∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
              ENNReal.ofReal (incomingKernel α r z x) *
                ENNReal.ofReal (collisionKernel α θ (u - r) z z') *
                diagramKernel θ w (t - u) (collisionEmbedding α z') y) ≤ _
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
          exact lintegral_mono (fun z => lintegral_mono (fun z' => hpoint r hr u hu z z'))
        _ = _ := by simp_rw [lintegral_const_mul' C _ hCt]; rfl
    have hscale : diagramKernel θ (α :: w) (a * t) x y = A * (A * J) :=
      diagramKernel_cons_time_dilate α w θ ha0 t x y
    have hA : 1 ≤ A := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal ha
    have hJ : J ≤ A * (A * J) := by
      have hfirst : J ≤ A * J := le_mul_of_one_le_left zero_le hA
      exact hfirst.trans (mul_le_mul' le_rfl hfirst)
    change diagramKernel θ (α :: w) t x y ≤ C * diagramKernel θ (α :: w) (a * t) x y
    calc
      _ ≤ C * J := hdom
      _ ≤ C * (A * (A * J)) := mul_le_mul' le_rfl hJ
      _ = _ := congrArg (fun q : ℝ≥0∞ => C * q) hscale.symm

/-- On a doubled time interval, the concrete diagram comparison has a
single constant depending only on particle number and word length. -/
theorem diagramKernel_le_on_double_time_interval {n : ℕ} (θ : ℝ)
    (w : List (CollisionPair n)) {t s : ℝ} (ht : 0 < t) (hts : t ≤ s) (hst : s ≤ 2 * t)
    (x y : Configuration n) :
    diagramKernel θ w t x y ≤ ENNReal.ofReal ((2 : ℝ) ^ (n * (2 * w.length + 1))) *
      diagramKernel θ w s x y := by
  have ha : 1 ≤ s / t := (le_div_iff₀ ht).mpr (by simpa only [one_mul] using hts)
  have ha2 : s / t ≤ 2 := (div_le_iff₀ ht).mpr hst
  have h := diagramKernel_le_time_dilate θ ha w ht x y
  rw [div_mul_cancel₀ s ht.ne'] at h
  exact h.trans (mul_le_mul'
    (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (zero_le_one.trans ha) ha2 _)) le_rfl)

end Critical2DKPZ.SHF.Tsai

end
