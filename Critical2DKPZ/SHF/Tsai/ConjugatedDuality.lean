/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.WeightedFormBound
import Mathlib.Tactic

/-! # Positive duality for conjugated kernel composition -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Cancelling the finite conjugate power in a positive duality estimate. -/
theorem ennreal_root_le_of_le_mul_conjugate {p : ℝ} (hp : 1 < p)
    {L C : ℝ≥0∞} (hL : L ≠ ⊤)
    (h : L ≤ C * L ^ (1 / (p / (p - 1)) : ℝ)) : L ^ (1 / p : ℝ) ≤ C := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq0 : 0 < 1 / (p / (p - 1)) := by positivity
  have hsum : (1 / p : ℝ) + 1 / (p / (p - 1)) = 1 := by
    field_simp
    ring
  by_cases hz : L = 0
  · rw [hz, ENNReal.zero_rpow_of_pos (by positivity : 0 < 1 / p)]
    exact bot_le
  · have hR0 : L ^ (1 / (p / (p - 1)) : ℝ) ≠ 0 := by
      exact (ENNReal.rpow_eq_zero_iff_of_pos hq0).not.mpr hz
    have hRt : L ^ (1 / (p / (p - 1)) : ℝ) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg hq0.le hL
    apply (ENNReal.mul_le_mul_iff_left hR0 hRt).mp
    calc
      L ^ (1 / p : ℝ) * L ^ (1 / (p / (p - 1)) : ℝ) = L := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ (by positivity) hq0.le, hsum,
          ENNReal.rpow_one]
      _ ≤ C * L ^ (1 / (p / (p - 1)) : ℝ) := h

/-- A bounded truncation of a positive function inherits the norm bound from all
positive dual tests. The finite-support assumption makes the cancellation legitimate. -/
theorem lintegral_trunc_rpow_le_of_dual {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {p : ℝ} (hp : 1 < p) {B : X → ℝ≥0∞} (hB : Measurable B)
    {C : ℝ≥0∞}
    (hpair : ∀ g : X → ℝ≥0∞, Measurable g →
      (∫⁻ x, g x * B x ∂μ) ≤
        C * (∫⁻ x, g x ^ (p / (p - 1)) ∂μ) ^ (1 / (p / (p - 1)) : ℝ))
    (s : Set X) (hs : MeasurableSet s) (hsμ : μ s < ⊤) (k : ℕ) :
    (∫⁻ x, (s.indicator (fun x => min (B x) (k : ℝ≥0∞)) x) ^ p ∂μ) ^ (1 / p : ℝ) ≤ C := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpm : 0 < p - 1 := sub_pos.mpr hp
  let b : X → ℝ≥0∞ := s.indicator (fun x => min (B x) (k : ℝ≥0∞))
  have hb : Measurable b := (hB.min measurable_const).indicator hs
  have hbB (x : X) : b x ≤ B x := by
    by_cases hx : x ∈ s
    · simpa only [b, indicator_of_mem hx] using min_le_left (B x) (k : ℝ≥0∞)
    · simp only [b, indicator_of_notMem hx]; exact bot_le
  let L : ℝ≥0∞ := ∫⁻ x, b x ^ p ∂μ
  have hLt : L ≠ ⊤ := by
    have hbound : L ≤ (k : ℝ≥0∞) ^ p * μ s := by
      calc
        L ≤ ∫⁻ x, s.indicator (fun _ => (k : ℝ≥0∞) ^ p) x ∂μ := by
          apply lintegral_mono
          intro x
          by_cases hx : x ∈ s
          · simp only [b, indicator_of_mem hx]
            exact ENNReal.rpow_le_rpow (min_le_right _ _) hp0.le
          · simp only [b, indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hp0]
            exact le_rfl
        _ = (k : ℝ≥0∞) ^ p * μ s := by rw [lintegral_indicator hs, setLIntegral_const]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hp0.le (ENNReal.natCast_ne_top k)) hsμ.ne) hbound
  have htest (x : X) : (b x ^ (p - 1)) ^ (p / (p - 1)) = b x ^ p := by
    rw [← ENNReal.rpow_mul]
    congr 1
    field_simp
  have hlower : L ≤ ∫⁻ x, b x ^ (p - 1) * B x ∂μ := by
    apply lintegral_mono
    intro x
    calc
      b x ^ p = b x ^ (p - 1) * b x := by
        calc
          b x ^ p = b x ^ ((p - 1) + 1) := by congr 1; ring
          _ = b x ^ (p - 1) * b x := by
            rw [ENNReal.rpow_add_of_nonneg _ _ hpm.le zero_le_one, ENNReal.rpow_one]
      _ ≤ b x ^ (p - 1) * B x := mul_le_mul' le_rfl (hbB x)
  apply ennreal_root_le_of_le_mul_conjugate hp hLt
  calc
    L ≤ ∫⁻ x, b x ^ (p - 1) * B x ∂μ := hlower
    _ ≤ C * (∫⁻ x, (b x ^ (p - 1)) ^ (p / (p - 1)) ∂μ) ^ (1 / (p / (p - 1)) : ℝ) :=
      hpair _ (hb.pow_const _)
    _ = C * L ^ (1 / (p / (p - 1)) : ℝ) := by simp_rw [htest]; rfl

/-- Positive `Lᵖ` duality on a sigma-finite measure, including infinite-valued
functions and constants. Bounded tests on finite sets justify every cancellation. -/
theorem lintegral_rpow_root_le_of_dual {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] {p : ℝ} (hp : 1 < p)
    {B : X → ℝ≥0∞} (hB : Measurable B) {C : ℝ≥0∞}
    (hpair : ∀ g : X → ℝ≥0∞, Measurable g →
      (∫⁻ x, g x * B x ∂μ) ≤
        C * (∫⁻ x, g x ^ (p / (p - 1)) ∂μ) ^ (1 / (p / (p - 1)) : ℝ)) :
    (∫⁻ x, B x ^ p ∂μ) ^ (1 / p : ℝ) ≤ C := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hbound : (∫⁻ x, B x ^ p ∂μ) ≤ C ^ p := by
    apply lintegral_le_of_forall_fin_meas_le
    intro s hs hsμ
    let F : ℕ → X → ℝ≥0∞ := fun k x =>
      (s.indicator (fun x => min (B x) (k : ℝ≥0∞)) x) ^ p
    have hFm (k : ℕ) : Measurable (F k) :=
      ((hB.min measurable_const).indicator hs).pow_const p
    have hmono : Monotone F := by
      intro k l hkl x
      apply ENNReal.rpow_le_rpow _ hp0.le
      apply indicator_le_indicator
      exact min_le_min_left _ (by exact_mod_cast hkl)
    have hsup (x : X) : (⨆ k, F k x) = s.indicator (fun x => B x ^ p) x := by
      by_cases hx : x ∈ s
      · simp only [F, indicator_of_mem hx]
        have hm : (⨆ k : ℕ, min (B x) (k : ℝ≥0∞)) = B x := by
          rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
        have he := (ENNReal.orderIsoRpow p hp0).map_iSup
          (fun k : ℕ => min (B x) (k : ℝ≥0∞))
        simpa only [ENNReal.orderIsoRpow_apply, hm] using he.symm
      · simp only [F, indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hp0, iSup_const]
    calc
      (∫⁻ x in s, B x ^ p ∂μ) = ∫⁻ x, ⨆ k, F k x ∂μ := by
        rw [← lintegral_indicator hs]
        exact lintegral_congr (fun x => (hsup x).symm)
      _ = ⨆ k, ∫⁻ x, F k x ∂μ := lintegral_iSup hFm hmono
      _ ≤ C ^ p := by
        apply iSup_le
        intro k
        have h := lintegral_trunc_rpow_le_of_dual μ hp hB hpair s hs
          (lt_top_iff_ne_top.mpr hsμ) k
        have hpow := ENNReal.rpow_le_rpow h hp0.le
        simpa only [F, ← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne',
          ENNReal.rpow_one] using hpow
  calc
    _ ≤ (C ^ p) ^ (1 / p : ℝ) := ENNReal.rpow_le_rpow hbound (by positivity)
    _ = C := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

end Critical2DKPZ.SHF.Tsai

end
