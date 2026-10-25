/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.HeadPowerConvolution
public import Critical2DKPZ.SHF.Tsai.Tech
import Mathlib.Tactic

/-! # Scalar time convolutions for head bounds

Convolving the scalar collision density with the two endpoint powers gives a bound of
order `e^{rate t} t^{1/2 - 2/p}` on bounded positive-time intervals.
-/

@[expose] public section

open MeasureTheory Set Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- The integral of a nonnegative endpoint power on a finite interval. -/
theorem lintegral_ofReal_rpow_Ioo {t b : ℝ} (ht : 0 < t) (hb : -1 < b) :
    (∫⁻ x in Ioo 0 t, ENNReal.ofReal (x ^ b)) =
      ENNReal.ofReal (t ^ (b + 1) / (b + 1)) := by
  have hInt : IntegrableOn (fun x : ℝ => x ^ b) (Ioo 0 t) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff ht).2 hb
  have hNonneg : ∀ᵐ x ∂volume.restrict (Ioo 0 t), 0 ≤ x ^ b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact Real.rpow_nonneg hx.1.le _
  have hIntegral : (∫ x in Ioo 0 t, x ^ b) = t ^ (b + 1) / (b + 1) := by
    calc
      (∫ x in Ioo 0 t, x ^ b) = ∫ x in (0 : ℝ)..t, x ^ b := by
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le]
      _ = t ^ (b + 1) / (b + 1) := by
        rw [integral_rpow (Or.inl hb)]
        simp only [Real.zero_rpow (by linarith : b + 1 ≠ 0), sub_zero]
  exact (ofReal_integral_eq_lintegral_ofReal hInt hNonneg).symm.trans
    (congrArg ENNReal.ofReal hIntegral)

/-- The same endpoint-power integral after reversing the interval. -/
theorem lintegral_ofReal_rpow_sub_Ioo {t b : ℝ} (ht : 0 < t) (hb : -1 < b) :
    (∫⁻ x in Ioo 0 t, ENNReal.ofReal ((t - x) ^ b)) =
      ENNReal.ofReal (t ^ (b + 1) / (b + 1)) := by
  have hInt : IntegrableOn (fun x : ℝ => (t - x) ^ b) (Ioo 0 t) := by
    have hpow : IntervalIntegrable (fun x : ℝ => x ^ b) volume 0 t :=
      intervalIntegral.intervalIntegrable_rpow' hb
    have hrev : IntervalIntegrable (fun x : ℝ => (t - x) ^ b) volume 0 t := by
      simpa using (hpow.comp_sub_left t).symm
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le
      (by finiteness) (by finiteness)).mp hrev
  have hNonneg : ∀ᵐ x ∂volume.restrict (Ioo 0 t), 0 ≤ (t - x) ^ b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact Real.rpow_nonneg (sub_nonneg.mpr hx.2.le) _
  have hIntegral : (∫ x in Ioo 0 t, (t - x) ^ b) = t ^ (b + 1) / (b + 1) := by
    calc
      (∫ x in Ioo 0 t, (t - x) ^ b) = ∫ x in (0 : ℝ)..t, (t - x) ^ b := by
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le]
      _ = ∫ x in (0 : ℝ)..t, x ^ b := by
        rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ b) t]
        simp only [sub_self, sub_zero]
      _ = t ^ (b + 1) / (b + 1) := by
        rw [integral_rpow (Or.inl hb)]
        simp only [Real.zero_rpow (by linarith : b + 1 ≠ 0), sub_zero]
  exact (ofReal_integral_eq_lintegral_ofReal hInt hNonneg).symm.trans
    (congrArg ENNReal.ofReal hIntegral)

/-- Convolving scalar collision density with the two powers appearing in a
head step gives the time exponent `1/2 - 2/p`. This scalar estimate is the
time-simplex input to `weightedFormBound_headKernel`. -/
theorem exists_scalarDensity_head_time_lintegral_bound (θ T p : ℝ) (hp : 2 < p) :
    ∃ C rate : ℝ, 0 < C ∧ 0 < rate ∧ ∀ t : ℝ, 0 < t → t ≤ T →
      (∫⁻ r in Ioo 0 t, ENNReal.ofReal (r ^ (-1 / p)) *
        (∫⁻ u in Ioo 0 (t - r),
          ENNReal.ofReal (scalarDensity θ u) *
            ENNReal.ofReal ((t - r - u) ^ (-(1 / 2 + 1 / p : ℝ))))) ≤
        ENNReal.ofReal (C * Real.exp (rate * t) * t ^ (1 / 2 - 2 / p)) := by
  let γ : ℝ := 1 / 2 + 1 / p
  let b : ℝ := -1 / p
  have hp0 : 0 < p := by linarith
  have hpInvLtOne : 1 / p < 1 := by
    simpa using one_div_lt_one_div_of_lt zero_lt_one (by linarith : (1 : ℝ) < p)
  have hb : -1 < b := by
    dsimp [b]
    rw [neg_div]
    exact (neg_lt_neg_iff).2 hpInvLtOne
  have hb0 : b < 0 := by
    dsimp [b]
    rw [neg_div]
    exact neg_lt_zero.mpr (one_div_pos.mpr hp0)
  have hγ0 : 0 ≤ γ := by dsimp [γ]; positivity
  have hγ1 : γ < 1 := by
    dsimp [γ]
    have hpInv : 1 / p < 1 / 2 := one_div_lt_one_div_of_lt zero_lt_two hp
    linarith
  have hdenb : 0 < b + 1 := by linarith
  have hdenγ : 0 < 1 - γ := by linarith
  obtain ⟨C₀, rate, hC₀, hrate, hinner⟩ :=
    exists_scalarDensity_rpow_sub_lintegral_le_gen θ T γ hγ0 hγ1
  let B : ℝ := 2 ^ γ / (b + 1) + 2 ^ (1 / p) / (1 - γ)
  have hB : 0 < B := by dsimp [B]; positivity
  let C : ℝ := C₀ * B
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, rate, hC, hrate, ?_⟩
  intro t ht htT
  have hpow1 := lintegral_ofReal_rpow_Ioo ht hb
  have hpow2 := lintegral_ofReal_rpow_sub_Ioo ht (by linarith : -1 < -γ)
  have hscale1 : (t / 2) ^ (-γ) = 2 ^ γ * t ^ (-γ) := by
    rw [Real.div_rpow ht.le (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg ht.le,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [div_eq_mul_inv, inv_inv]
    ring
  have hscale2 : (t / 2) ^ b = 2 ^ (1 / p) * t ^ b := by
    dsimp [b]
    rw [neg_div, Real.div_rpow ht.le (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.rpow_neg ht.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [div_eq_mul_inv, inv_inv]
    ac_rfl
  have hfactor :
      (∫⁻ r in Ioo 0 t,
        ENNReal.ofReal (r ^ b) * ENNReal.ofReal ((t - r) ^ (-γ))) ≤
        ENNReal.ofReal (B * t ^ (b + 1 - γ)) := by
    have hpoint (r : ℝ) (hr : r ∈ Ioo 0 t) :
        ENNReal.ofReal (r ^ b) * ENNReal.ofReal ((t - r) ^ (-γ)) ≤
          ENNReal.ofReal ((2 ^ γ * t ^ (-γ)) * r ^ b) +
            ENNReal.ofReal ((2 ^ (1 / p) * t ^ b) * (t - r) ^ (-γ)) := by
      have hrpos : 0 < r := hr.1
      have htrpos : 0 < t - r := sub_pos.mpr hr.2
      have hpowr : 0 < r ^ b := Real.rpow_pos_of_pos hrpos _
      have hpowtr : 0 < (t - r) ^ (-γ) := Real.rpow_pos_of_pos htrpos _
      rw [← ENNReal.ofReal_mul hpowr.le]
      by_cases hhalf : r ≤ t / 2
      · have htr : t / 2 ≤ t - r := by linarith
        have hpow : (t - r) ^ (-γ) ≤ (t / 2) ^ (-γ) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) htr (neg_nonpos.mpr hγ0)
        rw [hscale1] at hpow
        have hreal : r ^ b * (t - r) ^ (-γ) ≤
            (2 ^ γ * t ^ (-γ)) * r ^ b := by
          calc
            r ^ b * (t - r) ^ (-γ) ≤ r ^ b * (2 ^ γ * t ^ (-γ)) :=
              mul_le_mul_of_nonneg_left hpow hpowr.le
            _ = _ := by ring
        calc
          ENNReal.ofReal (r ^ b * (t - r) ^ (-γ)) ≤
              ENNReal.ofReal ((2 ^ γ * t ^ (-γ)) * r ^ b) := ENNReal.ofReal_le_ofReal hreal
          _ ≤ _ := le_add_of_nonneg_right (by positivity)
      · have hrhalf : t / 2 < r := lt_of_not_ge hhalf
        have hpow : r ^ b ≤ (t / 2) ^ b :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (le_of_lt hrhalf) hb0.le
        rw [hscale2] at hpow
        have hreal : r ^ b * (t - r) ^ (-γ) ≤
            (2 ^ (1 / p) * t ^ b) * (t - r) ^ (-γ) :=
          mul_le_mul_of_nonneg_right hpow hpowtr.le
        calc
          ENNReal.ofReal (r ^ b * (t - r) ^ (-γ)) ≤
              ENNReal.ofReal ((2 ^ (1 / p) * t ^ b) * (t - r) ^ (-γ)) :=
                ENNReal.ofReal_le_ofReal hreal
          _ ≤ _ := le_add_of_nonneg_left (by positivity)
    calc
      _ ≤ ∫⁻ r in Ioo 0 t,
          ENNReal.ofReal ((2 ^ γ * t ^ (-γ)) * r ^ b) +
            ENNReal.ofReal ((2 ^ (1 / p) * t ^ b) * (t - r) ^ (-γ)) := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
              exact hpoint r hr
      _ = ENNReal.ofReal (2 ^ γ * t ^ (-γ)) *
            (∫⁻ r in Ioo 0 t, ENNReal.ofReal (r ^ b)) +
          ENNReal.ofReal (2 ^ (1 / p) * t ^ b) *
            (∫⁻ r in Ioo 0 t, ENNReal.ofReal ((t - r) ^ (-γ))) := by
              have hpoint' (r : ℝ) :
                  ENNReal.ofReal (2 ^ γ * t ^ (-γ) * r ^ b) +
                    ENNReal.ofReal (2 ^ (1 / p) * t ^ b * (t - r) ^ (-γ)) =
                  ENNReal.ofReal (2 ^ γ * t ^ (-γ)) * ENNReal.ofReal (r ^ b) +
                    ENNReal.ofReal (2 ^ (1 / p) * t ^ b) *
                      ENNReal.ofReal ((t - r) ^ (-γ)) := by
                have hA' : 0 ≤ 2 ^ γ * t ^ (-γ) := by positivity
                have hB' : 0 ≤ 2 ^ (1 / p) * t ^ b := by positivity
                exact congrArg₂ (fun x y : ℝ≥0∞ => x + y)
                  (ENNReal.ofReal_mul (p := 2 ^ γ * t ^ (-γ)) (q := r ^ b) hA')
                  (ENNReal.ofReal_mul (p := 2 ^ (1 / p) * t ^ b)
                    (q := (t - r) ^ (-γ)) hB')
              have hm1 : Measurable (fun r : ℝ => ENNReal.ofReal (r ^ b)) := by
                have hm : Measurable (fun r : ℝ => (r, b)) := by fun_prop
                exact (measurable_real_rpow.comp hm).ennreal_ofReal
              have hm2 : Measurable (fun r : ℝ => ENNReal.ofReal ((t - r) ^ (-γ))) := by
                have hm : Measurable (fun r : ℝ => (t - r, -γ)) := by fun_prop
                exact (measurable_real_rpow.comp hm).ennreal_ofReal
              calc
                _ = ∫⁻ r in Ioo 0 t,
                    ENNReal.ofReal (2 ^ γ * t ^ (-γ)) * ENNReal.ofReal (r ^ b) +
                      ENNReal.ofReal (2 ^ (1 / p) * t ^ b) *
                        ENNReal.ofReal ((t - r) ^ (-γ)) := by
                    apply lintegral_congr_ae
                    filter_upwards [] with r
                    exact hpoint' r
                _ = _ := by
                  let f : ℝ → ℝ≥0∞ := fun r =>
                    ENNReal.ofReal (2 ^ γ * t ^ (-γ)) * ENNReal.ofReal (r ^ b)
                  let g : ℝ → ℝ≥0∞ := fun r =>
                    ENNReal.ofReal (2 ^ (1 / p) * t ^ b) * ENNReal.ofReal ((t - r) ^ (-γ))
                  have hf : Measurable f := by
                    dsimp [f]
                    exact measurable_const.ennreal_ofReal.mul hm1
                  have hsplit :
                      (∫⁻ r, f r + g r ∂volume.restrict (Ioo 0 t)) =
                        (∫⁻ r, f r ∂volume.restrict (Ioo 0 t)) +
                          (∫⁻ r, g r ∂volume.restrict (Ioo 0 t)) :=
                    lintegral_add_left hf g
                  rw [show (∫⁻ r in Ioo 0 t, f r + g r) =
                      ∫⁻ r, f r + g r ∂volume.restrict (Ioo 0 t) by rfl,
                    hsplit]
                  change (∫⁻ r in Ioo 0 t,
                      ENNReal.ofReal (2 ^ γ * t ^ (-γ)) * ENNReal.ofReal (r ^ b)) +
                    (∫⁻ r in Ioo 0 t,
                      ENNReal.ofReal (2 ^ (1 / p) * t ^ b) *
                        ENNReal.ofReal ((t - r) ^ (-γ))) = _
                  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
                    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal (B * t ^ (b + 1 - γ)) := by
            have hpow2' : (∫⁻ r in Ioo 0 t,
                ENNReal.ofReal ((t - r) ^ (-γ))) =
                ENNReal.ofReal (t ^ (1 - γ) / (1 - γ)) := by
              simpa [show -γ + 1 = 1 - γ by ring] using hpow2
            rw [hpow1, hpow2']
            have htime1 : t ^ (-γ) * (t ^ (b + 1) / (b + 1)) =
                (1 / (b + 1)) * t ^ (b + 1 - γ) := by
              rw [div_eq_mul_inv]
              calc
                _ = (t ^ (-γ) * t ^ (b + 1)) * (b + 1)⁻¹ := by ring
                _ = t ^ (-γ + (b + 1)) * (b + 1)⁻¹ := by rw [← Real.rpow_add ht]
                _ = t ^ (b + 1 - γ) * (b + 1)⁻¹ := by
                  rw [show -γ + (b + 1) = b + 1 - γ by ring]
                _ = _ := by rw [one_div]; ac_rfl
            have htime2 : t ^ b * (t ^ (1 - γ) / (1 - γ)) =
                (1 / (1 - γ)) * t ^ (b + 1 - γ) := by
              rw [div_eq_mul_inv]
              calc
                _ = (t ^ b * t ^ (1 - γ)) * (1 - γ)⁻¹ := by ring
                _ = t ^ (b + (1 - γ)) * (1 - γ)⁻¹ := by rw [← Real.rpow_add ht]
                _ = t ^ (b + 1 - γ) * (1 - γ)⁻¹ := by
                  rw [show b + (1 - γ) = b + 1 - γ by ring]
                _ = _ := by rw [one_div]; ac_rfl
            have hterm1 : ENNReal.ofReal (2 ^ γ * t ^ (-γ)) *
                ENNReal.ofReal (t ^ (b + 1) / (b + 1)) =
                ENNReal.ofReal (2 ^ γ * t ^ (-γ) * (t ^ (b + 1) / (b + 1))) :=
              (ENNReal.ofReal_mul (p := 2 ^ γ * t ^ (-γ))
                (q := t ^ (b + 1) / (b + 1)) (by positivity)).symm
            have hterm2 : ENNReal.ofReal (2 ^ (1 / p) * t ^ b) *
                ENNReal.ofReal (t ^ (1 - γ) / (1 - γ)) =
                ENNReal.ofReal (2 ^ (1 / p) * t ^ b * (t ^ (1 - γ) / (1 - γ))) :=
              (ENNReal.ofReal_mul (p := 2 ^ (1 / p) * t ^ b)
                (q := t ^ (1 - γ) / (1 - γ)) (by positivity)).symm
            have hreal1 : 0 ≤ 2 ^ γ * t ^ (-γ) * (t ^ (b + 1) / (b + 1)) := by
              positivity
            have hreal2 : 0 ≤ 2 ^ (1 / p) * t ^ b * (t ^ (1 - γ) / (1 - γ)) := by
              apply mul_nonneg (by positivity)
              exact div_nonneg (Real.rpow_nonneg ht.le _) hdenγ.le
            rw [hterm1, hterm2, ← ENNReal.ofReal_add hreal1 hreal2]
            congr 1
            dsimp [B]
            have hcalc1 : 2 ^ γ * t ^ (-γ) * (t ^ (b + 1) / (b + 1)) =
                (2 ^ γ / (b + 1)) * t ^ (b + 1 - γ) := by
              calc
                _ = 2 ^ γ * (t ^ (-γ) * (t ^ (b + 1) / (b + 1))) := by ring
                _ = 2 ^ γ * ((1 / (b + 1)) * t ^ (b + 1 - γ)) := by rw [htime1]
                _ = _ := by rw [one_div]; ring
            have hcalc2 : 2 ^ (1 / p) * t ^ b * (t ^ (1 - γ) / (1 - γ)) =
                (2 ^ (1 / p) / (1 - γ)) * t ^ (b + 1 - γ) := by
              calc
                _ = 2 ^ (1 / p) * (t ^ b * (t ^ (1 - γ) / (1 - γ))) := by ring
                _ = 2 ^ (1 / p) * ((1 / (1 - γ)) * t ^ (b + 1 - γ)) := by rw [htime2]
                _ = _ := by rw [one_div]; ring
            rw [hcalc1, hcalc2]
            ring
  have hOuter (r : ℝ) (hr : r ∈ Ioo 0 t) :
      (∫⁻ u in Ioo 0 (t - r),
        ENNReal.ofReal (scalarDensity θ u) *
          ENNReal.ofReal ((t - r - u) ^ (-γ))) ≤
        ENNReal.ofReal (C₀ * Real.exp (rate * t) * (t - r) ^ (-γ)) := by
    have hδpos : 0 < t - r := sub_pos.mpr hr.2
    have hδT : t - r ≤ T := le_trans (sub_le_self t hr.1.le) htT
    have hConv := hinner (t - r) hδpos hδT
    apply le_trans hConv
    apply ENNReal.ofReal_le_ofReal
    have hExp : Real.exp (rate * (t - r)) ≤ Real.exp (rate * t) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (sub_le_self t hr.1.le) hrate.le
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hExp hC₀.le)
      (Real.rpow_nonneg hδpos.le _)
  have houterInt :
      (∫⁻ r in Ioo 0 t, ENNReal.ofReal (r ^ b) *
        (∫⁻ u in Ioo 0 (t - r),
          ENNReal.ofReal (scalarDensity θ u) *
            ENNReal.ofReal ((t - r - u) ^ (-γ)))) ≤
        ENNReal.ofReal (C₀ * Real.exp (rate * t)) *
          (∫⁻ r in Ioo 0 t,
            ENNReal.ofReal (r ^ b) * ENNReal.ofReal ((t - r) ^ (-γ))) := by
    calc
      _ ≤ ∫⁻ r in Ioo 0 t,
          ENNReal.ofReal (r ^ b) *
            ENNReal.ofReal (C₀ * Real.exp (rate * t) * (t - r) ^ (-γ)) := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
              exact mul_le_mul' le_rfl (hOuter r hr)
      _ = _ := by
        have hEq : ∀ r : ℝ, r ∈ Ioo 0 t →
            ENNReal.ofReal (r ^ b) *
              ENNReal.ofReal (C₀ * Real.exp (rate * t) * (t - r) ^ (-γ)) =
            ENNReal.ofReal (C₀ * Real.exp (rate * t)) *
              (ENNReal.ofReal (r ^ b) * ENNReal.ofReal ((t - r) ^ (-γ))) := by
          intro r hr
          calc
            _ = ENNReal.ofReal (r ^ b) *
                (ENNReal.ofReal (C₀ * Real.exp (rate * t)) *
                  ENNReal.ofReal ((t - r) ^ (-γ))) := by
                    rw [ENNReal.ofReal_mul (by positivity)]
            _ = _ := by ac_rfl
        calc
          _ = ∫⁻ r in Ioo 0 t,
              ENNReal.ofReal (C₀ * Real.exp (rate * t)) *
                (ENNReal.ofReal (r ^ b) * ENNReal.ofReal ((t - r) ^ (-γ))) := by
                  apply lintegral_congr_ae
                  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
                  exact hEq r hr
          _ = _ := by
            exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hfinal :
      ENNReal.ofReal (C₀ * Real.exp (rate * t)) *
          (∫⁻ r in Ioo 0 t,
            ENNReal.ofReal (r ^ b) * ENNReal.ofReal ((t - r) ^ (-γ))) ≤
        ENNReal.ofReal (C * Real.exp (rate * t) * t ^ (b + 1 - γ)) := by
    calc
      _ ≤ ENNReal.ofReal (C₀ * Real.exp (rate * t)) *
          ENNReal.ofReal (B * t ^ (b + 1 - γ)) := by
            exact mul_le_mul' le_rfl hfactor
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        dsimp [C]
        ring
  have hκ : b + 1 - γ = 1 / 2 - 2 / p := by
    dsimp [b, γ]
    ring
  rw [hκ] at hfinal
  simpa only [b, γ] using houterInt.trans hfinal

end Critical2DKPZ.SHF.Tsai

end
