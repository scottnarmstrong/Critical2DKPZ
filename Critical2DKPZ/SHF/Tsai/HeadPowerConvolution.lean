/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.HeadGaussian
import Mathlib.Tactic

/-! # Collision-density convolutions with general endpoint powers -/

@[expose] public section

open MeasureTheory Set
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- The scalar collision density convolved with an integrable endpoint power
has the same small-time power. This includes the head exponent
`γ = 1/2 + 1/p` for every `p > 2`. -/
theorem exists_scalarDensity_rpow_sub_lintegral_le_gen (θ T γ : ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    ∃ C rate : ℝ, 0 < C ∧ 0 < rate ∧ ∀ t : ℝ, 0 < t → t ≤ T →
      (∫⁻ r in Ioo 0 t,
        ENNReal.ofReal (scalarDensity θ r) * ENNReal.ofReal ((t - r) ^ (-γ))) ≤
        ENNReal.ofReal (C * Real.exp (rate * t) * t ^ (-γ)) := by
  obtain ⟨C₀, c₀, hC₀, hc₀, hscalar⟩ := exists_scalarDensity_le_envelope θ
  let D : ℝ := 4 * max T 1 / (Real.log (1 / 2 : ℝ)) ^ 2
  let r₀ : ℝ := Real.exp (θ + 1)
  let rate : ℝ := max r₀ c₀
  let C : ℝ := 2 ^ γ + C₀ * D / (1 - γ)
  have hD : 0 < D := by
    dsimp [D]
    apply div_pos
    · positivity
    · exact sq_pos_of_ne_zero (by
        have hlog : Real.log (1 / 2 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
        exact ne_of_lt hlog)
  have hr₀ : 0 < r₀ := by dsimp [r₀]; positivity
  have hrate : 0 < rate := lt_of_lt_of_le hr₀ (le_max_left _ _)
  have hden : 0 < 1 - γ := by linarith
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, rate, hC, hrate, ?_⟩
  intro t ht htT
  have hT : 0 < T := lt_of_lt_of_le ht htT
  let J : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (scalarDensity θ r)
  let P : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal ((t - r) ^ (-γ))
  have hJm : Measurable J := by
    dsimp [J]
    exact (measurable_scalarDensity.comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hPm : Measurable P := by
    dsimp [P]
    have hm : Measurable (fun r : ℝ => (t - r, -γ)) := by fun_prop
    exact (measurable_real_rpow.comp hm).ennreal_ofReal
  have hpowInterval : IntervalIntegrable (fun u : ℝ => u ^ (-γ)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hpowInterval' : IntervalIntegrable (fun r : ℝ => (t - r) ^ (-γ)) volume 0 t := by
    have h := (hpowInterval.comp_sub_left t).symm
    simpa using h
  have hpowInt : IntegrableOn (fun r : ℝ => (t - r) ^ (-γ)) (Ioo 0 t) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith : (0 : ℝ) ≤ t)
      (by finiteness) (by finiteness)).mp hpowInterval'
  have hpowNonneg : ∀ᵐ r ∂volume.restrict (Ioo 0 t),
      0 ≤ (t - r) ^ (-γ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact Real.rpow_nonneg (sub_nonneg.mpr hr.2.le) _
  have hpowIntegral :
      (∫ r in Ioo 0 t, (t - r) ^ (-γ)) = t ^ (1 - γ) / (1 - γ) := by
    calc
      (∫ r in Ioo 0 t, (t - r) ^ (-γ)) = ∫ x in (0 : ℝ)..t, (t - x) ^ (-γ) := by
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le]
      _ = ∫ x in (0 : ℝ)..t, x ^ (-γ) := by
        rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-γ)) t]
        simp only [sub_self, sub_zero]
      _ = t ^ (1 - γ) / (1 - γ) := by
        rw [integral_rpow (Or.inl (by linarith : (-1 : ℝ) < -γ))]
        have he : -γ + 1 = 1 - γ := by ring
        rw [he]
        simp only [Real.zero_rpow (by linarith : 1 - γ ≠ 0), sub_zero]
  have hpowLintegral :
      (∫⁻ r in Ioo 0 t, P r) = ENNReal.ofReal (t ^ (1 - γ) / (1 - γ)) := by
    dsimp [P]
    exact (ofReal_integral_eq_lintegral_ofReal hpowInt hpowNonneg).symm.trans
      (congrArg ENNReal.ofReal hpowIntegral)
  have hpoint (r : ℝ) (hr : r ∈ Ioo 0 t) :
      J r * P r ≤
        ENNReal.ofReal ((t / 2) ^ (-γ)) * J r +
          ENNReal.ofReal (C₀ * D * Real.exp (c₀ * t) / t) * P r := by
    have hrpos : 0 < r := hr.1
    have hqpos : 0 < t - r := sub_pos.mpr hr.2
    have hjpos : 0 < scalarDensity θ r := scalarDensity_pos θ hrpos
    have hpPos : 0 < (t - r) ^ (-γ) := Real.rpow_pos_of_pos hqpos _
    rw [show J r = ENNReal.ofReal (scalarDensity θ r) by rfl,
      show P r = ENNReal.ofReal ((t - r) ^ (-γ)) by rfl,
      ← ENNReal.ofReal_mul hjpos.le]
    by_cases hsplit : r ≤ t / 2
    · have hqt : t / 2 ≤ t - r := by linarith
      have hpow : (t - r) ^ (-γ) ≤ (t / 2) ^ (-γ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hqt (by linarith)
      have hreal : scalarDensity θ r * (t - r) ^ (-γ) ≤
          (t / 2) ^ (-γ) * scalarDensity θ r := by
        nlinarith [mul_le_mul_of_nonneg_left hpow hjpos.le]
      calc
        ENNReal.ofReal (scalarDensity θ r * (t - r) ^ (-γ)) ≤
            ENNReal.ofReal ((t / 2) ^ (-γ) * scalarDensity θ r) :=
              ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal ((t / 2) ^ (-γ)) * J r := by
              rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
        _ ≤ _ := le_add_of_nonneg_right (by positivity)
    · have hrhalf : t / 2 < r := lt_of_not_ge hsplit
      have henv := hscalar θ r le_rfl hrpos
      have henv' : collisionTimeEnvelope r ≤ D / t := by
        simpa [D] using collisionTimeEnvelope_le_div hT ht htT hrhalf
      have hexp : Real.exp (c₀ * r) ≤ Real.exp (c₀ * t) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr.2.le hc₀.le)
      have hJreal : scalarDensity θ r ≤ C₀ * D * Real.exp (c₀ * t) / t := by
        calc
          scalarDensity θ r ≤ C₀ * collisionTimeEnvelope r * Real.exp (c₀ * r) := henv
          _ ≤ C₀ * (D / t) * Real.exp (c₀ * t) := by gcongr
          _ = C₀ * D * Real.exp (c₀ * t) / t := by ring
      have hreal : scalarDensity θ r * (t - r) ^ (-γ) ≤
          (C₀ * D * Real.exp (c₀ * t) / t) * (t - r) ^ (-γ) :=
        mul_le_mul_of_nonneg_right hJreal hpPos.le
      calc
        ENNReal.ofReal (scalarDensity θ r * (t - r) ^ (-γ)) ≤
            ENNReal.ofReal ((C₀ * D * Real.exp (c₀ * t) / t) *
              (t - r) ^ (-γ)) := ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal (C₀ * D * Real.exp (c₀ * t) / t) * P r := by
              rw [← ENNReal.ofReal_mul (by positivity)]
        _ ≤ _ := le_add_of_nonneg_left (by positivity)
  have hlintegral :
      (∫⁻ r in Ioo 0 t, J r * P r) ≤
        ENNReal.ofReal ((t / 2) ^ (-γ)) * (∫⁻ r in Ioo 0 t, J r) +
          ENNReal.ofReal (C₀ * D * Real.exp (c₀ * t) / t) *
            (∫⁻ r in Ioo 0 t, P r) := by
    calc
      _ ≤ ∫⁻ r in Ioo 0 t,
          ENNReal.ofReal ((t / 2) ^ (-γ)) * J r +
            ENNReal.ofReal (C₀ * D * Real.exp (c₀ * t) / t) * P r := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
              exact hpoint r hr
      _ = _ := by
        rw [lintegral_add_left (hJm.const_mul _),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hJbound :
      (∫⁻ r in Ioo 0 t, J r) ≤ ENNReal.ofReal (Real.exp (r₀ * t)) := by
    simpa [J, r₀] using (lintegral_scalarDensity_Ioo_le (θ := θ) (h := t))
  have hfirstScale :
      (t / 2) ^ (-γ) = 2 ^ γ * t ^ (-γ) := by
    rw [Real.div_rpow ht.le (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg ht.le,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [div_eq_mul_inv, inv_inv]
    ring
  have htime : (1 / t) * (t ^ (1 - γ) / (1 - γ)) =
      (1 / (1 - γ)) * t ^ (-γ) := by
    have hInv : 1 / t = t ^ (-1 : ℝ) := by
      rw [one_div]
      symm
      rw [Real.rpow_neg ht.le, Real.rpow_one]
    rw [hInv, div_eq_mul_inv]
    calc
      t ^ (-1 : ℝ) * (t ^ (1 - γ) * (1 - γ)⁻¹) =
          (t ^ (-1 : ℝ) * t ^ (1 - γ)) * (1 - γ)⁻¹ := by ring
      _ = t ^ (-1 + (1 - γ)) * (1 - γ)⁻¹ := by rw [← Real.rpow_add ht]
      _ = t ^ (-γ) * (1 - γ)⁻¹ := by rw [show -1 + (1 - γ) = -γ by ring]
      _ = (1 / (1 - γ)) * t ^ (-γ) := by rw [one_div]; ac_rfl
  have hExp₁ : Real.exp (r₀ * t) ≤ Real.exp (rate * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) ht.le)
  have hExp₂ : Real.exp (c₀ * t) ≤ Real.exp (rate * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) ht.le)
  have hsecondNonneg :
      0 ≤ C₀ * D / (1 - γ) * Real.exp (rate * t) * t ^ (-γ) := by
    apply mul_nonneg
    · apply mul_nonneg
      · exact div_nonneg (mul_nonneg hC₀.le hD.le) hden.le
      · exact Real.exp_nonneg _
    · exact Real.rpow_nonneg ht.le _
  have hsumBound :
      (∫⁻ r in Ioo 0 t, J r * P r) ≤
        ENNReal.ofReal (C * Real.exp (rate * t) * t ^ (-γ)) := by
    calc
      _ ≤ ENNReal.ofReal ((t / 2) ^ (-γ)) * ENNReal.ofReal (Real.exp (r₀ * t)) +
          ENNReal.ofReal (C₀ * D * Real.exp (c₀ * t) / t) *
            ENNReal.ofReal (t ^ (1 - γ) / (1 - γ)) := by
              calc
                _ ≤ _ := hlintegral
                _ ≤ _ := by
                  rw [hpowLintegral]
                  gcongr
      _ ≤ ENNReal.ofReal (2 ^ γ * Real.exp (rate * t) * t ^ (-γ)) +
          ENNReal.ofReal (C₀ * D / (1 - γ) * Real.exp (rate * t) * t ^ (-γ)) := by
            apply add_le_add
            · calc
                _ = ENNReal.ofReal ((t / 2) ^ (-γ) * Real.exp (r₀ * t)) := by
                      rw [← ENNReal.ofReal_mul (by positivity)]
                _ ≤ ENNReal.ofReal (2 ^ γ * Real.exp (rate * t) * t ^ (-γ)) := by
                      apply ENNReal.ofReal_le_ofReal
                      rw [hfirstScale]
                      calc
                        2 ^ γ * t ^ (-γ) * Real.exp (r₀ * t) =
                            (2 ^ γ * t ^ (-γ)) * Real.exp (r₀ * t) := by ring
                        _ ≤ (2 ^ γ * t ^ (-γ)) * Real.exp (rate * t) :=
                          mul_le_mul_of_nonneg_left hExp₁
                            (mul_nonneg (by positivity) (Real.rpow_nonneg ht.le _))
                        _ = 2 ^ γ * Real.exp (rate * t) * t ^ (-γ) := by ring
            · calc
                _ = ENNReal.ofReal
                    (C₀ * D * Real.exp (c₀ * t) / t * (t ^ (1 - γ) / (1 - γ))) := by
                      rw [← ENNReal.ofReal_mul (by positivity)]
                _ ≤ ENNReal.ofReal
                    (C₀ * D / (1 - γ) * Real.exp (rate * t) * t ^ (-γ)) := by
                      apply ENNReal.ofReal_le_ofReal
                      calc
                        C₀ * D * Real.exp (c₀ * t) / t *
                              (t ^ (1 - γ) / (1 - γ)) =
                            (C₀ * D * (1 / t * (t ^ (1 - γ) / (1 - γ)))) *
                              Real.exp (c₀ * t) := by ring
                        _ = (C₀ * D * (1 / (1 - γ) * t ^ (-γ))) *
                              Real.exp (c₀ * t) := by rw [htime]
                        _ ≤ (C₀ * D * (1 / (1 - γ) * t ^ (-γ))) *
                              Real.exp (rate * t) :=
                          mul_le_mul_of_nonneg_left hExp₂ (by positivity)
                        _ = C₀ * D / (1 - γ) * Real.exp (rate * t) * t ^ (-γ) := by ring
      _ = ENNReal.ofReal (C * Real.exp (rate * t) * t ^ (-γ)) := by
            rw [← ENNReal.ofReal_add (by positivity) hsecondNonneg]
            congr 1
            dsimp [C]
            ring
  simpa [J, P] using hsumBound

end Critical2DKPZ.SHF.Tsai

end
