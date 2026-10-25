/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.ClockWidthPerturbation
public import Critical2DKPZ.Smoothing.WindowWidthIntegration
public import Critical2DKPZ.Smoothing.UnitHorizonBounds
import Mathlib.Tactic

/-! # Vanishing integrated error for bounded changes of the smoothing width -/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal BoundedContinuousFunction

namespace Critical2DKPZ.Smoothing

private theorem width_raw_le_ofReal (C H F V L : ℝ)
    (hC : 0 < C) (hV : 0 ≤ V) (hL : 1 ≤ L)
    (hFexp : F = Real.exp H) :
    (ENNReal.ofReal logHolderConstant *
        ENNReal.ofReal (Real.sqrt (F ^ 2 * V ^ 2 * ((C + 1) * L))) ^ ((1 : ℝ) / 3) *
        (2 * (ENNReal.ofReal (Real.exp H * C * L) ^ ((1 : ℝ) / 3))) +
      ENNReal.ofReal logHolderConstant *
        ENNReal.ofReal (Real.sqrt (V ^ 2 * ((C + 1) * L))) ^ ((1 : ℝ) / 3) *
        (2 * (ENNReal.ofReal (C * L) ^ ((1 : ℝ) / 3)))) ≤
      ENNReal.ofReal (2 * logHolderConstant *
        ((F * (C + 1) * (Real.exp H * C)) ^ ((1 : ℝ) / 3) +
          ((C + 1) * C) ^ ((1 : ℝ) / 3)) * V ^ ((1 : ℝ) / 3) * L) := by
  have hlog : 0 < logHolderConstant := logHolderConstant_pos
  have hS : 1 ≤ (C + 1) * L := by nlinarith
  have hSpos : 0 < (C + 1) * L := lt_of_lt_of_le (by norm_num) hS
  have hF0 : 0 < F := by rw [hFexp]; exact Real.exp_pos _
  have hE0 : 0 < Real.exp H * C * L := by positivity
  have hC0 : 0 < C * L := by positivity
  have hroot₁ : Real.sqrt (F ^ 2 * V ^ 2 * ((C + 1) * L)) ≤
      F * V * ((C + 1) * L) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [mul_nonneg (sq_nonneg (F * V)) (sub_nonneg.mpr hS)]
  have hroot₂ : Real.sqrt (V ^ 2 * ((C + 1) * L)) ≤ V * ((C + 1) * L) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [mul_nonneg (sq_nonneg V) (sub_nonneg.mpr hS)]
  have hpow₁ := Real.rpow_le_rpow (Real.sqrt_nonneg _) hroot₁ (by norm_num : 0 ≤ (1 : ℝ) / 3)
  have hpow₂ := Real.rpow_le_rpow (Real.sqrt_nonneg _) hroot₂ (by norm_num : 0 ≤ (1 : ℝ) / 3)
  have hterm₁ :
      (ENNReal.ofReal logHolderConstant *
        ENNReal.ofReal (Real.sqrt (F ^ 2 * V ^ 2 * ((C + 1) * L))) ^ ((1 : ℝ) / 3) *
        (2 * (ENNReal.ofReal (Real.exp H * C * L) ^ ((1 : ℝ) / 3)))) ≤
      ENNReal.ofReal (2 * logHolderConstant *
        (F * (C + 1) * (Real.exp H * C)) ^ ((1 : ℝ) / 3) *
          V ^ ((1 : ℝ) / 3) * L) := by
    have hcollapse :
        ENNReal.ofReal logHolderConstant *
          ENNReal.ofReal (F * V * ((C + 1) * L)) ^ ((1 : ℝ) / 3) *
          (2 * (ENNReal.ofReal (Real.exp H * C * L) ^ ((1 : ℝ) / 3))) =
        ENNReal.ofReal (2 * logHolderConstant *
          (F * V * ((C + 1) * L)) ^ ((1 : ℝ) / 3) *
            (Real.exp H * C * L) ^ ((1 : ℝ) / 3)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg
          (mul_nonneg (mul_nonneg hF0.le hV) hSpos.le) (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg hE0.le (by norm_num)]
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
      calc
        _ = ENNReal.ofReal (logHolderConstant *
              (F * V * ((C + 1) * L)) ^ ((1 : ℝ) / 3)) *
            ENNReal.ofReal (2 * (Real.exp H * C * L) ^ ((1 : ℝ) / 3)) := by
              rw [← ENNReal.ofReal_mul hlog.le, ← ENNReal.ofReal_mul (by norm_num)]
        _ = ENNReal.ofReal (2 * logHolderConstant *
              (F * V * ((C + 1) * L)) ^ ((1 : ℝ) / 3) *
                (Real.exp H * C * L) ^ ((1 : ℝ) / 3)) := by
              rw [← ENNReal.ofReal_mul (by positivity)]
              congr 1
              ring
    calc
      _ ≤ ENNReal.ofReal logHolderConstant *
          ENNReal.ofReal (F * V * ((C + 1) * L)) ^ ((1 : ℝ) / 3) *
          (2 * (ENNReal.ofReal (Real.exp H * C * L) ^ ((1 : ℝ) / 3))) := by
            gcongr
      _ = _ := hcollapse
      _ ≤ ENNReal.ofReal (2 * logHolderConstant *
          (F * (C + 1) * (Real.exp H * C)) ^ ((1 : ℝ) / 3) *
            V ^ ((1 : ℝ) / 3) * L) := by
          apply ENNReal.ofReal_le_ofReal
          have hprod :
              (F * V * ((C + 1) * L)) ^ ((1 : ℝ) / 3) *
                  (Real.exp H * C * L) ^ ((1 : ℝ) / 3) =
                (F * (C + 1) * (Real.exp H * C)) ^ ((1 : ℝ) / 3) *
                  V ^ ((1 : ℝ) / 3) * L ^ ((2 : ℝ) / 3) := by
            have hfirst : (F * V * ((C + 1) * L)) ^ ((1 : ℝ) / 3) =
                (F * (C + 1)) ^ ((1 : ℝ) / 3) * V ^ ((1 : ℝ) / 3) *
                  L ^ ((1 : ℝ) / 3) := by
              rw [show F * V * ((C + 1) * L) = (F * (C + 1)) * (V * L) by ring]
              calc
                _ = (F * (C + 1)) ^ ((1 : ℝ) / 3) * (V * L) ^ ((1 : ℝ) / 3) :=
                  Real.mul_rpow (by positivity) (by positivity)
                _ = _ := by rw [Real.mul_rpow hV (by positivity)]; ring
            have hsecond : (Real.exp H * C * L) ^ ((1 : ℝ) / 3) =
                (Real.exp H * C) ^ ((1 : ℝ) / 3) * L ^ ((1 : ℝ) / 3) := by
              rw [show Real.exp H * C * L = (Real.exp H * C) * L by ring,
                Real.mul_rpow (by positivity) (by positivity)]
            rw [hfirst, hsecond]
            calc
              _ = ((F * (C + 1)) ^ ((1 : ℝ) / 3) *
                    (Real.exp H * C) ^ ((1 : ℝ) / 3)) *
                    (V ^ ((1 : ℝ) / 3) *
                      (L ^ ((1 : ℝ) / 3) * L ^ ((1 : ℝ) / 3))) := by ring
              _ = ((F * (C + 1)) * (Real.exp H * C)) ^ ((1 : ℝ) / 3) *
                    V ^ ((1 : ℝ) / 3) * L ^ ((2 : ℝ) / 3) := by
                rw [← Real.mul_rpow (by positivity) (by positivity),
                  ← Real.rpow_add (by positivity : 0 < L)]
                rw [show (1 : ℝ) / 3 + (1 : ℝ) / 3 = (2 : ℝ) / 3 by norm_num]
                ring
          have hLpow : L ^ ((2 : ℝ) / 3) ≤ L := by
            simpa only [Real.rpow_one] using
              Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (2 : ℝ) / 3 ≤ 1)
          have hbasepow : 0 ≤ (F * (C + 1) * (Real.exp H * C)) ^ ((1 : ℝ) / 3) := by positivity
          have hVpow : 0 ≤ V ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hV _
          calc
            _ = 2 * logHolderConstant *
                ((F * V * ((C + 1) * L)) ^ ((1 : ℝ) / 3) *
                  (Real.exp H * C * L) ^ ((1 : ℝ) / 3)) := by ring
            _ = 2 * logHolderConstant *
                (F * (C + 1) * (Real.exp H * C)) ^ ((1 : ℝ) / 3) *
                  V ^ ((1 : ℝ) / 3) * L ^ ((2 : ℝ) / 3) := by rw [hprod]; ring
            _ ≤ 2 * logHolderConstant *
                (F * (C + 1) * (Real.exp H * C)) ^ ((1 : ℝ) / 3) *
                  V ^ ((1 : ℝ) / 3) * L := by
                  gcongr
  have hterm₂ :
      (ENNReal.ofReal logHolderConstant *
        ENNReal.ofReal (Real.sqrt (V ^ 2 * ((C + 1) * L))) ^ ((1 : ℝ) / 3) *
        (2 * (ENNReal.ofReal (C * L) ^ ((1 : ℝ) / 3)))) ≤
      ENNReal.ofReal (2 * logHolderConstant *
        ((C + 1) * C) ^ ((1 : ℝ) / 3) * V ^ ((1 : ℝ) / 3) * L) := by
    have hcollapse :
        ENNReal.ofReal logHolderConstant *
          ENNReal.ofReal (V * ((C + 1) * L)) ^ ((1 : ℝ) / 3) *
          (2 * (ENNReal.ofReal (C * L) ^ ((1 : ℝ) / 3))) =
        ENNReal.ofReal (2 * logHolderConstant *
          (V * ((C + 1) * L)) ^ ((1 : ℝ) / 3) * (C * L) ^ ((1 : ℝ) / 3)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hV hSpos.le) (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg hC0.le (by norm_num)]
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
      calc
        _ = ENNReal.ofReal (logHolderConstant *
              (V * ((C + 1) * L)) ^ ((1 : ℝ) / 3)) *
            ENNReal.ofReal (2 * (C * L) ^ ((1 : ℝ) / 3)) := by
              rw [← ENNReal.ofReal_mul hlog.le, ← ENNReal.ofReal_mul (by norm_num)]
        _ = ENNReal.ofReal (2 * logHolderConstant *
              (V * ((C + 1) * L)) ^ ((1 : ℝ) / 3) * (C * L) ^ ((1 : ℝ) / 3)) := by
              rw [← ENNReal.ofReal_mul (by positivity)]
              congr 1
              ring
    calc
      _ ≤ ENNReal.ofReal logHolderConstant *
          ENNReal.ofReal (V * ((C + 1) * L)) ^ ((1 : ℝ) / 3) *
          (2 * (ENNReal.ofReal (C * L) ^ ((1 : ℝ) / 3))) := by
            gcongr
      _ = _ := hcollapse
      _ ≤ ENNReal.ofReal (2 * logHolderConstant *
          ((C + 1) * C) ^ ((1 : ℝ) / 3) * V ^ ((1 : ℝ) / 3) * L) := by
          apply ENNReal.ofReal_le_ofReal
          have hprod :
              (V * ((C + 1) * L)) ^ ((1 : ℝ) / 3) * (C * L) ^ ((1 : ℝ) / 3) =
                ((C + 1) * C) ^ ((1 : ℝ) / 3) *
                  V ^ ((1 : ℝ) / 3) * L ^ ((2 : ℝ) / 3) := by
            have hfirst : (V * ((C + 1) * L)) ^ ((1 : ℝ) / 3) =
                (C + 1) ^ ((1 : ℝ) / 3) * V ^ ((1 : ℝ) / 3) *
                  L ^ ((1 : ℝ) / 3) := by
              rw [show V * ((C + 1) * L) = (C + 1) * (V * L) by ring]
              calc
                _ = (C + 1) ^ ((1 : ℝ) / 3) * (V * L) ^ ((1 : ℝ) / 3) :=
                  Real.mul_rpow (by positivity) (by positivity)
                _ = _ := by rw [Real.mul_rpow hV (by positivity)]; ring
            have hsecond : (C * L) ^ ((1 : ℝ) / 3) =
                C ^ ((1 : ℝ) / 3) * L ^ ((1 : ℝ) / 3) := by
              rw [Real.mul_rpow (by positivity) (by positivity)]
            rw [hfirst, hsecond]
            calc
              _ = (C + 1) ^ ((1 : ℝ) / 3) * C ^ ((1 : ℝ) / 3) *
                    V ^ ((1 : ℝ) / 3) *
                      (L ^ ((1 : ℝ) / 3) * L ^ ((1 : ℝ) / 3)) := by ring
              _ = ((C + 1) * C) ^ ((1 : ℝ) / 3) *
                    V ^ ((1 : ℝ) / 3) * L ^ ((2 : ℝ) / 3) := by
                rw [← Real.mul_rpow (by positivity) (by positivity),
                  ← Real.rpow_add (by positivity : 0 < L)]
                rw [show (1 : ℝ) / 3 + (1 : ℝ) / 3 = (2 : ℝ) / 3 by norm_num]
          have hLpow : L ^ ((2 : ℝ) / 3) ≤ L := by
            simpa only [Real.rpow_one] using
              Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (2 : ℝ) / 3 ≤ 1)
          have hbasepow : 0 ≤ ((C + 1) * C) ^ ((1 : ℝ) / 3) := by positivity
          have hVpow : 0 ≤ V ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hV _
          calc
            _ = 2 * logHolderConstant *
                ((V * ((C + 1) * L)) ^ ((1 : ℝ) / 3) *
                  (C * L) ^ ((1 : ℝ) / 3)) := by ring
            _ = 2 * logHolderConstant *
                ((C + 1) * C) ^ ((1 : ℝ) / 3) * V ^ ((1 : ℝ) / 3) *
                  L ^ ((2 : ℝ) / 3) := by rw [hprod]; ring
            _ ≤ 2 * logHolderConstant *
                ((C + 1) * C) ^ ((1 : ℝ) / 3) * V ^ ((1 : ℝ) / 3) * L := by
                  gcongr
  calc
    _ ≤ ENNReal.ofReal (2 * logHolderConstant *
        (F * (C + 1) * (Real.exp H * C)) ^ ((1 : ℝ) / 3) *
          V ^ ((1 : ℝ) / 3) * L) +
      ENNReal.ofReal (2 * logHolderConstant * ((C + 1) * C) ^ ((1 : ℝ) / 3) *
        V ^ ((1 : ℝ) / 3) * L) := add_le_add hterm₁ hterm₂
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- The centered profile-log comparison has a uniform bound in terms of the collision variation,
with the square-root and fractional-power factors simplified to one real expression. -/
theorem eLpNorm_centered_log_walkKernel_profile_difference_le_simplified_collision
    (A H : ℝ) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ M : ℕ in atTop,
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ f : Site → ℝ,
        (∀ z, |f z| ≤ Real.exp H) →
        (∀ z, 0 < f z ∧ |Real.log (f z)| ≤ H) →
        ∀ a T p q : ℕ, a + T ≤ M → ∀ x : Site,
          eLpNorm (fun ω =>
            (Real.log (profileP2Fun (criticalBeta ϑ M) a (a + T)
                (fun w => srwKernel (2 * q) (w - x)) f ω) -
              Real.log (profileP2Fun (criticalBeta ϑ M) a (a + T)
                (fun w => srwKernel (2 * p) (w - x)) f ω)) -
              (∫ ω', (Real.log (profileP2Fun (criticalBeta ϑ M) a (a + T)
                  (fun w => srwKernel (2 * q) (w - x)) (fun _ => 1) ω') -
                Real.log (profileP2Fun (criticalBeta ϑ M) a (a + T)
                  (fun w => srwKernel (2 * p) (w - x)) (fun _ => 1) ω'))
                ∂disorderLaw)) 2 disorderLaw ≤
            ENNReal.ofReal (2 * logHolderConstant *
              ((Real.exp H * (C + 1) * (Real.exp H * C)) ^ ((1 : ℝ) / 3) +
                ((C + 1) * C) ^ ((1 : ℝ) / 3)) *
              (2 * (((max p q - min p q : ℕ) : ℝ)) /
                Real.sqrt ((min p q : ℝ) + 1)) ^ ((1 : ℝ) / 3) *
              (1 + Real.log ((M : ℝ) + 1))) := by
  obtain ⟨C, hC, hraw⟩ :=
    eLpNorm_centered_log_walkKernel_profile_difference_le_collision_uniform_variation
      A H (Real.exp H) hH (by positivity)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hraw] with M hM
  intro ϑ hϑ f hfb hf a T p q hTM x
  let V : ℝ := 2 * (((max p q - min p q : ℕ) : ℝ)) /
    Real.sqrt ((min p q : ℝ) + 1)
  let L : ℝ := 1 + Real.log ((M : ℝ) + 1)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hL : 1 ≤ L := by
    dsimp [L]
    apply le_add_of_nonneg_right
    apply Real.log_nonneg
    have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    linarith
  have hraw' := hM ϑ hϑ f hfb hf a T p q hTM x
  have hsimp := width_raw_le_ofReal C H (Real.exp H) V L hC hV hL rfl
  simpa [V, L] using hraw'.trans hsimp

/-- At diffusively large widths, the `L²` difference between centered profile logarithms tends to zero for half-width changes of at most three steps, uniformly in the spatial center. -/
theorem eLpNorm_centered_log_walkKernel_profile_difference_small_of_close_widths
    (A H δ : ℝ) (hH : 0 ≤ H) (hδ : 0 < δ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop,
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ f : Site → ℝ,
        (∀ z, |f z| ≤ Real.exp H) →
        (∀ z, 0 < f z ∧ |Real.log (f z)| ≤ H) →
        ∀ a T p q : ℕ, a + T ≤ M → max p q - min p q ≤ 3 →
          δ * (M : ℝ) / 4 ≤ (min p q : ℝ) → ∀ x : Site,
            eLpNorm (fun ω =>
              (Real.log (profileP2Fun (criticalBeta ϑ M) a (a + T)
                  (fun w => srwKernel (2 * q) (w - x)) f ω) -
                Real.log (profileP2Fun (criticalBeta ϑ M) a (a + T)
                  (fun w => srwKernel (2 * p) (w - x)) f ω)) -
                (∫ ω', (Real.log (profileP2Fun (criticalBeta ϑ M) a (a + T)
                    (fun w => srwKernel (2 * q) (w - x)) (fun _ => 1) ω') -
                  Real.log (profileP2Fun (criticalBeta ϑ M) a (a + T)
                    (fun w => srwKernel (2 * p) (w - x)) (fun _ => 1) ω'))
                  ∂disorderLaw)) 2 disorderLaw ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨C, hC, hraw⟩ :=
    eLpNorm_centered_log_walkKernel_profile_difference_le_simplified_collision
      A H hH
  let K : ℝ := 2 * logHolderConstant *
    ((Real.exp H * (C + 1) * (Real.exp H * C)) ^ ((1 : ℝ) / 3) +
      ((C + 1) * C) ^ ((1 : ℝ) / 3))
  let S : ℝ := 3 * K * (12 / Real.sqrt δ) ^ ((1 : ℝ) / 3)
  have hK : 0 ≤ K := by
    dsimp [K]
    apply mul_nonneg (mul_nonneg (by positivity : 0 ≤ (2 : ℝ)) logHolderConstant_pos.le)
    apply add_nonneg
    · exact Real.rpow_nonneg (by positivity) _
    · exact Real.rpow_nonneg (by positivity) _
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hdecay : Tendsto (fun M : ℕ => S * (M : ℝ) ^ (-(1 : ℝ) / 12)) atTop (nhds 0) := by
    have hpow := (tendsto_rpow_neg_atTop (y := (1 : ℝ) / 12) (by norm_num)).comp
      tendsto_natCast_atTop_atTop
    have hexp : -(1 : ℝ) / 12 = -(1 / 12 : ℝ) := by norm_num
    simpa [S, hexp] using hpow.const_mul S
  have hsmall := hdecay.eventually (Iio_mem_nhds hε)
  have hMpos := (tendsto_natCast_atTop_atTop.const_mul_atTop hδ).eventually_ge_atTop 12
  have hlogReal := log_rpow_le_rpow_eventually 1 ((1 : ℝ) / 12) (by norm_num)
  have hplusTendsto : Tendsto (fun M : ℕ => (M : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hlogpow : ∀ᶠ M : ℕ in atTop,
      Real.log ((M : ℝ) + 1) ≤ ((M : ℝ) + 1) ^ ((1 : ℝ) / 12) := by
    filter_upwards [hplusTendsto.eventually hlogReal] with M hM
    simpa only [Real.rpow_one] using hM
  have hMone := (eventually_ge_atTop (1 : ℕ))
  filter_upwards [hraw, hsmall, hMpos, hlogpow, hMone] with M hMraw hMsmall hMδ hMlog hMone
  intro ϑ hϑ f hfb hf a T p q hTM hgap hmin x
  have hMreal : 1 ≤ (M : ℝ) := by exact_mod_cast hMone
  have hMnonneg : 0 ≤ (M : ℝ) := Nat.cast_nonneg _
  have hδM : 0 < δ * (M : ℝ) := by positivity
  have hmin' : δ * (M : ℝ) / 4 ≤ (min p q : ℝ) + 1 := by linarith
  have hdenPos : 0 < Real.sqrt ((min p q : ℝ) + 1) :=
    Real.sqrt_pos.mpr (by linarith)
  have hsmallDenPos : 0 < Real.sqrt (δ * (M : ℝ) / 4) :=
    Real.sqrt_pos.mpr (by positivity)
  have hden : Real.sqrt (δ * (M : ℝ) / 4) ≤ Real.sqrt ((min p q : ℝ) + 1) :=
    Real.sqrt_le_sqrt hmin'
  have hgapR : ((max p q - min p q : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hgap
  let V : ℝ := 2 * (((max p q - min p q : ℕ) : ℝ)) /
    Real.sqrt ((min p q : ℝ) + 1)
  let L : ℝ := 1 + Real.log ((M : ℝ) + 1)
  have hVbound : V ≤ 12 / Real.sqrt (δ * (M : ℝ)) := by
    dsimp [V]
    calc
      _ ≤ 6 / Real.sqrt ((min p q : ℝ) + 1) := by
        apply (div_le_div_iff₀ hdenPos hdenPos).2
        nlinarith [hgapR, hdenPos]
      _ ≤ 6 / Real.sqrt (δ * (M : ℝ) / 4) :=
        div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 6) hsmallDenPos hden
      _ = 12 / Real.sqrt (δ * (M : ℝ)) := by
        rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ δ * (M : ℝ)),
          Real.sqrt_mul hδ.le]
        have hrootProd : 0 < Real.sqrt δ * Real.sqrt (M : ℝ) :=
          mul_pos (Real.sqrt_pos.mpr hδ) (Real.sqrt_pos.mpr (by linarith))
        field_simp; ring
  have hVnonneg : 0 ≤ V := by dsimp [V]; positivity
  have hVpow : V ^ ((1 : ℝ) / 3) ≤
      (12 / Real.sqrt (δ * (M : ℝ))) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow hVnonneg hVbound (by norm_num)
  have hlognonneg : 0 ≤ Real.log ((M : ℝ) + 1) := by
    apply Real.log_nonneg
    linarith
  have hLbound : L ≤ 3 * (M : ℝ) ^ ((1 : ℝ) / 12) := by
    dsimp [L]
    have hlog : Real.log ((M : ℝ) + 1) ≤ ((M : ℝ) + 1) ^ ((1 : ℝ) / 12) := by
      simpa only [Real.rpow_one] using hMlog
    have hplus : (M : ℝ) + 1 ≤ 2 * (M : ℝ) := by linarith
    have hpowplus : ((M : ℝ) + 1) ^ ((1 : ℝ) / 12) ≤
        (2 * (M : ℝ)) ^ ((1 : ℝ) / 12) :=
      Real.rpow_le_rpow (by linarith) hplus (by norm_num)
    have hmul : (2 * (M : ℝ)) ^ ((1 : ℝ) / 12) =
        2 ^ ((1 : ℝ) / 12) * (M : ℝ) ^ ((1 : ℝ) / 12) :=
      Real.mul_rpow (by norm_num) hMnonneg
    have htwo : (2 : ℝ) ^ ((1 : ℝ) / 12) ≤ 2 := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (1 : ℝ) / 12 ≤ 1)
    have hone : 1 ≤ (M : ℝ) ^ ((1 : ℝ) / 12) := by
      simpa only [Real.rpow_zero] using
        Real.rpow_le_rpow_of_exponent_le hMreal (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 12)
    have hpowplus' : ((M : ℝ) + 1) ^ ((1 : ℝ) / 12) ≤
        2 * (M : ℝ) ^ ((1 : ℝ) / 12) := by
      calc
        _ ≤ (2 * (M : ℝ)) ^ ((1 : ℝ) / 12) := hpowplus
        _ = 2 ^ ((1 : ℝ) / 12) * (M : ℝ) ^ ((1 : ℝ) / 12) := hmul
        _ ≤ 2 * (M : ℝ) ^ ((1 : ℝ) / 12) := by
          exact mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hMnonneg _)
    calc
      1 + Real.log ((M : ℝ) + 1) ≤
          (M : ℝ) ^ ((1 : ℝ) / 12) +
            2 * (M : ℝ) ^ ((1 : ℝ) / 12) := by
              exact add_le_add hone (hlog.trans hpowplus')
      _ = 3 * (M : ℝ) ^ ((1 : ℝ) / 12) := by ring
  have hpower : (12 / Real.sqrt (δ * (M : ℝ))) ^ ((1 : ℝ) / 3) *
      (M : ℝ) ^ ((1 : ℝ) / 12) =
      (12 / Real.sqrt δ) ^ ((1 : ℝ) / 3) * (M : ℝ) ^ (-(1 : ℝ) / 12) := by
    have hexp13 : -(1 : ℝ) / 3 = -((1 : ℝ) / 3) := by norm_num
    have hrootInv : ((Real.sqrt (M : ℝ)) ^ ((1 : ℝ) / 3))⁻¹ =
        (Real.sqrt (M : ℝ)) ^ (-(1 : ℝ) / 3) := by
      rw [hexp13]
      exact (Real.rpow_neg (Real.sqrt_nonneg (M : ℝ)) ((1 : ℝ) / 3)).symm
    have hrootPow : (Real.sqrt (M : ℝ)) ^ (-(1 : ℝ) / 3) =
        (M : ℝ) ^ (-(1 : ℝ) / 6) := by
      rw [hexp13, Real.sqrt_eq_rpow, ← Real.rpow_mul hMnonneg]
      rw [show ((1 : ℝ) / 2) * (-((1 : ℝ) / 3)) = -(1 : ℝ) / 6 by norm_num]
    have hcombine : (M : ℝ) ^ (-(1 : ℝ) / 6) * (M : ℝ) ^ ((1 : ℝ) / 12) =
        (M : ℝ) ^ (-(1 : ℝ) / 12) := by
      rw [← Real.rpow_add (by linarith : 0 < (M : ℝ))]
      rw [show (-(1 : ℝ) / 6) + (1 : ℝ) / 12 = -(1 : ℝ) / 12 by norm_num]
    rw [Real.sqrt_mul hδ.le,
      Real.div_rpow (by norm_num : 0 ≤ (12 : ℝ)) (by positivity) ((1 : ℝ) / 3),
      Real.mul_rpow (Real.sqrt_nonneg δ) (Real.sqrt_nonneg (M : ℝ))]
    calc
      _ = (12 ^ ((1 : ℝ) / 3) / (Real.sqrt δ) ^ ((1 : ℝ) / 3)) *
          ((Real.sqrt (M : ℝ)) ^ ((1 : ℝ) / 3))⁻¹ * (M : ℝ) ^ ((1 : ℝ) / 12) := by ring
      _ = (12 / Real.sqrt δ) ^ ((1 : ℝ) / 3) *
          ((Real.sqrt (M : ℝ)) ^ ((1 : ℝ) / 3))⁻¹ * (M : ℝ) ^ ((1 : ℝ) / 12) := by
            rw [← Real.div_rpow (by norm_num : 0 ≤ (12 : ℝ)) (Real.sqrt_nonneg δ)]
      _ = (12 / Real.sqrt δ) ^ ((1 : ℝ) / 3) *
          (Real.sqrt (M : ℝ)) ^ (-(1 : ℝ) / 3) * (M : ℝ) ^ ((1 : ℝ) / 12) := by
            rw [hrootInv]
      _ = (12 / Real.sqrt δ) ^ ((1 : ℝ) / 3) *
          (M : ℝ) ^ (-(1 : ℝ) / 6) * (M : ℝ) ^ ((1 : ℝ) / 12) := by
            rw [hrootPow]
      _ = (12 / Real.sqrt δ) ^ ((1 : ℝ) / 3) *
          (M : ℝ) ^ (-(1 : ℝ) / 12) := by
            rw [show ((12 / Real.sqrt δ) ^ ((1 : ℝ) / 3) *
              (M : ℝ) ^ (-(1 : ℝ) / 6) * (M : ℝ) ^ ((1 : ℝ) / 12)) =
                (12 / Real.sqrt δ) ^ ((1 : ℝ) / 3) *
                  ((M : ℝ) ^ (-(1 : ℝ) / 6) * (M : ℝ) ^ ((1 : ℝ) / 12)) by ring,
              hcombine]
  have htarget : K * V ^ ((1 : ℝ) / 3) * L ≤ S * (M : ℝ) ^ (-(1 : ℝ) / 12) := by
    calc
      _ ≤ K * (12 / Real.sqrt (δ * (M : ℝ))) ^ ((1 : ℝ) / 3) *
          (3 * (M : ℝ) ^ ((1 : ℝ) / 12)) := by
            dsimp [K]
            gcongr
      _ = S * (M : ℝ) ^ (-(1 : ℝ) / 12) := by
            dsimp [S]
            calc
              _ = 3 * K * ((12 / Real.sqrt (δ * (M : ℝ))) ^ ((1 : ℝ) / 3) *
                    (M : ℝ) ^ ((1 : ℝ) / 12)) := by ring
              _ = _ := by rw [hpower]; ring
  have hbound := hMraw ϑ hϑ f hfb hf a T p q hTM x
  have hsmall' : S * (M : ℝ) ^ (-(1 : ℝ) / 12) < ε := hMsmall
  have hreal : K * V ^ ((1 : ℝ) / 3) * L ≤ ε := le_trans htarget hsmall'.le
  have hfinal := ENNReal.ofReal_le_ofReal hreal
  simpa [K, V, L] using hbound.trans hfinal

private theorem latticeSmoothingError_sameStart_width_integrate_profile_bound
    (β : ℝ) (M a p q : ℕ) (hM : Even M) (ha : Even a)
    (hMpos : 0 < M) (haM : a ≤ M)
    (h₀ : Plane →ᵇ ℝ) (φ : Plane → ℝ) (hφ : Measurable φ)
    (hφc : HasCompactSupport φ) (hφint : Integrable φ) (R : ℝ) (hR : 0 ≤ R)
    (hsite : ∀ z : Site,
      eLpNorm (fun ω =>
        (Real.log (profileP2Fun β a M (fun w => srwKernel (2 * q) (w - z))
            (evenExtension (cellAverage M fun y => Real.exp (h₀ y))) ω) -
          Real.log (profileP2Fun β a M (fun w => srwKernel (2 * p) (w - z))
            (evenExtension (cellAverage M fun y => Real.exp (h₀ y))) ω)) -
        (∫ ω', (Real.log (profileP2Fun β a M
            (fun w => srwKernel (2 * q) (w - z)) (fun _ => 1) ω') -
          Real.log (profileP2Fun β a M
            (fun w => srwKernel (2 * p) (w - z)) (fun _ => 1) ω')) ∂disorderLaw))
        2 disorderLaw ≤ ENNReal.ofReal R) :
    eLpNorm (fun ω =>
      latticeSmoothingError β M M a (2 * q) h₀ φ ω -
        latticeSmoothingError β M M a (2 * p) h₀ φ ω) 2 disorderLaw ≤
      ENNReal.ofReal (R * ∫ x, |φ x|) := by
  let f : Site → ℝ := evenExtension (cellAverage M (fun y => Real.exp (h₀ y)))
  have hwidth : ∀ z : Site,
      eLpNorm (fun ω =>
        (Real.log (profileP2Fun β a M (fun w => srwKernel (2 * q) (w - z)) f ω) -
          ∫ ω', Real.log (profileP2Fun β a M
            (fun w => srwKernel (2 * q) (w - z)) (fun _ => 1) ω') ∂disorderLaw) -
        (Real.log (profileP2Fun β a M (fun w => srwKernel (2 * p) (w - z)) f ω) -
          ∫ ω', Real.log (profileP2Fun β a M
            (fun w => srwKernel (2 * p) (w - z)) (fun _ => 1) ω') ∂disorderLaw))
        2 disorderLaw ≤ ENNReal.ofReal R := by
    intro z
    let νq : Site → ℝ := fun w => srwKernel (2 * q) (w - z)
    let νp : Site → ℝ := fun w => srwKernel (2 * p) (w - z)
    let Aq : Finset Site := Polymer.endpoints z (2 * q)
    let Ap : Finset Site := Polymer.endpoints z (2 * p)
    have hνqA : ∀ w ∉ Aq, νq w = 0 := by
      intro w hw
      exact Polymer.srwKernel_eq_zero_of_not_mem (2 * q) z w (by simpa [Aq] using hw)
    have hνpA : ∀ w ∉ Ap, νp w = 0 := by
      intro w hw
      exact Polymer.srwKernel_eq_zero_of_not_mem (2 * p) z w (by simpa [Ap] using hw)
    have hνq0 : ∀ w, 0 ≤ νq w := fun w => Polymer.kernel_nonneg (2 * q) (w - z)
    have hνp0 : ∀ w, 0 ≤ νp w := fun w => Polymer.kernel_nonneg (2 * p) (w - z)
    have hνq1 : ∑ w ∈ Aq, νq w = 1 := by
      simpa [νq, Aq] using Polymer.sum_srwKernel_endpoints (2 * q) z
    have hνp1 : ∑ w ∈ Ap, νp w = 1 := by
      simpa [νp, Ap] using Polymer.sum_srwKernel_endpoints (2 * p) z
    have hflat : ∀ w : Site, 0 < (1 : ℝ) ∧ |Real.log (1 : ℝ)| ≤ 0 := by
      intro w
      norm_num
    have hqmem := memLp_log_profileP2Fun_of_bounded_terminal β a M νq Aq
      hνqA hνq0 hνq1 (fun _ => 1) 0 (by norm_num) hflat
    have hpmem := memLp_log_profileP2Fun_of_bounded_terminal β a M νp Ap
      hνpA hνp0 hνp1 (fun _ => 1) 0 (by norm_num) hflat
    have hqint : Integrable
        (fun ω => Real.log (profileP2Fun β a M νq (fun _ => 1) ω)) disorderLaw :=
      hqmem.integrable (by norm_num)
    have hpint : Integrable
        (fun ω => Real.log (profileP2Fun β a M νp (fun _ => 1) ω)) disorderLaw :=
      hpmem.integrable (by norm_num)
    have heq : (fun ω =>
        (Real.log (profileP2Fun β a M νq f ω) -
            ∫ ω', Real.log (profileP2Fun β a M νq (fun _ => 1) ω') ∂disorderLaw) -
          (Real.log (profileP2Fun β a M νp f ω) -
            ∫ ω', Real.log (profileP2Fun β a M νp (fun _ => 1) ω') ∂disorderLaw)) =
        fun ω =>
          (Real.log (profileP2Fun β a M νq f ω) -
            Real.log (profileP2Fun β a M νp f ω)) -
          ∫ ω', (Real.log (profileP2Fun β a M νq (fun _ => 1) ω') -
            Real.log (profileP2Fun β a M νp (fun _ => 1) ω')) ∂disorderLaw := by
      funext ω
      rw [integral_sub hqint hpint]
      ring
    have hz := hsite z
    rw [heq]
    simpa only [νq, νp] using hz
  have hresult := latticeSmoothingError_sameStart_width_le_of
    β M a (2 * q) (2 * p) hM ha (by simp) (by simp) hMpos haM h₀ φ hφ hφc
    hφint R hR (by simpa [f] using hwidth)
  exact hresult.2

/-- Integrating the uniform centered profile comparison gives a small same-start smoothing
error when the two kernel widths differ by at most three half-steps. -/
theorem latticeSmoothingError_sameStart_width_small_of_close_widths
    (A H M₁ M₂ δ : ℝ) (hH : 0 ≤ H) (hδ : 0 < δ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop,
      Even M → ∀ ϑ ∈ Set.Icc (-A) A, ∀ a T p q : ℕ,
        Even a → a + T ≤ M → max p q - min p q ≤ 3 →
        δ * (M : ℝ) / 4 ≤ (min p q : ℝ) →
        ∀ h₀ : Plane →ᵇ ℝ, ‖h₀‖ ≤ H →
        ∀ φ : Plane → ℝ, Measurable φ → HasCompactSupport φ →
          (∫ x, |φ x| ≤ M₁) → (∀ x, |φ x| ≤ M₂) →
          eLpNorm (fun ω =>
            latticeSmoothingError (criticalBeta ϑ M) M M a (2 * q) h₀ φ ω -
              latticeSmoothingError (criticalBeta ϑ M) M M a (2 * p) h₀ φ ω)
            2 disorderLaw ≤ ENNReal.ofReal ε := by
  intro ε hε
  let R : ℝ := ε / (|M₁| + 1)
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hsmall :=
    eLpNorm_centered_log_walkKernel_profile_difference_small_of_close_widths
      A H δ hH hδ R hR
  have hMlarge : ∀ᶠ M : ℕ in atTop, δ * (M : ℝ) ≥ 16 := by
    have h := (tendsto_natCast_atTop_atTop.const_mul_atTop hδ).eventually_ge_atTop 16
    filter_upwards [h] with M hM
    exact hM
  have hMone : ∀ᶠ M : ℕ in atTop, 1 ≤ M := eventually_ge_atTop 1
  filter_upwards [hsmall, hMlarge, hMone] with M hMsmall hMlarge hMone
  intro hMeven ϑ hϑ a T p q haEven haTM hgap hmin h₀ hh₀ φ hφ hφc hφL1 hφM
  have hMpos : 0 < M := by omega
  have hMnat : 1 ≤ M := hMone
  have hMreal : 0 ≤ (M : ℝ) := Nat.cast_nonneg _
  let f : Site → ℝ := evenExtension (cellAverage M (fun y => Real.exp (h₀ y)))
  have hfcell : ∀ z, 0 < f z ∧ |Real.log (f z)| ≤ H := by
    intro z
    by_cases hz : Even (z 0 + z 1)
    · have hb := cellAverage_exp_bounds_of_even M hMnat h₀ hz
      refine ⟨?_, ?_⟩
      · simpa [f, evenExtension, hz] using hb.1
      · simpa [f, evenExtension, hz] using hb.2.trans hh₀
    · have hH : 0 ≤ H := hH
      simp [f, evenExtension, hz, hH]
  have hfb : ∀ z, |f z| ≤ Real.exp H := by
    intro z
    have hpos := (hfcell z).1
    have hlog := (abs_le.mp (hfcell z).2).2
    have hup : f z ≤ Real.exp H := by
      calc
        f z = Real.exp (Real.log (f z)) := (Real.exp_log hpos).symm
        _ ≤ Real.exp H := Real.exp_le_exp.mpr hlog
    rw [abs_of_pos hpos]
    exact hup
  have hφint : Integrable φ :=
    integrable_of_measurable_compactSupport_bounded hφ hφc ⟨M₂, hφM⟩
  have hsite := hMsmall ϑ hϑ f hfb hfcell a (M - a) p q (by omega) hgap hmin
  have hsite' : ∀ z : Site,
      eLpNorm (fun ω =>
        (Real.log (profileP2Fun (criticalBeta ϑ M) a M
            (fun w => srwKernel (2 * q) (w - z)) f ω) -
          Real.log (profileP2Fun (criticalBeta ϑ M) a M
            (fun w => srwKernel (2 * p) (w - z)) f ω)) -
        (∫ ω', (Real.log (profileP2Fun (criticalBeta ϑ M) a M
            (fun w => srwKernel (2 * q) (w - z)) (fun _ => 1) ω') -
          Real.log (profileP2Fun (criticalBeta ϑ M) a M
            (fun w => srwKernel (2 * p) (w - z)) (fun _ => 1) ω')) ∂disorderLaw))
        2 disorderLaw ≤ ENNReal.ofReal R := by
    intro z
    simpa [Nat.add_sub_of_le (by omega : a ≤ M)] using hsite z
  have hwidthIntegrated := latticeSmoothingError_sameStart_width_integrate_profile_bound
    (criticalBeta ϑ M) M a p q hMeven haEven hMpos (by omega)
    h₀ φ hφ hφc hφint R hR.le (by simpa [f] using hsite')
  have hM₁nonneg : 0 ≤ M₁ := by
    have hintnonneg : 0 ≤ ∫ x, |φ x| := integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun x => abs_nonneg (φ x))
    exact hintnonneg.trans hφL1
  have hmass : ∫ x, |φ x| ≤ M₁ := hφL1
  have hreal : R * ∫ x, |φ x| ≤ ε := by
    rw [show R * ∫ x, |φ x| = ε * (∫ x, |φ x|) / (|M₁| + 1) by
      dsimp [R]
      ring]
    have hden : 0 < |M₁| + 1 := by positivity
    have hmassAbs : ∫ x, |φ x| ≤ |M₁| + 1 := by
      exact le_trans hmass (by linarith [le_abs_self M₁])
    exact (div_le_iff₀ hden).2 (mul_le_mul_of_nonneg_left hmassAbs hε.le)
  exact hwidthIntegrated.trans (ENNReal.ofReal_le_ofReal hreal)

/-- The same-start width estimate in the original integer-width convention. Even widths within six
integer steps have half-widths within three steps. -/
theorem latticeSmoothingError_sameStart_width_small_of_close_even_widths
    (A H M₁ M₂ δ : ℝ) (hH : 0 ≤ H) (hδ : 0 < δ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ M : ℕ in atTop,
      Even M → ∀ ϑ ∈ Set.Icc (-A) A, ∀ a j d : ℕ,
        Even a → a ≤ M → Even j → Even d →
        (j : ℤ) ≤ (d : ℤ) + 6 → (d : ℤ) ≤ (j : ℤ) + 6 →
        δ * (M : ℝ) / 4 ≤ (min (j / 2) (d / 2) : ℝ) →
        ∀ h₀ : Plane →ᵇ ℝ, ‖h₀‖ ≤ H →
        ∀ φ : Plane → ℝ, Measurable φ → HasCompactSupport φ →
          (∫ x, |φ x| ≤ M₁) → (∀ x, |φ x| ≤ M₂) →
          eLpNorm (fun ω =>
            latticeSmoothingError (criticalBeta ϑ M) M M a j h₀ φ ω -
              latticeSmoothingError (criticalBeta ϑ M) M M a d h₀ φ ω)
            2 disorderLaw ≤ ENNReal.ofReal ε := by
  intro ε hε
  filter_upwards [latticeSmoothingError_sameStart_width_small_of_close_widths
      A H M₁ M₂ δ hH hδ ε hε] with M hM
  intro hMeven ϑ hϑ a j d ha haM hj hd hjd hdj hmin h₀ hh₀ φ hφ hφc hφL1 hφM
  have hjhalf : 2 * (j / 2) = j := by
    rcases hj with ⟨r, hr⟩
    omega
  have hdhalf : 2 * (d / 2) = d := by
    rcases hd with ⟨r, hr⟩
    omega
  have hjreal : ((j / 2 : ℕ) : ℝ) = (j : ℝ) / 2 := by
    have hcast : 2 * ((j / 2 : ℕ) : ℝ) = (j : ℝ) := by exact_mod_cast hjhalf
    nlinarith
  have hdreal : ((d / 2 : ℕ) : ℝ) = (d : ℝ) / 2 := by
    have hcast : 2 * ((d / 2 : ℕ) : ℝ) = (d : ℝ) := by exact_mod_cast hdhalf
    nlinarith
  have hgap : max (j / 2) (d / 2) - min (j / 2) (d / 2) ≤ 3 := by
    omega
  have hmin' : δ * (M : ℝ) / 4 ≤
      min ((j / 2 : ℕ) : ℝ) ((d / 2 : ℕ) : ℝ) := by
    simpa only [hjreal, hdreal] using hmin
  have hgap' : max (d / 2) (j / 2) - min (d / 2) (j / 2) ≤ 3 := by
    simpa only [max_comm, min_comm] using hgap
  have hmin'' : δ * (M : ℝ) / 4 ≤
      min ((d / 2 : ℕ) : ℝ) ((j / 2 : ℕ) : ℝ) := by
    simpa only [min_comm] using hmin'
  have h := hM hMeven ϑ hϑ a (M - a) (d / 2) (j / 2) ha (by omega)
    hgap' hmin'' h₀ hh₀ φ hφ hφc hφL1 hφM
  simpa only [hjhalf, hdhalf] using h

end Critical2DKPZ.Smoothing

end
