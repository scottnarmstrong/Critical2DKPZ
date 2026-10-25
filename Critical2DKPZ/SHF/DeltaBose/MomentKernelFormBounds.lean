/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.DiagramKernelBounds
public import Critical2DKPZ.SHF.DeltaBose.ChainSummability
public import Critical2DKPZ.SHF.DeltaBose.Measurability
public import Critical2DKPZ.SHF.DeltaBose.FreeMass
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # Positive form bounds for the complete moment-kernel series -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- The full moment-kernel series is bounded as a positive bilinear form.
The constant is uniform for `θ ≤ A` and the time exponential is explicit. -/
theorem exists_formBound_momentKernel (n : ℕ) (A : ℝ) :
    ∃ C rate : ℝ, 0 < C ∧ ∀ θ : ℝ, θ ≤ A → ∀ h : ℝ, 0 < h →
      FormBound volume volume (momentKernel n θ h)
        (ENNReal.ofReal (C * Real.exp (rate * h) * min h 1 ^ (-(n : ℝ)))) := by
  obtain ⟨CD, cD, rateD, hCD, hcD, hrateD, hD5⟩ :=
    exists_formBound_diagramKernel n A
  let N : ℝ := (Fintype.card (CollisionPair n) : ℝ)
  let rate : ℝ := max rateD (Real.exp (A + 2 * N * cD + 1))
  let CE : ℝ := 1 + 2 * CD * N
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hrate : rateD ≤ rate := by dsimp [rate]; exact le_max_left _ _
  have hrateExp : Real.exp (A + 2 * N * cD + 1) ≤ rate := by
    dsimp [rate]
    exact le_max_right _ _
  have hratePos : 0 < rate := lt_of_lt_of_le (Real.exp_pos (A + 1))
    (le_trans hrateD hrate)
  have hlog : A + 2 * N * cD + 1 ≤ Real.log rate := by
    calc
      A + 2 * N * cD + 1 = Real.log (Real.exp (A + 2 * N * cD + 1)) :=
        (Real.log_exp _).symm
      _ ≤ Real.log rate := Real.log_le_log (Real.exp_pos _) hrateExp
  have hgap : 0 < Real.log rate - A := by
    have htwo : 0 ≤ 2 * N * cD := by positivity
    have hlogBase : A + 1 ≤ Real.log rate := by
      calc
        A + 1 ≤ A + 2 * N * cD + 1 := by linarith
        _ ≤ Real.log rate := hlog
    linarith
  have hratioHalf : N * cD / (Real.log rate - A) ≤ 1 / 2 := by
    apply (div_le_iff₀ hgap).2
    have hstrong : 2 * N * cD + 1 ≤ Real.log rate - A := by linarith
    nlinarith [hstrong]
  have hratio0 : 0 ≤ N * cD / (Real.log rate - A) :=
    div_nonneg (mul_nonneg hN hcD.le) hgap.le
  have hratioLt : N * cD / (Real.log rate - A) < 1 :=
    lt_of_le_of_lt hratioHalf (by norm_num)
  refine ⟨CE, rate, ?_, ?_⟩
  · dsimp [CE]
    positivity
  · intro θ hθ h hh
    let B : ℝ := CD * Real.exp (rate * h) * min h 1 ^ (-(n : ℝ))
    let r : ℝ := cD / (Real.log rate - A)
    let q : ℝ := N * cD / (Real.log rate - A)
    have hminPos : 0 < min h 1 := lt_min hh (by norm_num)
    have hBpos : 0 < B := by
      dsimp [B]
      positivity
    have hBnonneg : 0 ≤ B := hBpos.le
    have hq0 : 0 ≤ q := by
      dsimp [q]
      exact div_nonneg (mul_nonneg hN hcD.le) hgap.le
    have hqBound : q ≤ 1 / 2 := by
      dsimp [q, r]
      exact hratioHalf
    have hqLt : q < 1 := lt_of_le_of_lt hqBound (by norm_num)
    have hBN : 0 ≤ B * N := mul_nonneg hBnonneg hN
    have hrealSeries : Summable (fun m : ℕ => B * N * q ^ m) :=
      (summable_geometric_of_lt_one hq0 hqLt).mul_left (B * N)
    have hrealSeriesSum :
        (∑' m : ℕ, B * N * q ^ m) ≤ 2 * B * N := by
      calc
        (∑' m : ℕ, B * N * q ^ m) = B * N * ∑' m : ℕ, q ^ m := tsum_mul_left
        _ = B * N * (1 - q)⁻¹ := by rw [tsum_geometric_of_lt_one hq0 hqLt]
        _ ≤ B * N * 2 := mul_le_mul_of_nonneg_left ?_ hBN
        _ = 2 * B * N := by ring
      · have hden : 1 / 2 ≤ 1 - q := by linarith
        have hdenPos : 0 < 1 - q := by linarith
        calc
          (1 - q)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ :=
            (inv_le_inv₀ hdenPos (by norm_num)).mpr hden
          _ = 2 := by norm_num
    have hrealTermNonneg (m : ℕ) : 0 ≤ B * N * q ^ m := by positivity
    have hennrealSeries :
        (∑' m : ℕ, ENNReal.ofReal (B * N * q ^ m)) ≤ ENNReal.ofReal (2 * B * N) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg hrealTermNonneg hrealSeries]
      exact ENNReal.ofReal_le_ofReal hrealSeriesSum
    let K : ℕ → Configuration n → Configuration n → ℝ≥0∞ := fun m x y =>
      ∑ w : CollisionWord n (m + 1), diagramKernel θ (List.ofFn w.1) h x y
    have hKmeas (m : ℕ) : Measurable (Function.uncurry (K m)) := by
      dsimp [K]
      apply Finset.measurable_sum
      intro w hw
      exact measurable_diagramKernel_comp (List.ofFn w.1)
        measurable_const measurable_const measurable_fst measurable_snd
    have hwordMeas (m : ℕ) (w : CollisionWord n (m + 1)) :
        Measurable (Function.uncurry (fun x y : Configuration n =>
          diagramKernel θ (List.ofFn w.1) h x y)) := by
      exact measurable_diagramKernel_comp (List.ofFn w.1)
        measurable_const measurable_const measurable_fst measurable_snd
    have hwordForm (m : ℕ) (w : CollisionWord n (m + 1)) :
        FormBound volume volume (fun x y : Configuration n =>
          diagramKernel θ (List.ofFn w.1) h x y)
          (ENNReal.ofReal (B * r ^ m)) := by
      have hd := hD5 θ hθ rate hrate m w h hh
      simpa [B, r, mul_assoc] using hd
    have hcoeff (m : ℕ) :
        (∑' w : CollisionWord n (m + 1), ENNReal.ofReal (B * r ^ m)) ≤
          ENNReal.ofReal (B * N * q ^ m) := by
      have hcardReal :
          (Fintype.card (CollisionWord n (m + 1)) : ℝ) ≤ N ^ (m + 1) := by
        dsimp [N]
        exact_mod_cast collisionWord_card_le_pow n (m + 1)
      have hcard :
          (Fintype.card (CollisionWord n (m + 1)) : ℝ≥0∞) ≤
            ENNReal.ofReal (N ^ (m + 1)) := by
        have hcard' := ENNReal.ofReal_le_ofReal hcardReal
        simpa using hcard'
      have hsum :
          (∑' w : CollisionWord n (m + 1), ENNReal.ofReal (B * r ^ m)) =
            (Fintype.card (CollisionWord n (m + 1)) : ℝ≥0∞) *
              ENNReal.ofReal (B * r ^ m) := by
        simp only [tsum_fintype, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      rw [hsum]
      calc
        (Fintype.card (CollisionWord n (m + 1)) : ℝ≥0∞) *
            ENNReal.ofReal (B * r ^ m) ≤
            ENNReal.ofReal (N ^ (m + 1)) * ENNReal.ofReal (B * r ^ m) :=
              mul_le_mul' hcard le_rfl
        _ = ENNReal.ofReal (N ^ (m + 1) * (B * r ^ m)) := by
              rw [← ENNReal.ofReal_mul (pow_nonneg hN _)]
        _ = ENNReal.ofReal (B * N * q ^ m) := by
              congr 1
              dsimp [q]
              rw [pow_succ]
              ring
    have hKform (m : ℕ) : FormBound volume volume (K m)
        (ENNReal.ofReal (B * N * q ^ m)) := by
      have hs := formBound_tsum (μ := volume) (ν := volume)
        (fun w : CollisionWord n (m + 1) => hwordMeas m w)
        (fun w : CollisionWord n (m + 1) => hwordForm m w)
      have hs' := hs.mono (fun _ _ => le_rfl) (hcoeff m)
      simpa [K, tsum_fintype] using hs'
    have hseriesMeas : Measurable (Function.uncurry (fun x y : Configuration n =>
        ∑' m : ℕ, K m x y)) := by
      apply Measurable.tsum
      intro m
      exact hKmeas m
    have hseriesForm := formBound_tsum (μ := volume) (ν := volume)
      (fun m : ℕ => hKmeas m) (fun m : ℕ => hKform m)
    have hseriesForm' := hseriesForm.mono (fun _ _ => le_rfl) hennrealSeries
    have hfreeKernelMeas : Measurable (Function.uncurry (fun x y : Configuration n =>
        ENNReal.ofReal (freeKernel n h x y))) :=
      ((measurable_freeKernel n).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
    have hfreeForm : FormBound volume volume
        (fun x y : Configuration n => ENNReal.ofReal (freeKernel n h x y)) 1 := by
      refine formBound_of_schur volume volume (A := 1) (B := 1) (c := 1)
        hfreeKernelMeas ?_ ?_ ?_
      · intro x
        rw [lintegral_freeKernel_right n hh x]
      · intro y
        simp_rw [freeKernel_symm n h]
        rw [lintegral_freeKernel_right n hh y]
      · norm_num
    have hfreeSeries := FormBound.add hfreeKernelMeas hseriesMeas hfreeForm hseriesForm'
    have hmomentPre : FormBound volume volume (momentKernel n θ h)
        (1 + ENNReal.ofReal (2 * B * N)) := by
      change FormBound volume volume (fun x y : Configuration n =>
        ENNReal.ofReal (freeKernel n h x y) + ∑' m : ℕ, K m x y)
        (1 + ENNReal.ofReal (2 * B * N))
      simpa [K] using hfreeSeries
    have hfacExp : 1 ≤ Real.exp (rate * h) := by
      apply Real.one_le_exp_iff.mpr
      exact mul_nonneg hratePos.le hh.le
    have hfacMin : 1 ≤ min h 1 ^ (-(n : ℝ)) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
      have hpowPos : 0 < min h 1 ^ n := pow_pos hminPos _
      have hpow : min h 1 ^ n ≤ 1 := by
        calc
          min h 1 ^ n ≤ 1 ^ n := pow_le_pow_left₀ (by positivity) (min_le_right _ _) n
          _ = 1 := by simp
      simpa using (inv_le_inv₀ one_pos hpowPos).mpr hpow
    have hfac : 1 ≤ Real.exp (rate * h) * min h 1 ^ (-(n : ℝ)) := by
      calc
        1 ≤ Real.exp (rate * h) := hfacExp
        _ = Real.exp (rate * h) * 1 := by simp
        _ ≤ Real.exp (rate * h) * min h 1 ^ (-(n : ℝ)) :=
          mul_le_mul_of_nonneg_left hfacMin (Real.exp_nonneg _)
    have hfinalCoeff :
        1 + ENNReal.ofReal (2 * B * N) ≤
          ENNReal.ofReal (CE * Real.exp (rate * h) * min h 1 ^ (-(n : ℝ))) := by
      rw [← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add (by norm_num) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      dsimp [B, CE]
      have hfac' : 1 ≤ Real.exp (rate * h) * min h 1 ^ (-(n : ℝ)) := hfac
      calc
        1 + 2 * (CD * Real.exp (rate * h) * min h 1 ^ (-(n : ℝ))) * N =
            1 + (2 * CD * N) *
              (Real.exp (rate * h) * min h 1 ^ (-(n : ℝ))) := by ring
        _ ≤ Real.exp (rate * h) * min h 1 ^ (-(n : ℝ)) +
              (2 * CD * N) * (Real.exp (rate * h) * min h 1 ^ (-(n : ℝ))) :=
                add_le_add hfac' le_rfl
        _ = (1 + 2 * CD * N) * Real.exp (rate * h) *
              min h 1 ^ (-(n : ℝ)) := by ring
    exact hmomentPre.mono (fun _ _ => le_rfl) hfinalCoeff

end Critical2DKPZ.DeltaBose
