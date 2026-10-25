/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.ScalarBounds
public import Critical2DKPZ.SHF.DeltaBose.ScalarEnvelope
public import Critical2DKPZ.Renewal.Primitive
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

/-! # Backward weights for collision renewals

The logarithmic weight used when integrating collision strings from their terminal
time backwards. -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.Collision

open MeasureTheory
open Filter
open Set
open scoped Topology

/-- The backward logarithmic weight. -/
def backwardWeight (T τ : ℝ) : ℝ := Real.log (2 * T) - Real.log (T - τ)

/-- On the strict time triangle, the weight equals the logarithmic quotient in equation (A.21). Its extension has a finite value at the terminal endpoint `τ = T`. -/
theorem backwardWeight_eq_log_ratio {T τ : ℝ} (hT : 0 < T) (hτT : τ < T) :
    backwardWeight T τ = Real.log (2 * T / (T - τ)) := by
  unfold backwardWeight
  rw [Real.log_div (x := 2 * T) (y := T - τ) (by positivity)
    (sub_ne_zero.mpr hτT.ne.symm)]

/-- The backward weight is nonnegative for `0 ≤ τ < T`. -/
theorem backwardWeight_nonneg {T τ : ℝ} (hT : 0 < T) (hτ : 0 ≤ τ) (hτT : τ < T) :
    0 ≤ backwardWeight T τ := by
  rw [backwardWeight_eq_log_ratio hT hτT]
  apply Real.log_nonneg
  rw [le_div_iff₀ (sub_pos.mpr hτT)]
  nlinarith

/-- For `0 ≤ τ < T`, the backward weight is at least `log 2`. -/
theorem backwardWeight_ge_log_two {T τ : ℝ} (hτ : 0 ≤ τ) (hτT : τ < T) :
    Real.log 2 ≤ backwardWeight T τ := by
  rw [backwardWeight_eq_log_ratio (by linarith [hτT, hτ]) hτT]
  apply Real.log_le_log (by norm_num)
  rw [le_div_iff₀ (sub_pos.mpr hτT)]
  nlinarith

/-- The backward weight is at most the logarithm of four before half the positive terminal time. -/
theorem backwardWeight_le_log_four {T s : ℝ} (hT : 0 < T)
    (hsHalf : s ≤ T / 2) :
    backwardWeight T s ≤ Real.log 4 := by
  rw [backwardWeight_eq_log_ratio hT (by linarith)]
  apply Real.log_le_log
  · exact div_pos (by positivity) (sub_pos.mpr (by linarith : s < T))
  · apply (div_le_iff₀ (sub_pos.mpr (by linarith : s < T))).2
    nlinarith

/-- For fixed `τ ≥ 0`, the backward weight is nonincreasing as the terminal horizon varies over `(τ,∞)`. -/
theorem backwardWeight_antitone_horizon {τ S T : ℝ} (hτ : 0 ≤ τ)
    (hτS : τ < S) (hST : S ≤ T) : backwardWeight T τ ≤ backwardWeight S τ := by
  have hS : 0 < S := lt_of_le_of_lt hτ hτS
  have hT : 0 < T := lt_of_lt_of_le hS hST
  rw [backwardWeight_eq_log_ratio hT (lt_of_lt_of_le hτS hST),
    backwardWeight_eq_log_ratio hS hτS]
  apply Real.log_le_log
  · exact div_pos (by positivity) (sub_pos.mpr (lt_of_lt_of_le hτS hST))
  · have hT : 0 < T := lt_of_lt_of_le hS hST
    have hdenS : 0 < S - τ := sub_pos.mpr hτS
    have hdenT : 0 < T - τ := sub_pos.mpr (lt_of_lt_of_le hτS hST)
    rw [div_le_div_iff₀ hdenT hdenS]
    nlinarith

/-- The integral of the backward weight from `T/2` to `T` equals `T/2 * (log 4 + 1)` for `T > 0`. -/
theorem integral_backwardWeight_upperHalf {T : ℝ} (hT : 0 < T) :
    ∫ s in T / 2..T, backwardWeight T s = T / 2 * (Real.log 4 + 1) := by
  have hlog : IntervalIntegrable (fun s : ℝ => Real.log (T - s)) volume (T / 2) T := by
    have h := (intervalIntegral.intervalIntegrable_log' (a := T / 2) (b := 0)).comp_sub_left T
    convert h using 2 <;> ring
  have hc : IntervalIntegrable (fun _ : ℝ => Real.log (2 * T)) volume (T / 2) T :=
    intervalIntegrable_const
  change ∫ s in T / 2..T, (Real.log (2 * T) - Real.log (T - s)) = _
  rw [intervalIntegral.integral_sub hc hlog,
    intervalIntegral.integral_const, intervalIntegral.integral_comp_sub_left,
    integral_log]
  have hratio : Real.log (2 * T) - Real.log (T / 2) = Real.log 4 := by
    rw [← Real.log_div (by positivity : 2 * T ≠ 0) (by positivity : T / 2 ≠ 0)]
    congr 1
    field_simp
    norm_num
  simp only [sub_self, zero_mul, sub_zero, add_zero]
  rw [smul_eq_mul]
  calc
    _ = T / 2 * (Real.log (2 * T) - Real.log (T / 2) + 1) := by ring_nf
    _ = _ := by rw [hratio]

/-- The extended backward weight is interval-integrable up to its terminal endpoint. -/
theorem backwardWeight_intervalIntegrable {S T : ℝ} :
    IntervalIntegrable (backwardWeight T) volume S T := by
  have hlog : IntervalIntegrable (fun s : ℝ => Real.log (T - s)) volume S T := by
    have h := (intervalIntegral.intervalIntegrable_log' (a := T - S) (b := 0)).comp_sub_left T
    convert h using 2 <;> ring
  have hc : IntervalIntegrable (fun _ : ℝ => Real.log (2 * T)) volume S T :=
    intervalIntegrable_const
  change IntervalIntegrable (fun s => Real.log (2 * T) - Real.log (T - s)) volume S T
  exact hc.sub hlog

/-- The elementary rational factor in a backward step has its exact logarithmic integral. -/
theorem integral_backwardRational_eq {τ S B : ℝ} (hτ : 0 ≤ τ) (hτS : τ < S)
    (hSB : S ≤ B) :
    ∫ s in S..B, τ / (s * (s - τ)) =
      Real.log ((B - τ) / (S - τ)) - Real.log (B / S) := by
  have hS : 0 < S := lt_of_le_of_lt hτ hτS
  have hB : 0 < B := lt_of_lt_of_le hS hSB
  have hshift (x : ℝ) (hx : x ∈ Set.uIcc S B) : x - τ ≠ 0 := by
    rw [uIcc_of_le hSB] at hx
    exact (sub_pos.mpr (lt_of_lt_of_le hτS hx.1)).ne'
  have hbase (x : ℝ) (hx : x ∈ Set.uIcc S B) : x ≠ 0 := by
    rw [uIcc_of_le hSB] at hx
    exact (lt_of_lt_of_le hS hx.1).ne'
  have hcontShift : ContinuousOn (fun x : ℝ => x - τ) (Set.uIcc S B) :=
    continuousOn_id.sub continuousOn_const
  have hinvShift : IntervalIntegrable (fun s : ℝ => 1 / (s - τ)) volume S B :=
    intervalIntegral.intervalIntegrable_one_div hshift hcontShift
  have hinv : IntervalIntegrable (fun s : ℝ => 1 / s) volume S B :=
    intervalIntegral.intervalIntegrable_one_div hbase continuousOn_id
  calc
    _ = ∫ s in S..B, (1 / (s - τ) - 1 / s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hSB] at hs
      have hsτ : s - τ ≠ 0 := hshift s (uIcc_of_le hSB ▸ hs)
      have hs0 : s ≠ 0 := hbase s (uIcc_of_le hSB ▸ hs)
      field_simp
      ring
    _ = (∫ s in S..B, 1 / (s - τ)) - ∫ s in S..B, 1 / s :=
      intervalIntegral.integral_sub hinvShift hinv
    _ = Real.log ((B - τ) / (S - τ)) - Real.log (B / S) := by
      rw [intervalIntegral.integral_comp_sub_right]
      simp only [one_div, integral_inv_of_pos (sub_pos.mpr hτS)
        (sub_pos.mpr (lt_of_lt_of_le hτS hSB)), integral_inv_of_pos hS hB]

/-- Extending the logarithmic primitive to a later endpoint can only decrease it. -/
theorem integral_backwardRational_le {τ S B : ℝ} (hτ : 0 ≤ τ) (hτS : τ < S)
    (hSB : S ≤ B) :
    ∫ s in S..B, τ / (s * (s - τ)) ≤ Real.log (S / (S - τ)) := by
  have hS : 0 < S := lt_of_le_of_lt hτ hτS
  have hB : 0 < B := lt_of_lt_of_le hS hSB
  have hBτ : 0 < B - τ := sub_pos.mpr (lt_of_lt_of_le hτS hSB)
  have hSτ : 0 < S - τ := sub_pos.mpr hτS
  rw [integral_backwardRational_eq hτ hτS hSB]
  have hidentity :
      Real.log ((B - τ) / (S - τ)) - Real.log (B / S) =
        Real.log (S / (S - τ)) - Real.log (B / (B - τ)) := by
    rw [Real.log_div hBτ.ne' hSτ.ne', Real.log_div hB.ne' hS.ne',
      Real.log_div hS.ne' hSτ.ne', Real.log_div hB.ne' hBτ.ne']
    ring
  rw [hidentity]
  apply sub_le_self
  apply Real.log_nonneg
  rw [le_div_iff₀ hBτ]
  nlinarith

/-- The logarithmic primitive of the rational factor is controlled by the previous
backward weight, including when `τ` is close to the left endpoint `S`. -/
theorem logRatio_le_scaled_backwardWeight {τ S : ℝ} (hτ : 0 ≤ τ) (hτS : τ < S) :
    Real.log (S / (S - τ)) ≤ (2 / Real.log 2 + 2) * (τ / S) * backwardWeight S τ := by
  have hS : 0 < S := lt_of_le_of_lt hτ hτS
  have hden : 0 < S - τ := sub_pos.mpr hτS
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx : 0 ≤ τ / S := div_nonneg hτ hS.le
  have hW : Real.log 2 ≤ backwardWeight S τ := backwardWeight_ge_log_two hτ hτS
  have hW0 : 0 ≤ backwardWeight S τ := le_trans hlog2.le hW
  have hrelation : backwardWeight S τ = Real.log 2 + Real.log (S / (S - τ)) := by
    rw [backwardWeight_eq_log_ratio hS hτS]
    have hm : 2 * S / (S - τ) = 2 * (S / (S - τ)) := by field_simp
    rw [hm, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (div_ne_zero hS.ne' hden.ne')]
  by_cases hxhalf : τ / S ≤ 1 / 2
  · have hτhalf : τ ≤ S / 2 := by
      have h := (div_le_iff₀ hS).mp hxhalf
      nlinarith
    have hlogle : Real.log (S / (S - τ)) ≤ S / (S - τ) - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hS hden)
    have hratio : S / (S - τ) - 1 ≤ 2 * (τ / S) := by
      rw [sub_le_iff_le_add, div_le_iff₀ hden]
      field_simp [hS.ne']
      nlinarith [mul_nonneg hτ (sub_nonneg.mpr (by linarith : 2 * τ ≤ S))]
    have hcoef : 0 < 2 / Real.log 2 := div_pos (by norm_num) hlog2
    have hsmall : 2 * (τ / S) ≤ (2 / Real.log 2) * (τ / S) * backwardWeight S τ := by
      calc
        _ = (2 / Real.log 2) * (τ / S) * Real.log 2 := by field_simp
        _ ≤ _ := by
          exact mul_le_mul_of_nonneg_left hW (mul_nonneg hcoef.le hx)
    calc
      Real.log (S / (S - τ)) ≤ 2 * (τ / S) := hlogle.trans hratio
      _ ≤ (2 / Real.log 2) * (τ / S) * backwardWeight S τ := hsmall
      _ ≤ (2 / Real.log 2 + 2) * (τ / S) * backwardWeight S τ := by
        have := mul_nonneg hx hW0
        nlinarith

  · have hxhalf' : 1 / 2 < τ / S := lt_of_not_ge hxhalf
    have hlarge : Real.log (S / (S - τ)) ≤ backwardWeight S τ := by
      rw [hrelation]
      linarith [hlog2]
    have hcoef : 0 < 2 / Real.log 2 := div_pos (by norm_num) hlog2
    have htwo : backwardWeight S τ ≤ 2 * (τ / S) * backwardWeight S τ := by
      have hxdiff : 0 ≤ 2 * (τ / S) - 1 := by linarith
      nlinarith [mul_nonneg hxdiff hW0]
    calc
      Real.log (S / (S - τ)) ≤ backwardWeight S τ := hlarge
      _ ≤ 2 * (τ / S) * backwardWeight S τ := htwo
      _ ≤ (2 / Real.log 2 + 2) * (τ / S) * backwardWeight S τ := by
        have := mul_nonneg hx hW0
        nlinarith

/-- The complete unweighted rational factor has the scale needed for backward iteration. -/
theorem integral_backwardRational_scaled {τ S B : ℝ} (hτ : 0 ≤ τ) (hτS : τ < S)
    (hSB : S ≤ B) :
    ∫ s in S..B, τ / (s * (s - τ)) ≤
      (2 / Real.log 2 + 2) * (τ / S) * backwardWeight S τ := by
  exact (integral_backwardRational_le hτ hτS hSB).trans
    (logRatio_le_scaled_backwardWeight hτ hτS)

/-- The initial backward integral is logarithmic in the ratio of its two time scales. -/
theorem integral_backwardWeight_initial {S T : ℝ} (hS : 0 < S) (hST : 2 * S ≤ T) :
    ∫ s in S..T, (1 / s) * backwardWeight T s ≤
      (4 + 4 / Real.log 2) * Real.log (T / S) := by
  have hTpos : 0 < T := by linarith
  have hmid : S ≤ T / 2 := by linarith
  have hmidpos : 0 < T / 2 := by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog4le : Real.log 4 ≤ 4 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hST' : S ≤ T := by linarith
  have hweight : IntervalIntegrable (backwardWeight T) volume S T :=
    backwardWeight_intervalIntegrable
  have hinvCont : ContinuousOn (fun s : ℝ => 1 / s) (Set.uIcc S T) := by
    apply continuousOn_const.div continuousOn_id
    intro s hs
    rw [uIcc_of_le hST'] at hs
    exact (lt_of_lt_of_le hS hs.1).ne'
  have hsubLo : Set.uIcc S (T / 2) ⊆ Set.uIcc S T := by
    rw [uIcc_of_le hmid, uIcc_of_le hST']
    exact Icc_subset_Icc_right (by linarith)
  have hsubHi : Set.uIcc (T / 2) T ⊆ Set.uIcc S T := by
    rw [uIcc_of_le hST', uIcc_of_le (by linarith : T / 2 ≤ T)]
    exact Icc_subset_Icc_left hmid
  have hweightLo : IntervalIntegrable (backwardWeight T) volume S (T / 2) :=
    hweight.mono_set hsubLo
  have hweightHi : IntervalIntegrable (backwardWeight T) volume (T / 2) T :=
    hweight.mono_set hsubHi
  have hinvLo : IntervalIntegrable (fun s : ℝ => 1 / s) volume S (T / 2) := by
    apply intervalIntegral.intervalIntegrable_one_div
    · intro s hs
      rw [uIcc_of_le hmid] at hs
      exact (lt_of_lt_of_le hS hs.1).ne'
    · exact continuousOn_id
  have hinvLoCont : ContinuousOn (fun s : ℝ => 1 / s) (Set.uIcc S (T / 2)) := by
    apply continuousOn_const.div continuousOn_id
    intro s hs
    rw [uIcc_of_le hmid] at hs
    exact (lt_of_lt_of_le hS hs.1).ne'
  have hprodLo : IntervalIntegrable (fun s : ℝ => (1 / s) * backwardWeight T s)
      volume S (T / 2) := hweightLo.continuousOn_mul hinvLoCont
  have hprodHi : IntervalIntegrable (fun s : ℝ => (1 / s) * backwardWeight T s)
      volume (T / 2) T := hweightHi.continuousOn_mul (hinvCont.mono hsubHi)
  have hLow :
      ∫ s in S..T / 2, (1 / s) * backwardWeight T s ≤
        4 * Real.log (T / S) := by
    have hconst : IntervalIntegrable (fun s : ℝ => Real.log 4 * (1 / s)) volume S (T / 2) :=
      hinvLo.const_mul _
    have hpoint : ∀ s ∈ Icc S (T / 2),
        (1 / s) * backwardWeight T s ≤ Real.log 4 * (1 / s) := by
      intro s hs
      have hspos : 0 < s := lt_of_lt_of_le hS hs.1
      have hws : backwardWeight T s ≤ Real.log 4 :=
        backwardWeight_le_log_four hTpos (by linarith [hs.2])
      calc
        (1 / s) * backwardWeight T s ≤ (1 / s) * Real.log 4 :=
          mul_le_mul_of_nonneg_left hws (by positivity)
        _ = Real.log 4 * (1 / s) := by ring
    calc
      _ ≤ ∫ s in S..T / 2, Real.log 4 * (1 / s) :=
        intervalIntegral.integral_mono_on (by linarith) hprodLo hconst hpoint
      _ = Real.log 4 * Real.log ((T / 2) / S) := by
        rw [intervalIntegral.integral_const_mul]
        simp only [one_div, integral_inv_of_pos hS hmidpos]
      _ ≤ 4 * Real.log (T / S) := by
        have hratio : (T / 2) / S ≤ T / S :=
          div_le_div_of_nonneg_right (by linarith) hS.le
        have hlogmono : Real.log ((T / 2) / S) ≤ Real.log (T / S) :=
          Real.log_le_log (div_pos hmidpos hS) hratio
        have hlogarg : 0 ≤ Real.log ((T / 2) / S) :=
          Real.log_nonneg (by rw [le_div_iff₀ hS]; linarith)
        exact mul_le_mul hlog4le hlogmono hlogarg (by norm_num)
  have hHigh :
      ∫ s in T / 2..T, (1 / s) * backwardWeight T s ≤ 4 := by
    have hconst : IntervalIntegrable
        (fun s : ℝ => (2 / T) * backwardWeight T s) volume (T / 2) T :=
      hweightHi.const_mul _
    have hpoint : ∀ s ∈ Ioo (T / 2) T,
        (1 / s) * backwardWeight T s ≤ (2 / T) * backwardWeight T s := by
      intro s hs
      have hspos : 0 < s := by nlinarith [hs.1]
      have hw : 0 ≤ backwardWeight T s :=
        backwardWeight_nonneg hTpos (by linarith) hs.2
      have hrecip : 1 / s ≤ 2 / T := by
        rw [div_le_div_iff₀ hspos hTpos]
        nlinarith [hs.1]
      exact mul_le_mul_of_nonneg_right hrecip hw
    calc
      _ ≤ ∫ s in T / 2..T, (2 / T) * backwardWeight T s :=
        intervalIntegral.integral_mono_on_of_le_Ioo (by linarith) hprodHi hconst hpoint
      _ = 2 / T * ∫ s in T / 2..T, backwardWeight T s := by
        rw [intervalIntegral.integral_const_mul]
      _ = Real.log 4 + 1 := by rw [integral_backwardWeight_upperHalf hTpos]; field_simp
      _ ≤ 4 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
        linarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hprodLo hprodHi
  have hlogratio : Real.log 2 ≤ Real.log (T / S) := by
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ hS]
    linarith
  have hhigh : (4 : ℝ) ≤ 4 / Real.log 2 * Real.log (T / S) := by
    calc
      4 = (4 / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ (4 / Real.log 2) * Real.log (T / S) :=
        mul_le_mul_of_nonneg_left hlogratio (div_nonneg (by norm_num) hlog2.le)
  calc
    _ = (∫ s in S..T / 2, (1 / s) * backwardWeight T s) +
        ∫ s in T / 2..T, (1 / s) * backwardWeight T s := hsplit.symm
    _ ≤ 4 * Real.log (T / S) + 4 := add_le_add hLow hHigh
    _ ≤ (4 + 4 / Real.log 2) * Real.log (T / S) := by linarith

/-- The outer rational factor in the iterated backward-block estimate. -/
theorem integral_backwardBlock_outer {τ S T : ℝ} (hτ : 0 ≤ τ) (hτS : τ < S)
    (hS : 0 < S) (hblock : 4 * S ≤ T) :
    ∫ s in S..T, (τ / (s * (s - τ))) * backwardWeight T s ≤
      (24 / Real.log 2 + 8) * (τ / S) * backwardWeight S τ := by
  have hTpos : 0 < T := by linarith
  have hST : S ≤ T := by linarith
  have hmid : S ≤ T / 2 := by linarith
  have hmidT : T / 2 ≤ T := by linarith
  have hSpos : 0 < S := hS
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog4le : Real.log 4 ≤ 4 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hweight : IntervalIntegrable (backwardWeight T) volume S T :=
    backwardWeight_intervalIntegrable
  have hsubLo : Set.uIcc S (T / 2) ⊆ Set.uIcc S T := by
    rw [uIcc_of_le hmid, uIcc_of_le hST]
    exact Icc_subset_Icc_right hmidT
  have hsubHi : Set.uIcc (T / 2) T ⊆ Set.uIcc S T := by
    rw [uIcc_of_le hST, uIcc_of_le hmidT]
    exact Icc_subset_Icc_left hmid
  have hweightLo : IntervalIntegrable (backwardWeight T) volume S (T / 2) :=
    hweight.mono_set hsubLo
  have hweightHi : IntervalIntegrable (backwardWeight T) volume (T / 2) T :=
    hweight.mono_set hsubHi
  have hRcont : ContinuousOn (fun s : ℝ => τ / (s * (s - τ))) (Set.uIcc S T) := by
    apply continuousOn_const.div (continuousOn_id.mul
      (continuousOn_id.sub continuousOn_const))
    intro s hs
    rw [uIcc_of_le hST] at hs
    have hspos : 0 < s := lt_of_lt_of_le hS hs.1
    have hsdpos : 0 < s - τ := sub_pos.mpr (lt_of_lt_of_le hτS hs.1)
    exact mul_ne_zero hspos.ne' hsdpos.ne'
  have hRcontLo : ContinuousOn (fun s : ℝ => τ / (s * (s - τ)))
      (Icc S (T / 2)) := by
    rw [← uIcc_of_le hmid]
    exact hRcont.mono hsubLo
  have hRintLo : IntervalIntegrable (fun s : ℝ => τ / (s * (s - τ)))
      volume S (T / 2) := hRcontLo.intervalIntegrable_of_Icc hmid
  have hprodLo : IntervalIntegrable
      (fun s : ℝ => (τ / (s * (s - τ))) * backwardWeight T s) volume S (T / 2) :=
    hweightLo.continuousOn_mul (hRcont.mono hsubLo)
  have hprodHi : IntervalIntegrable
      (fun s : ℝ => (τ / (s * (s - τ))) * backwardWeight T s) volume (T / 2) T :=
    hweightHi.continuousOn_mul (hRcont.mono hsubHi)
  have hlow :
      ∫ s in S..T / 2, (τ / (s * (s - τ))) * backwardWeight T s ≤
        4 * (2 / Real.log 2 + 2) * (τ / S) * backwardWeight S τ := by
    have hRconst : IntervalIntegrable
        (fun s : ℝ => Real.log 4 * (τ / (s * (s - τ)))) volume S (T / 2) :=
      hRintLo.const_mul _
    have hpoint : ∀ s ∈ Icc S (T / 2),
        (τ / (s * (s - τ))) * backwardWeight T s ≤
          Real.log 4 * (τ / (s * (s - τ))) := by
      intro s hs
      have hspos : 0 < s := lt_of_lt_of_le hS hs.1
      have hsdpos : 0 < s - τ := sub_pos.mpr (lt_of_lt_of_le hτS hs.1)
      have hRnonneg : 0 ≤ τ / (s * (s - τ)) :=
        div_nonneg hτ (mul_nonneg hspos.le hsdpos.le)
      have hws : backwardWeight T s ≤ Real.log 4 :=
        backwardWeight_le_log_four hTpos (by linarith [hs.2])
      calc
        _ ≤ (τ / (s * (s - τ))) * Real.log 4 :=
          mul_le_mul_of_nonneg_left hws hRnonneg
        _ = _ := by ring
    have hRbound := integral_backwardRational_scaled hτ hτS hmid
    have hSweight : 0 ≤ (2 / Real.log 2 + 2) * (τ / S) * backwardWeight S τ := by
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hcoef : 0 ≤ 2 / Real.log 2 + 2 := by positivity
      have hx : 0 ≤ τ / S := div_nonneg hτ hS.le
      have hW : 0 ≤ backwardWeight S τ := backwardWeight_nonneg hS hτ hτS
      exact mul_nonneg (mul_nonneg hcoef hx) hW
    have hlog4bound :
        ∫ s in S..T / 2, Real.log 4 * (τ / (s * (s - τ))) ≤
          4 * ((2 / Real.log 2 + 2) * (τ / S) * backwardWeight S τ) := by
      rw [intervalIntegral.integral_const_mul]
      calc
        _ ≤ Real.log 4 * ((2 / Real.log 2 + 2) * (τ / S) * backwardWeight S τ) :=
          mul_le_mul_of_nonneg_left hRbound hlog4
        _ ≤ _ := mul_le_mul_of_nonneg_right hlog4le hSweight
    calc
      _ ≤ ∫ s in S..T / 2, Real.log 4 * (τ / (s * (s - τ))) :=
        intervalIntegral.integral_mono_on (by linarith) hprodLo hRconst hpoint
      _ ≤ _ := by nlinarith [hlog4bound]
  have hhigh :
      ∫ s in T / 2..T, (τ / (s * (s - τ))) * backwardWeight T s ≤
        (16 / Real.log 2) * (τ / S) * backwardWeight S τ := by
    have hconst : IntervalIntegrable
        (fun s : ℝ => (8 * τ / T ^ 2) * backwardWeight T s) volume (T / 2) T :=
      hweightHi.const_mul _
    have hpoint : ∀ s ∈ Ioo (T / 2) T,
        (τ / (s * (s - τ))) * backwardWeight T s ≤
          (8 * τ / T ^ 2) * backwardWeight T s := by
      intro s hs
      have hspos : 0 < s := by nlinarith [hs.1]
      have hsdpos : 0 < s - τ := by nlinarith [hs.1, hτS]
      have hw : 0 ≤ backwardWeight T s := backwardWeight_nonneg hTpos (by linarith) hs.2
      have hτT : τ ≤ T / 4 := by nlinarith [hτS, hblock]
      have hprod : T ^ 2 / 8 ≤ s * (s - τ) := by
        have h1 : T / 2 ≤ s := le_of_lt hs.1
        have h2 : T / 4 ≤ s - τ := by nlinarith [hs.1, hτT]
        have hmul := mul_le_mul h1 h2 (by positivity : 0 ≤ T / 4) hspos.le
        nlinarith [hmul]
      have hR : τ / (s * (s - τ)) ≤ 8 * τ / T ^ 2 := by
        rw [div_le_div_iff₀ (mul_pos hspos hsdpos) (sq_pos_of_pos hTpos)]
        have hm := mul_le_mul_of_nonneg_left hprod
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hτ)
        nlinarith [hm]
      exact mul_le_mul_of_nonneg_right hR hw
    have hupper : ∫ s in T / 2..T, backwardWeight T s ≤ 2 * T := by
      rw [integral_backwardWeight_upperHalf hTpos]
      have hlog4 : Real.log 4 + 1 ≤ 4 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
        linarith
      nlinarith
    have hW : 0 ≤ backwardWeight S τ :=
      backwardWeight_nonneg hS hτ hτS
    have hWs : Real.log 2 ≤ backwardWeight S τ :=
      backwardWeight_ge_log_two hτ hτS
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hcoeff : 0 ≤ 8 * τ / T ^ 2 := by positivity
    calc
      _ ≤ ∫ s in T / 2..T, (8 * τ / T ^ 2) * backwardWeight T s :=
        intervalIntegral.integral_mono_on_of_le_Ioo (by linarith) hprodHi hconst hpoint
      _ = (8 * τ / T ^ 2) * ∫ s in T / 2..T, backwardWeight T s := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ (8 * τ / T ^ 2) * (2 * T) :=
        mul_le_mul_of_nonneg_left hupper hcoeff
      _ ≤ (16 / Real.log 2) * (τ / S) * backwardWeight S τ := by
        have hscale : τ / T ≤ (1 / Real.log 2) * (τ / S) * backwardWeight S τ := by
          have hx : 0 ≤ τ / S := div_nonneg hτ hS.le
          have hcoef : 0 ≤ 1 / Real.log 2 := one_div_nonneg.mpr hlog2.le
          calc
            τ / T ≤ τ / S := div_le_div_of_nonneg_left hτ hS hST
            _ = (1 / Real.log 2) * (τ / S) * Real.log 2 := by field_simp
            _ ≤ (1 / Real.log 2) * (τ / S) * backwardWeight S τ :=
              mul_le_mul_of_nonneg_left hWs (mul_nonneg hcoef hx)
        calc
          8 * τ / T ^ 2 * (2 * T) = 16 * (τ / T) := by
            field_simp [hTpos.ne']
            ring
          _ ≤ 16 * ((1 / Real.log 2) * (τ / S) * backwardWeight S τ) :=
            mul_le_mul_of_nonneg_left hscale (by norm_num)
          _ = (16 / Real.log 2) * (τ / S) * backwardWeight S τ := by ring
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hprodLo hprodHi
  calc
    _ = (∫ s in S..T / 2, (τ / (s * (s - τ))) * backwardWeight T s) +
        ∫ s in T / 2..T, (τ / (s * (s - τ))) * backwardWeight T s := hsplit.symm
    _ ≤ 4 * (2 / Real.log 2 + 2) * (τ / S) * backwardWeight S τ +
        (16 / Real.log 2) * (τ / S) * backwardWeight S τ := add_le_add hlow hhigh
    _ = (24 / Real.log 2 + 8) * (τ / S) * backwardWeight S τ := by ring

/-! ### Scalar renewal estimates used by the backward iteration -/


/-- The logarithmic kernel used by the scalar collision envelope has an exact cumulative
integral. The reciprocal substitution sends `1 - log u` to `1 + log (1/u)`. -/
theorem integral_inv_mul_one_sub_log_sq_Ioc {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    ∫ u in Ioc 0 h, (u * (1 - Real.log u) ^ 2)⁻¹ = (1 - Real.log h)⁻¹ := by
  have hrec : 1 ≤ h⁻¹ := by
    rw [one_le_inv₀ hh]
    exact hh1
  let g : ℝ → ℝ := (Ici h⁻¹).indicator (fun y => (y * (1 + Real.log y) ^ 2)⁻¹)
  have hchange :
      (∫ x in Ioi 0, (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) * g (x ^ (-1 : ℝ))) =
        ∫ y in Ioi 0, g y := integral_comp_rpow_Ioi g (by norm_num)
  have hleft :
      (∫ x in Ioi 0, (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) * g (x ^ (-1 : ℝ))) =
        ∫ x in Ioi 0, (Iic h).indicator (fun u => (u * (1 - Real.log u) ^ 2)⁻¹) x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hxpos : 0 < x := hx
    have hlogx : Real.log (x⁻¹) = -Real.log x := by rw [Real.log_inv]
    have hpow : x ^ ((-1 : ℝ) - 1) = x⁻¹ ^ 2 := by
      calc
        x ^ ((-1 : ℝ) - 1) = x ^ ((-1 : ℝ) * 2) := by congr 1; ring
        _ = (x ^ (-1 : ℝ)) ^ (2 : ℝ) := by rw [Real.rpow_mul hxpos.le]
        _ = (x ^ (-1 : ℝ)) ^ (2 : ℕ) := Real.rpow_natCast _ 2
        _ = x⁻¹ ^ 2 := by rw [Real.rpow_neg_one x]
    have hinvpow : x ^ (-1 : ℝ) = x⁻¹ := by rw [Real.rpow_neg_one x]
    change |(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1) * g (x ^ (-1 : ℝ)) =
      (Iic h).indicator (fun u => (u * (1 - Real.log u) ^ 2)⁻¹) x
    rw [hpow, hinvpow]
    dsimp [g]
    by_cases hxh : x ≤ h
    · have hxhi : h⁻¹ ≤ x⁻¹ := (inv_le_inv₀ hh hxpos).mpr hxh
      rw [indicator_of_mem (show x⁻¹ ∈ Ici h⁻¹ from hxhi),
        indicator_of_mem (show x ∈ Iic h from hxh), hlogx]
      have hxne : x ≠ 0 := hxpos.ne'
      rw [sub_eq_add_neg]
      norm_num
      field_simp [hxne]
    · have hxnot : ¬ x⁻¹ ∈ Ici h⁻¹ := by
        change ¬ h⁻¹ ≤ x⁻¹
        intro hxle
        exact (not_le_of_gt (lt_of_not_ge hxh)) ((inv_le_inv₀ hh hxpos).mp hxle)
      have hxnot' : x ∉ Iic h := not_le.mpr (lt_of_not_ge hxh)
      simp [Set.indicator, hxnot, hxnot']
  have hleft' :
      (∫ x in Ioi 0, (Iic h).indicator (fun u => (u * (1 - Real.log u) ^ 2)⁻¹) x) =
        ∫ u in Ioc 0 h, (u * (1 - Real.log u) ^ 2)⁻¹ := by
    rw [setIntegral_indicator measurableSet_Iic]
    congr 1
  have hright : ∫ y in Ioi 0, g y =
      ∫ y in Ioi h⁻¹, (y * (1 + Real.log y) ^ 2)⁻¹ := by
    rw [show g = (Ici h⁻¹).indicator
        (fun y => (y * (1 + Real.log y) ^ 2)⁻¹) by rfl]
    rw [setIntegral_indicator measurableSet_Ici]
    have hset : Ioi 0 ∩ Ici h⁻¹ = Ici h⁻¹ := by
      ext y
      simp only [mem_inter_iff, mem_Ioi, mem_Ici]
      constructor
      · exact And.right
      · intro hy
        exact ⟨lt_of_lt_of_le (by positivity : (0 : ℝ) < h⁻¹) hy, hy⟩
    rw [hset, integral_Ici_eq_integral_Ioi]
  have hderiv (y : ℝ) (hy : y ∈ Ici h⁻¹) :
      HasDerivAt (fun v => -(1 + Real.log v)⁻¹)
        ((y * (1 + Real.log y) ^ 2)⁻¹) y := by
    have hypos : 0 < y := lt_of_lt_of_le (by positivity : (0 : ℝ) < h⁻¹) hy
    have hyge : 1 ≤ y := le_trans hrec hy
    have hlog : 0 ≤ Real.log y := Real.log_nonneg hyge
    have hden : 1 + Real.log y ≠ 0 := by
      linarith
    have hlog' := (Real.hasDerivAt_log hypos.ne' : HasDerivAt Real.log y⁻¹ y)
    convert (hlog'.const_add 1).inv hden |>.neg using 1
    all_goals field_simp [hypos.ne', hden]
  have htail : Tendsto (fun y : ℝ => -(1 + Real.log y)⁻¹) atTop (nhds 0) := by
    have hlog : Tendsto (fun y : ℝ => 1 + Real.log y) atTop atTop :=
      tendsto_atTop_mono (by intro y; linarith) Real.tendsto_log_atTop
    convert hlog.inv_tendsto_atTop.neg using 1
    all_goals simp
  have hnonneg : ∀ y ∈ Ioi h⁻¹, 0 ≤ (y * (1 + Real.log y) ^ 2)⁻¹ := by
    intro y hy
    have hyge : 1 ≤ y := le_trans hrec (le_of_lt hy)
    have hlog : 0 ≤ Real.log y := Real.log_nonneg hyge
    positivity
  have hint : IntegrableOn (fun y => (y * (1 + Real.log y) ^ 2)⁻¹) (Ioi h⁻¹) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv hnonneg htail
  have hexact := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htail
  rw [← hleft', ← hleft, hchange, hright, hexact]
  rw [Real.log_inv]
  ring

/-- Integrability of the same shifted-log reciprocal kernel on its improper interval. -/
theorem integrableOn_inv_mul_one_sub_log_sq_Ioc {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    IntegrableOn (fun u => (u * (1 - Real.log u) ^ 2)⁻¹) (Ioc 0 h) := by
  have hrec : 1 ≤ h⁻¹ := by
    rw [one_le_inv₀ hh]
    exact hh1
  let g : ℝ → ℝ := (Ici h⁻¹).indicator (fun y => (y * (1 + Real.log y) ^ 2)⁻¹)
  have hgIci : IntegrableOn (fun y => (y * (1 + Real.log y) ^ 2)⁻¹) (Ici h⁻¹) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    have hderiv (y : ℝ) (hy : y ∈ Ici h⁻¹) :
        HasDerivAt (fun v => -(1 + Real.log v)⁻¹)
          ((y * (1 + Real.log y) ^ 2)⁻¹) y := by
      have hypos : 0 < y := lt_of_lt_of_le (by positivity : (0 : ℝ) < h⁻¹) hy
      have hyge : 1 ≤ y := le_trans hrec hy
      have hlog : 0 ≤ Real.log y := Real.log_nonneg hyge
      have hden : 1 + Real.log y ≠ 0 := by
        linarith
      have hlog' := (Real.hasDerivAt_log hypos.ne' : HasDerivAt Real.log y⁻¹ y)
      convert (hlog'.const_add 1).inv hden |>.neg using 1
      all_goals field_simp [hypos.ne', hden]
    have htail : Tendsto (fun y : ℝ => -(1 + Real.log y)⁻¹) atTop (nhds 0) := by
      have hlog : Tendsto (fun y : ℝ => 1 + Real.log y) atTop atTop :=
        tendsto_atTop_mono (by intro y; linarith) Real.tendsto_log_atTop
      convert hlog.inv_tendsto_atTop.neg using 1
      all_goals simp
    exact integrableOn_Ioi_deriv_of_nonneg' hderiv (by
      intro y hy
      have hyge : 1 ≤ y := le_trans hrec (le_of_lt hy)
      have hlog : 0 ≤ Real.log y := Real.log_nonneg hyge
      positivity) htail
  have hg : Integrable g := by
    dsimp [g]
    exact (integrable_indicator_iff measurableSet_Ici).2 hgIci
  have htrans : IntegrableOn
      (fun x => (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) * g (x ^ (-1 : ℝ))) (Ioi 0) := by
    simpa only [smul_eq_mul] using
      (integrableOn_Ioi_comp_rpow_iff g (by norm_num : (-1 : ℝ) ≠ 0)).2 hg.integrableOn
  have hpoint : ∀ x ∈ Ioi 0,
      (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) * g (x ^ (-1 : ℝ)) =
        (Iic h).indicator (fun u => (u * (1 - Real.log u) ^ 2)⁻¹) x := by
    intro x hx
    have hxpos : 0 < x := hx
    have hlogx : Real.log (x⁻¹) = -Real.log x := by rw [Real.log_inv]
    have hpow : x ^ ((-1 : ℝ) - 1) = x⁻¹ ^ 2 := by
      calc
        x ^ ((-1 : ℝ) - 1) = x ^ ((-1 : ℝ) * 2) := by congr 1; ring
        _ = (x ^ (-1 : ℝ)) ^ (2 : ℝ) := by rw [Real.rpow_mul hxpos.le]
        _ = (x ^ (-1 : ℝ)) ^ (2 : ℕ) := Real.rpow_natCast _ 2
        _ = x⁻¹ ^ 2 := by rw [Real.rpow_neg_one x]
    have hinvpow : x ^ (-1 : ℝ) = x⁻¹ := by rw [Real.rpow_neg_one x]
    change |(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1) * g (x ^ (-1 : ℝ)) =
      (Iic h).indicator (fun u => (u * (1 - Real.log u) ^ 2)⁻¹) x
    rw [hpow, hinvpow]
    dsimp [g]
    by_cases hxh : x ≤ h
    · have hxhi : h⁻¹ ≤ x⁻¹ := (inv_le_inv₀ hh hxpos).mpr hxh
      rw [indicator_of_mem (show x⁻¹ ∈ Ici h⁻¹ from hxhi),
        indicator_of_mem (show x ∈ Iic h from hxh), hlogx]
      have hxne : x ≠ 0 := hxpos.ne'
      rw [sub_eq_add_neg]
      norm_num
      field_simp [hxne]
    · have hxnot : ¬ x⁻¹ ∈ Ici h⁻¹ := by
        change ¬ h⁻¹ ≤ x⁻¹
        intro hxle
        exact (not_le_of_gt (lt_of_not_ge hxh)) ((inv_le_inv₀ hh hxpos).mp hxle)
      have hxnot' : x ∉ Iic h := not_le.mpr (lt_of_not_ge hxh)
      simp [Set.indicator, hxnot, hxnot']
  have hind : IntegrableOn
      ((Iic h).indicator (fun u => (u * (1 - Real.log u) ^ 2)⁻¹)) (Ioi 0) :=
    (integrableOn_congr_fun hpoint measurableSet_Ioi).mp htrans
  have hrestrict : IntegrableOn
      ((Iic h).indicator (fun u => (u * (1 - Real.log u) ^ 2)⁻¹)) (Ioc 0 h) :=
    hind.mono_set (fun _ hx => hx.1)
  exact hrestrict.congr_fun (fun x hx => by simp [Set.indicator, hx.2]) measurableSet_Ioc


/-- The scalar collision density has the pointwise logarithmic envelope required by the
backward-weight argument, uniformly on every parameter half-line `θ ≤ B`. -/
theorem exists_scalarDensity_le_logKernel (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ t : ℝ, θ ≤ B → 0 < t → t ≤ 1 →
      DeltaBose.scalarDensity θ t ≤ C / (t * (1 - Real.log t) ^ 2) := by
  obtain ⟨K, hK, hsmall⟩ := DeltaBose.exists_scalarDensity_le_log
  let δ := min (Real.exp (-(2 * |B| + 1))) (1 / 2)
  let c := Real.exp (B + 1)
  let H := 1 - Real.log δ
  let C := 4 * K + Real.exp 1 * Real.exp c * H ^ 2
  have hδ : 0 < δ := lt_min (Real.exp_pos _) (by norm_num)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hH : 0 < H := by
    dsimp [H]
    linarith [Real.log_neg hδ hδ1]
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun θ t hθ ht ht1 => ?_⟩
  have hL : 0 < 1 - Real.log t := by
    have hlog : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1
    linarith
  by_cases hsmallT : t ≤ δ
  · have hinput : t ≤ Real.exp (-(2 * |B| + 1)) := hsmallT.trans (min_le_left _ _)
    have hbound := hsmall θ B t hθ ht hinput
    have hlog : Real.log t ≤ -(2 * |B| + 1) := by
      exact (Real.log_le_log ht hinput).trans_eq (Real.log_exp _)
    have hLlarge : 1 ≤ -Real.log t := by
      have habs : 0 ≤ |B| := abs_nonneg B
      linarith
    have hloglt : Real.log t < 0 := by linarith
    have hfactor : (1 - Real.log t) ^ 2 ≤ 4 * (Real.log t) ^ 2 := by
      have hlinear : 1 - Real.log t ≤ 2 * (-Real.log t) := by linarith
      nlinarith [sq_nonneg (1 - Real.log t), sq_nonneg (-Real.log t)]
    have hden₁ : 0 < t * (Real.log t) ^ 2 := mul_pos ht (sq_pos_of_ne_zero (by
      exact ne_of_lt hloglt))
    have hden₂ : 0 < t * (1 - Real.log t) ^ 2 := mul_pos ht (sq_pos_of_pos hL)
    have hscaled : K / (t * (Real.log t) ^ 2) ≤
        (4 * K) / (t * (1 - Real.log t) ^ 2) := by
      rw [div_le_div_iff₀ hden₁ hden₂]
      have hmul := mul_le_mul_of_nonneg_left hfactor hK.le
      nlinarith [mul_le_mul_of_nonneg_left hmul ht.le]
    calc
      DeltaBose.scalarDensity θ t ≤ K / (t * (Real.log t) ^ 2) := hbound
      _ ≤ (4 * K) / (t * (1 - Real.log t) ^ 2) := hscaled
      _ ≤ C / (t * (1 - Real.log t) ^ 2) := by
        apply div_le_div_of_nonneg_right _ hden₂.le
        dsimp [C]
        exact le_add_of_nonneg_right (by positivity)
  · have hδt : δ < t := lt_of_not_ge hsmallT
    have hlogδ : Real.log δ ≤ Real.log t := Real.log_le_log hδ hδt.le
    have hLbound : 1 - Real.log t ≤ H := by dsimp [H]; linarith
    have hlarge := DeltaBose.scalarDensity_le_exp hθ ht
    have hexp : Real.exp (c * t) ≤ Real.exp c := by
      apply Real.exp_le_exp.mpr
      dsimp [c]
      have hc : 0 < Real.exp (B + 1) := Real.exp_pos _
      nlinarith
    have hden : 0 < t * (1 - Real.log t) ^ 2 := mul_pos ht (sq_pos_of_pos hL)
    have hscaled : Real.exp 1 / t * Real.exp c ≤
        (Real.exp 1 * Real.exp c * H ^ 2) / (t * (1 - Real.log t) ^ 2) := by
      rw [div_mul_eq_mul_div]
      have hLsq : (1 - Real.log t) ^ 2 ≤ H ^ 2 := by
        nlinarith [hLbound, hL, hH]
      have hcoef : 0 ≤ Real.exp 1 * Real.exp c := by positivity
      calc
        Real.exp 1 * Real.exp c / t =
            (Real.exp 1 * Real.exp c) * (1 - Real.log t) ^ 2 /
              (t * (1 - Real.log t) ^ 2) := by field_simp [ht.ne']
        _ ≤ (Real.exp 1 * Real.exp c) * H ^ 2 /
              (t * (1 - Real.log t) ^ 2) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLsq hcoef) hden.le
    calc
      DeltaBose.scalarDensity θ t ≤ Real.exp 1 / t * Real.exp (Real.exp (B + 1) * t) := hlarge
      _ ≤ Real.exp 1 / t * Real.exp c := by
        exact mul_le_mul_of_nonneg_left hexp (div_nonneg (Real.exp_nonneg _) ht.le)
      _ ≤ (Real.exp 1 * Real.exp c * H ^ 2) / (t * (1 - Real.log t) ^ 2) := hscaled
      _ ≤ C / (t * (1 - Real.log t) ^ 2) := by
        apply div_le_div_of_nonneg_right _ hden.le
        dsimp [C]
        exact le_add_of_nonneg_left (by positivity)

/-- On compact parameter intervals, the Dickman collision density has uniform logarithmic pointwise and cumulative integral bounds and is integrable on each interval `(0,t]`. -/
theorem exists_G_log_bounds (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ϑ ∈ Set.Icc (-A) A, ∀ h : ℝ, 0 < h → h ≤ 1 →
      DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) h ≤
        C / (h * (1 + Real.log (1 / h)) ^ 2) ∧
      (IntegrableOn (fun r => DeltaBose.scalarDensity
          (ϑ - Real.eulerMascheroniConstant) r) (Ioc 0 h) ∧
        (∫ r in Ioc 0 h, DeltaBose.scalarDensity
          (ϑ - Real.eulerMascheroniConstant) r) ≤ C / (1 + Real.log (1 / h))) := by
  obtain ⟨C, hC, hbound⟩ := exists_scalarDensity_le_logKernel
    (A - Real.eulerMascheroniConstant)
  refine ⟨C, hC, fun ϑ hϑ h hh hh1 => ?_⟩
  have hθ : ϑ - Real.eulerMascheroniConstant ≤ A - Real.eulerMascheroniConstant :=
    sub_le_sub_right hϑ.2 _
  have hloginv (t : ℝ) (ht : 0 < t) : Real.log (1 / t) = -Real.log t := by
    rw [one_div, Real.log_inv]
  have hpt := hbound (ϑ - Real.eulerMascheroniConstant) h hθ hh hh1
  have hpoint : DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) h ≤
      C * (h * (1 - Real.log h) ^ 2)⁻¹ := by
    simpa only [div_eq_mul_inv] using hpt
  have hden : 1 - Real.log h = 1 + Real.log (1 / h) := by
    rw [hloginv h hh]
    ring
  have hpoint' : DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) h ≤
      C / (h * (1 + Real.log (1 / h)) ^ 2) := by
    rw [← hden]
    simpa only [div_eq_mul_inv] using hpoint
  have hGint : IntervalIntegrable
      (fun r => DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) r)
      volume 0 h := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hh.le]
    exact Renewal.integrableOn_scalarDensity_Ioc _ _
  have henvInt : IntervalIntegrable
      (fun r => (r * (1 - Real.log r) ^ 2)⁻¹) volume 0 h := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hh.le]
    exact integrableOn_inv_mul_one_sub_log_sq_Ioc hh hh1
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo (a := 0) (b := h)
    hh.le hGint (henvInt.const_mul C) (by
      intro r hr
      have hr0 : 0 < r := hr.1
      have hrh : r ≤ h := hr.2.le
      have hpr := hbound (ϑ - Real.eulerMascheroniConstant) r hθ hr0 (le_trans hrh hh1)
      simpa only [div_eq_mul_inv] using hpr)
  have hmono'' : (∫ r in 0..h,
        DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) r) ≤
      C * (∫ r in 0..h, (r * (1 - Real.log r) ^ 2)⁻¹) := by
    simpa only [intervalIntegral.integral_const_mul] using hmono
  have hmono' : (∫ r in Ioc 0 h,
        DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) r) ≤
      C * (∫ r in Ioc 0 h, (r * (1 - Real.log r) ^ 2)⁻¹) := by
    calc
      _ = ∫ r in 0..h, DeltaBose.scalarDensity
            (ϑ - Real.eulerMascheroniConstant) r := by
          rw [← intervalIntegral.integral_of_le hh.le]
      _ ≤ C * (∫ r in 0..h, (r * (1 - Real.log r) ^ 2)⁻¹) := hmono''
      _ = C * (∫ r in Ioc 0 h, (r * (1 - Real.log r) ^ 2)⁻¹) := by
          rw [intervalIntegral.integral_of_le hh.le]
  rw [integral_inv_mul_one_sub_log_sq_Ioc hh hh1] at hmono'
  rw [hden] at hmono'
  refine ⟨hpoint', ?_⟩
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hh.le] at hGint
    exact hGint
  · simpa only [div_eq_mul_inv] using hmono'

end Critical2DKPZ.Collision
