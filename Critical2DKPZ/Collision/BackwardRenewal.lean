/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Collision.BackwardWeights
public import Mathlib.MeasureTheory.Measure.Prod
public import Critical2DKPZ.SHF.DeltaBose.Measurability

/-! # Renewal-weighted backward integrals -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.Collision

open MeasureTheory
open Set
open scoped ENNReal

/-- The nonnegative integral over an ordered time triangle equals the corresponding iterated integral. -/
theorem lintegral_openTriangle_eq {f : ℝ × ℝ → ℝ≥0∞}
    (hf : Measurable f) {S T : ℝ} :
    ∫⁻ p in {p : ℝ × ℝ | S < p.1 ∧ p.1 < p.2 ∧ p.2 < T}, f p =
      ∫⁻ x in Ioo S T, ∫⁻ y in Ioo x T, f (x, y) := by
  let triangle : Set (ℝ × ℝ) := {p | S < p.1 ∧ p.1 < p.2 ∧ p.2 < T}
  have htriangle : MeasurableSet triangle := by
    dsimp [triangle]
    measurability
  have hfun (x y : ℝ) : triangle.indicator f (x, y) =
      if x ∈ Ioo S T then (Ioo x T).indicator (fun y => f (x, y)) y else 0 := by
    by_cases hx : x ∈ Ioo S T
    · by_cases hy : y ∈ Ioo x T
      · have hp : (x, y) ∈ triangle := by
          simpa [triangle, mem_Ioo] using ⟨hx.1, hy.1, hy.2⟩
        simp [hp, hx, hy]
      · have hp : (x, y) ∉ triangle := by
          intro h
          have h' : S < x ∧ x < y ∧ y < T := by simpa [triangle] using h
          exact hy ⟨h'.2.1, h'.2.2⟩
        simp [hp, hx, hy]
    · have hp : (x, y) ∉ triangle := by
        intro h
        have h' : S < x ∧ x < y ∧ y < T := by simpa [triangle] using h
        exact hx ⟨h'.1, lt_trans h'.2.1 h'.2.2⟩
      simp [hp, hx]
  have hinner (x : ℝ) :
      ∫⁻ y, (Ioo x T).indicator (fun y => f (x, y)) y =
        ∫⁻ y in Ioo x T, f (x, y) :=
    lintegral_indicator measurableSet_Ioo _
  calc
    _ = ∫⁻ p, triangle.indicator f p ∂(volume.prod volume) := by
      change ∫⁻ p in triangle, f p = _
      rw [← Measure.volume_eq_prod ℝ ℝ]
      rw [lintegral_indicator htriangle]
    _ = ∫⁻ x, ∫⁻ y, triangle.indicator f (x, y) ∂volume ∂volume :=
      lintegral_prod _ ((hf.indicator htriangle).aemeasurable)
    _ = ∫⁻ x, if x ∈ Ioo S T then ∫⁻ y in Ioo x T, f (x, y) else 0 ∂volume := by
      apply lintegral_congr
      intro x
      rw [show (fun y => triangle.indicator f (x, y)) =
          fun y => if x ∈ Ioo S T then (Ioo x T).indicator (fun y => f (x, y)) y else 0 by
        funext y
        exact hfun x y]
      by_cases hx : x ∈ Ioo S T <;> simp [hx, hinner]
    _ = ∫⁻ x in Ioo S T, ∫⁻ y in Ioo x T, f (x, y) := by
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro x
      simp only [Set.indicator, mem_Ioo]

/-- Exact integral of the backward logarithmic weight over a terminal segment. -/
theorem integral_backwardWeight_terminalSegment {T h : ℝ} (hT : 0 < T)
    (hh : 0 < h) :
    ∫ t in T - h / 2..T, backwardWeight T t =
      h / 2 * (Real.log (4 * T / h) + 1) := by
  have hlog : IntervalIntegrable (fun t : ℝ => Real.log (T - t)) volume (T - h / 2) T := by
    have h := (intervalIntegral.intervalIntegrable_log' (a := h / 2) (b := 0)).comp_sub_left T
    convert h using 2; ring
  have hc : IntervalIntegrable (fun _ : ℝ => Real.log (2 * T)) volume (T - h / 2) T :=
    intervalIntegrable_const
  change ∫ t in T - h / 2..T, (Real.log (2 * T) - Real.log (T - t)) = _
  rw [intervalIntegral.integral_sub hc hlog,
    intervalIntegral.integral_const, intervalIntegral.integral_comp_sub_left,
    integral_log]
  simp only [sub_self, zero_mul, sub_zero, add_zero]
  rw [smul_eq_mul]
  calc
    _ = h / 2 * (Real.log (2 * T) - Real.log (h / 2) + 1) := by ring_nf
    _ = h / 2 * (Real.log (4 * T / h) + 1) := by
      have hlogdiv : Real.log (2 * T) - Real.log (h / 2) = Real.log (4 * T / h) := by
        rw [← Real.log_div (by positivity : 2 * T ≠ 0) (by positivity : h / 2 ≠ 0)]
        congr 1
        field_simp
        ring
      rw [hlogdiv]

/-- The scalar renewal density convolved with a terminal backward weight is controlled by
the backward weight at the starting time. -/
theorem exists_backwardRenewal_inner_bound (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ϑ ∈ Set.Icc (-A) A, ∀ s T : ℝ,
      0 ≤ s → s < T → T < 1 →
        IntegrableOn (fun t =>
          DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (t - s) *
            backwardWeight T t) (Ioc s T) ∧
        (∫ t in Ioc s T,
          DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (t - s) *
            backwardWeight T t) ≤ C * backwardWeight T s / (-Real.log T) := by
  obtain ⟨CG, hCG, hG⟩ := exists_G_log_bounds A
  let C : ℝ := CG * (4 + 1 / Real.log 2)
  have hC : 0 < C := mul_pos hCG (by positivity)
  refine ⟨C, hC, ?_⟩
  intro ϑ hϑ s T hs hst hT
  have hTpos : 0 < T := lt_of_le_of_lt hs hst
  have hh : 0 < T - s := sub_pos.mpr hst
  have hhT : T - s ≤ 1 := by linarith
  have hM : 0 < -Real.log T := by
    have := Real.log_lt_log hTpos hT
    rw [Real.log_one] at this
    linarith
  have hW : 0 < backwardWeight T s := by
    have h := backwardWeight_ge_log_two hs (by linarith : s < T)
    exact lt_of_lt_of_le (Real.log_pos (by norm_num)) h
  have hL : 0 < 1 + Real.log (1 / (T - s)) := by
    have harg : 1 ≤ 1 / (T - s) := by
      rw [le_div_iff₀ hh]
      linarith
    have hlog : 0 ≤ Real.log (1 / (T - s)) := Real.log_nonneg harg
    linarith
  have hLgeM : -Real.log T ≤ 1 + Real.log (1 / (T - s)) := by
    have hlog := Real.log_le_log hh (sub_le_self T hs)
    have hloginv : Real.log (1 / (T - s)) = -Real.log (T - s) := by
      rw [one_div, Real.log_inv]
    rw [hloginv]
    linarith
  let m : ℝ := s + (T - s) / 2
  have hsm : s < m := by dsimp [m]; linarith
  have hmT : m < T := by dsimp [m]; linarith
  have hmidnonneg : 0 ≤ (T - s) / 2 := le_of_lt (by positivity)
  have hcum := hG ϑ hϑ ((T - s) / 2) (by positivity) (by
    have : T - s ≤ 1 := hhT
    linarith)
  have hcum' : (∫ r in Ioc 0 ((T - s) / 2),
      DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) r) ≤
      CG / (1 + Real.log (1 / (T - s))) := by
    calc
      _ ≤ CG / (1 + Real.log (1 / ((T - s) / 2))) := hcum.2.2
      _ ≤ _ := by
        have hden : 0 < 1 + Real.log (1 / ((T - s) / 2)) := by
          have harg : 1 ≤ 1 / ((T - s) / 2) := by
            rw [le_div_iff₀ (by positivity : 0 < (T - s) / 2)]
            linarith [hhT]
          have hrec := Real.log_nonneg harg
          linarith
        have harg : 1 / (T - s) ≤ 1 / ((T - s) / 2) := by
          rw [div_le_div_iff₀ hh (by positivity)]
          nlinarith [hh]
        have hdenle : 1 + Real.log (1 / (T - s)) ≤
            1 + Real.log (1 / ((T - s) / 2)) :=
          by simpa [add_comm] using add_le_add_left (Real.log_le_log (by positivity) harg) 1
        exact div_le_div_of_nonneg_left hCG.le hL hdenle
  have hbaseInt : IntervalIntegrable
      (fun r => DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) r)
      volume 0 ((T - s) / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
    exact Renewal.integrableOn_scalarDensity_Ioc _ _
  have hdensHead : IntervalIntegrable
      (fun t => DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (t - s))
      volume s m := by
    simpa [m, add_comm] using hbaseInt.comp_sub_right s
  have hcumShift : (∫ t in s..m,
      DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (t - s)) =
      ∫ r in Ioc 0 ((T - s) / 2),
        DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) r := by
    rw [intervalIntegral.integral_comp_sub_right]
    rw [← intervalIntegral.integral_of_le (by positivity : 0 ≤ (T - s) / 2)]
    simp [m]
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hheadWeight : ∀ t ∈ Ioo s m,
      backwardWeight T t ≤ backwardWeight T s + Real.log 2 := by
    intro t ht
    have hbound : T - t ≥ (T - s) / 2 := by
      dsimp [m] at ht
      nlinarith [ht.1, ht.2]
    have hlog : Real.log ((T - s) / 2) ≤ Real.log (T - t) :=
      Real.log_le_log (by positivity) hbound
    rw [show backwardWeight T t = Real.log (2 * T) - Real.log (T - t) by rfl,
      show backwardWeight T s = Real.log (2 * T) - Real.log (T - s) by rfl]
    have hratio : Real.log (T - s) - Real.log ((T - s) / 2) = Real.log 2 := by
      rw [← Real.log_div hh.ne' (by positivity : (T - s) / 2 ≠ 0)]
      congr 1
      field_simp
    linarith
  have hweightHeadCont : ContinuousOn (backwardWeight T) (uIcc s m) := by
    rw [uIcc_of_le hsm.le]
    change ContinuousOn (fun t => Real.log (2 * T) - Real.log (T - t)) (Icc s m)
    apply continuousOn_const.sub
    apply Real.continuousOn_log.comp (continuousOn_const.sub continuousOn_id)
    intro t ht
    exact (sub_pos.mpr (lt_of_le_of_lt ht.2 hmT)).ne'
  have hprodHead : IntervalIntegrable
      (fun t => DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (t - s) *
        backwardWeight T t) volume s m := by
    simpa only [mul_comm] using hdensHead.continuousOn_mul hweightHeadCont
  have hconstHead : IntervalIntegrable
      (fun t => (backwardWeight T s + Real.log 2) *
        DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (t - s)) volume s m :=
    hdensHead.const_mul _
  have hheadPoint : ∀ t ∈ Ioo s m,
      DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (t - s) *
        backwardWeight T t ≤
      (backwardWeight T s + Real.log 2) *
        DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (t - s) := by
    intro t ht
    have hpos := DeltaBose.scalarDensity_pos
      (ϑ - Real.eulerMascheroniConstant) (sub_pos.mpr ht.1)
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hheadWeight t ht) hpos.le
  have hhead := intervalIntegral.integral_mono_on_of_le_Ioo hsm.le
    hprodHead hconstHead hheadPoint
  have hheadBound : (∫ t in s..m,
      DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (t - s) *
        backwardWeight T t) ≤
      (backwardWeight T s + Real.log 2) * CG /
        (1 + Real.log (1 / (T - s))) := by
    calc
      _ ≤ (backwardWeight T s + Real.log 2) *
          (∫ t in s..m,
            DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (t - s)) := by
            calc
              _ ≤ ∫ t in s..m,
                (backwardWeight T s + Real.log 2) *
                  DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (t - s) := hhead
              _ = _ := by rw [intervalIntegral.integral_const_mul]
      _ ≤ _ := by
        rw [hcumShift]
        simpa only [div_eq_mul_inv, mul_assoc] using
          (mul_le_mul_of_nonneg_left hcum'
            (by positivity : 0 ≤ backwardWeight T s + Real.log 2))
  have hGtail_point : ∀ r ∈ Icc ((T - s) / 2) (T - s),
      DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) r ≤
        2 * CG / ((T - s) * (1 + Real.log (1 / (T - s))) ^ 2) := by
    intro r hr
    have hrpos : 0 < r := lt_of_lt_of_le (by positivity) hr.1
    have hrle : r ≤ 1 := hr.2.trans hhT
    have hrG := (hG ϑ hϑ r hrpos hrle).1
    have hlogmono : Real.log (1 / (T - s)) ≤ Real.log (1 / r) := by
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ hh hrpos]
      linarith [hr.2]
    have hden0 : 0 < 1 + Real.log (1 / (T - s)) := hL
    have hrecip : 1 / r ≤ 2 / (T - s) := by
      rw [div_le_div_iff₀ hrpos hh]
      linarith [hr.1]
    have hdenle : 1 + Real.log (1 / (T - s)) ≤ 1 + Real.log (1 / r) :=
      by simpa [add_comm] using add_le_add_left hlogmono 1
    have hdenpos : 0 < 1 + Real.log (1 / r) := lt_of_lt_of_le hden0 hdenle
    have hdenSq : (1 + Real.log (1 / (T - s))) ^ 2 ≤
        (1 + Real.log (1 / r)) ^ 2 := by nlinarith [hden0, hdenle]
    have hdenprod : (T - s) * (1 + Real.log (1 / (T - s))) ^ 2 ≤
        2 * r * (1 + Real.log (1 / r)) ^ 2 := by
      have hrInv : T - s ≤ 2 * r := by linarith [hr.1]
      calc
        (T - s) * (1 + Real.log (1 / (T - s))) ^ 2 ≤
            (2 * r) * (1 + Real.log (1 / (T - s))) ^ 2 :=
          mul_le_mul_of_nonneg_right hrInv (sq_nonneg _)
        _ ≤ 2 * r * (1 + Real.log (1 / r)) ^ 2 :=
          mul_le_mul_of_nonneg_left hdenSq (by positivity)
    calc
      DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) r ≤
          CG / (r * (1 + Real.log (1 / r)) ^ 2) := hrG
      _ ≤ 2 * CG / ((T - s) * (1 + Real.log (1 / (T - s))) ^ 2) := by
        have hdenprodpos : 0 < (T - s) * (1 + Real.log (1 / (T - s))) ^ 2 := by positivity
        rw [div_le_div_iff₀ (by positivity) hdenprodpos]
        nlinarith [hCG, hdenprod]
  have hdensTailCont : ContinuousOn
      (fun t => DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (t - s))
      (Icc m T) := by
    have hmap : ContinuousOn (fun t : ℝ => (ϑ - Real.eulerMascheroniConstant, t - s))
        (Icc m T) := continuousOn_const.prodMk (continuousOn_id.sub continuousOn_const)
    apply DeltaBose.continuousOn_scalarDensity.comp hmap
    intro t ht
    exact sub_pos.mpr (lt_of_lt_of_le hsm ht.1)
  have hdensTail : IntervalIntegrable
      (fun t => DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (t - s))
      volume m T := hdensTailCont.intervalIntegrable_of_Icc hmT.le
  have hweightTail : IntervalIntegrable (backwardWeight T) volume m T :=
    backwardWeight_intervalIntegrable
  have hdensTailCont' : ContinuousOn
      (fun t => DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (t - s))
      (uIcc m T) := by
    rw [uIcc_of_le hmT.le]
    exact hdensTailCont
  have hprodTail : IntervalIntegrable
      (fun t => DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (t - s) *
        backwardWeight T t) volume m T :=
    hweightTail.continuousOn_mul hdensTailCont'
  let K : ℝ := 2 * CG / ((T - s) * (1 + Real.log (1 / (T - s))) ^ 2)
  have hKnonneg : 0 ≤ K := by dsimp [K]; positivity
  have hconstTail : IntervalIntegrable (fun t => K * backwardWeight T t) volume m T :=
    hweightTail.const_mul K
  have htailPoint : ∀ t ∈ Ioo m T,
      DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (t - s) *
        backwardWeight T t ≤ K * backwardWeight T t := by
    intro t ht
    have ht0 : 0 < t - s := by linarith [ht.1]
    have htrange : t - s ∈ Icc ((T - s) / 2) (T - s) := by
      constructor
      · dsimp [m] at ht
        nlinarith [ht.1]
      · linarith [ht.2]
    have hWt : 0 ≤ backwardWeight T t := backwardWeight_nonneg hTpos (by linarith [hs]) ht.2
    exact mul_le_mul_of_nonneg_right (hGtail_point (t - s) htrange) hWt
  have htail := intervalIntegral.integral_mono_on_of_le_Ioo hmT.le
    hprodTail hconstTail htailPoint
  have htailWeightIntegral : ∫ t in m..T, backwardWeight T t =
      (T - s) / 2 * (backwardWeight T s + Real.log 2 + 1) := by
    have hEq : m = T - (T - s) / 2 := by dsimp [m]; ring
    rw [hEq, integral_backwardWeight_terminalSegment hTpos hh]
    have hlog : Real.log (4 * T / (T - s)) =
        backwardWeight T s + Real.log 2 := by
      have hfactor : 4 * T / (T - s) = 2 * (2 * T / (T - s)) := by field_simp; ring
      rw [hfactor, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (div_ne_zero (by positivity : (2 * T : ℝ) ≠ 0) hh.ne'),
        backwardWeight_eq_log_ratio hTpos hst]
      ring
    rw [hlog]
  have htailBound : (∫ t in m..T,
      DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (t - s) *
        backwardWeight T t) ≤
      CG * (backwardWeight T s + Real.log 2 + 1) /
        (1 + Real.log (1 / (T - s))) ^ 2 := by
    calc
      _ ≤ K * ∫ t in m..T, backwardWeight T t := by
        calc
          _ ≤ ∫ t in m..T, K * backwardWeight T t := htail
          _ = _ := by rw [intervalIntegral.integral_const_mul]
      _ = _ := by rw [htailWeightIntegral]; dsimp [K]; field_simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hprodHead hprodTail
  have htotal : (∫ t in s..T,
      DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (t - s) *
        backwardWeight T t) ≤
      CG * (backwardWeight T s + Real.log 2) /
        (1 + Real.log (1 / (T - s))) +
      CG * (backwardWeight T s + Real.log 2 + 1) /
        (1 + Real.log (1 / (T - s))) ^ 2 := by
    rw [← hsplit]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      add_le_add hheadBound htailBound
  have hWlog : Real.log 2 ≤ backwardWeight T s := backwardWeight_ge_log_two hs (by linarith)
  have hWlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hboundfinal :
      CG * (backwardWeight T s + Real.log 2) /
          (1 + Real.log (1 / (T - s))) +
        CG * (backwardWeight T s + Real.log 2 + 1) /
          (1 + Real.log (1 / (T - s))) ^ 2 ≤
        C * backwardWeight T s / (-Real.log T) := by
    dsimp [C]
    have hden : 1 ≤ 1 + Real.log (1 / (T - s)) := by
      have harg : 1 ≤ 1 / (T - s) := by
        rw [le_div_iff₀ hh]
        linarith [hhT]
      have := Real.log_nonneg harg
      linarith
    have hdenM : -Real.log T ≤ 1 + Real.log (1 / (T - s)) := hLgeM
    have hdenSqM : -Real.log T ≤ (1 + Real.log (1 / (T - s))) ^ 2 := by
      nlinarith [hL, hdenM, hM]
    have hlog2inv : 1 / Real.log 2 > 0 := by positivity
    have h1 : backwardWeight T s + Real.log 2 ≤ 2 * backwardWeight T s := by linarith
    have h2 : backwardWeight T s + Real.log 2 + 1 ≤
        (2 + 1 / Real.log 2) * backwardWeight T s := by
      have hscale : 1 ≤ (1 / Real.log 2) * backwardWeight T s := by
        calc
          1 = (1 / Real.log 2) * Real.log 2 := by field_simp
          _ ≤ (1 / Real.log 2) * backwardWeight T s :=
            mul_le_mul_of_nonneg_left hWlog (by positivity)
      calc
        backwardWeight T s + Real.log 2 + 1 ≤
            2 * backwardWeight T s + 1 := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right h1 1
        _ ≤ 2 * backwardWeight T s + (1 / Real.log 2) * backwardWeight T s :=
          by simpa [add_comm] using add_le_add_left hscale (2 * backwardWeight T s)
        _ = (2 + 1 / Real.log 2) * backwardWeight T s := by ring
    have hterms :
        CG * (backwardWeight T s + Real.log 2) /
            (1 + Real.log (1 / (T - s))) ≤
          2 * CG * backwardWeight T s / (-Real.log T) := by
      calc
        _ ≤ CG * (backwardWeight T s + Real.log 2) / (-Real.log T) :=
          div_le_div_of_nonneg_left (by positivity) hM hdenM
        _ ≤ 2 * CG * backwardWeight T s / (-Real.log T) := by
          apply div_le_div_of_nonneg_right _ hM.le
          calc
            CG * (backwardWeight T s + Real.log 2) ≤
                CG * (2 * backwardWeight T s) :=
              mul_le_mul_of_nonneg_left h1 hCG.le
            _ = 2 * CG * backwardWeight T s := by ring
    have hterms' :
        CG * (backwardWeight T s + Real.log 2 + 1) /
            (1 + Real.log (1 / (T - s))) ^ 2 ≤
          CG * (2 + 1 / Real.log 2) * backwardWeight T s / (-Real.log T) := by
      calc
        _ ≤ CG * (backwardWeight T s + Real.log 2 + 1) / (-Real.log T) :=
          div_le_div_of_nonneg_left (by positivity) hM hdenSqM
        _ ≤ CG * (2 + 1 / Real.log 2) * backwardWeight T s / (-Real.log T) := by
          apply div_le_div_of_nonneg_right _ hM.le
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            mul_le_mul_of_nonneg_left h2 hCG.le
    have hsum := add_le_add hterms hterms'
    calc
      _ ≤ 2 * CG * backwardWeight T s / (-Real.log T) +
          CG * (2 + 1 / Real.log 2) * backwardWeight T s / (-Real.log T) := hsum
      _ = CG * (4 + 1 / Real.log 2) * backwardWeight T s / (-Real.log T) := by ring
  have hinterval := htotal.trans hboundfinal
  rw [intervalIntegral.integral_of_le hst.le] at hinterval
  have hsplit : Ioc s T = Ioc s m ∪ Ioc m T := by
    ext t
    simp only [mem_Ioc, mem_union]
    constructor
    · intro ht
      by_cases htm : t ≤ m
      · exact Or.inl ⟨ht.1, htm⟩
      · exact Or.inr ⟨lt_of_not_ge htm, ht.2⟩
    · rintro (⟨hst', htm⟩ | ⟨hmt, htT⟩)
      · exact ⟨hst', le_trans htm hmT.le⟩
      · exact ⟨lt_trans hsm hmt, htT⟩
  have hInt : IntegrableOn
      (fun t => DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (t - s) *
        backwardWeight T t) (Ioc s T) := by
    rw [hsplit, integrableOn_union]
    exact ⟨
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hsm.le).1 hprodHead,
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hmT.le).1 hprodTail⟩
  exact ⟨hInt, hinterval⟩

/-- The scalar backward-renewal bound expressed as a nonnegative integral. -/
theorem lintegral_backwardRenewal_inner_bound (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ϑ ∈ Set.Icc (-A) A, ∀ s T : ℝ,
      0 ≤ s → s < T → T < 1 →
        ∫⁻ t in Ioc s T,
          ENNReal.ofReal (DeltaBose.scalarDensity
            (ϑ - Real.eulerMascheroniConstant) (t - s) * backwardWeight T t) ≤
          ENNReal.ofReal (C * backwardWeight T s / (-Real.log T)) := by
  obtain ⟨C, hC, hbound⟩ := exists_backwardRenewal_inner_bound A
  refine ⟨C, hC, fun ϑ hϑ s T hs hst hT => ?_⟩
  obtain ⟨hInt, hreal⟩ := hbound ϑ hϑ s T hs hst hT
  have hTpos : 0 < T := lt_of_le_of_lt hs hst
  have hIntoo : IntegrableOn
      (fun t => DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (t - s) *
        backwardWeight T t) (Ioo s T) :=
    hInt.mono_set Ioo_subset_Ioc_self
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo s T)]
      (fun t => DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (t - s) *
        backwardWeight T t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact mul_nonneg
      (DeltaBose.scalarDensity_pos (ϑ - Real.eulerMascheroniConstant)
        (sub_pos.mpr ht.1)).le
      (backwardWeight_nonneg hTpos (le_trans hs ht.1.le) ht.2)
  have hlin :
      (∫⁻ t in Ioc s T, ENNReal.ofReal
        (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (t - s) *
          backwardWeight T t)) =
        ENNReal.ofReal (∫ t in Ioc s T,
          DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (t - s) *
            backwardWeight T t) := by
    rw [← restrict_Ioo_eq_restrict_Ioc]
    rw [← ofReal_integral_eq_lintegral_ofReal hIntoo hnonneg]
  rw [hlin]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The outer backward-block estimate expressed as a nonnegative integral. -/
theorem lintegral_backwardBlock_outer_le {τ S T : ℝ} (hτ : 0 ≤ τ)
    (hτS : τ < S) (hS : 0 < S) (hblock : 4 * S ≤ T) :
    ∫⁻ x in Ioo S T, ENNReal.ofReal
        ((τ / (x * (x - τ))) * backwardWeight T x) ≤
      ENNReal.ofReal
        ((24 / Real.log 2 + 8) * (τ / S) * backwardWeight S τ) := by
  have hTpos : 0 < T := by linarith
  have hST : S ≤ T := by linarith
  have hRcont : ContinuousOn (fun x : ℝ => τ / (x * (x - τ))) (uIcc S T) := by
    rw [uIcc_of_le hST]
    apply continuousOn_const.div (continuousOn_id.mul
      (continuousOn_id.sub continuousOn_const))
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hS hx.1
    have hxdpos : 0 < x - τ := sub_pos.mpr (lt_of_lt_of_le hτS hx.1)
    exact mul_ne_zero hxpos.ne' hxdpos.ne'
  have hprod : IntervalIntegrable
      (fun x : ℝ => (τ / (x * (x - τ))) * backwardWeight T x) volume S T := by
    have h := backwardWeight_intervalIntegrable.continuousOn_mul hRcont
    simpa only [mul_comm] using h
  have hIntIoc : IntegrableOn
      (fun x : ℝ => (τ / (x * (x - τ))) * backwardWeight T x) (Ioc S T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hST).1 hprod
  have hIntIoo : IntegrableOn
      (fun x : ℝ => (τ / (x * (x - τ))) * backwardWeight T x) (Ioo S T) :=
    hIntIoc.mono_set Ioo_subset_Ioc_self
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo S T)]
      (fun x : ℝ => (τ / (x * (x - τ))) * backwardWeight T x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hxpos : 0 < x := lt_trans hS hx.1
    have hxdpos : 0 < x - τ := sub_pos.mpr (lt_trans hτS hx.1)
    exact mul_nonneg
      (div_nonneg hτ (mul_nonneg hxpos.le hxdpos.le))
      (backwardWeight_nonneg hTpos (le_trans hS.le hx.1.le) hx.2)
  have hlin :
      (∫⁻ x in Ioo S T, ENNReal.ofReal
        ((τ / (x * (x - τ))) * backwardWeight T x)) =
        ENNReal.ofReal (∫ x in S..T,
          (τ / (x * (x - τ))) * backwardWeight T x) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hIntIoo hnonneg]
    rw [← integral_Ioc_eq_integral_Ioo]
    rw [← intervalIntegral.integral_of_le hST]
  rw [hlin]
  apply ENNReal.ofReal_le_ofReal
  exact integral_backwardBlock_outer hτ hτS hS hblock

/-- The backward-weight integral bound of Lemma A.4, equation (A.22), uniformly for `ϑ ∈ [−A, A]`. -/
theorem lintegral_backwardBlock_le (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ϑ ∈ Set.Icc (-A) A, ∀ τ S T : ℝ,
      0 < τ → τ < S → 4 * S ≤ T → T < 1 →
      ∫⁻ p : ℝ × ℝ in {p | S < p.1 ∧ p.1 < p.2 ∧ p.2 < T},
          ENNReal.ofReal (DeltaBose.scalarDensity
            (ϑ - Real.eulerMascheroniConstant) (p.2 - p.1) *
            (τ / (p.1 * (p.1 - τ))) * backwardWeight T p.2) ≤
        ENNReal.ofReal (C / (-Real.log T) * (τ / S) * backwardWeight S τ) := by
  obtain ⟨Cinner, hCinner, hinner⟩ := lintegral_backwardRenewal_inner_bound A
  let Couter : ℝ := 24 / Real.log 2 + 8
  let C : ℝ := Cinner * Couter
  have hCouter : 0 < Couter := by
    dsimp [Couter]
    positivity
  have hC : 0 < C := mul_pos hCinner hCouter
  refine ⟨C, hC, fun ϑ hϑ τ S T hτ hτS hblock hT => ?_⟩
  have hS : 0 < S := lt_trans hτ hτS
  have hTpos : 0 < T := by linarith
  have hscalar : Measurable (fun t : ℝ => DeltaBose.scalarDensity
      (ϑ - Real.eulerMascheroniConstant) t) := by
    exact DeltaBose.measurable_scalarDensity.comp
      (measurable_const.prodMk measurable_id)
  have hback : Measurable (backwardWeight T) := by
    change Measurable (fun t : ℝ => Real.log (2 * T) - Real.log (T - t))
    fun_prop
  have hratio : Measurable (fun p : ℝ × ℝ => τ / (p.1 * (p.1 - τ))) := by
    fun_prop
  have hreal : Measurable (fun p : ℝ × ℝ =>
      DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (p.2 - p.1) *
        (τ / (p.1 * (p.1 - τ))) * backwardWeight T p.2) := by
    exact (hscalar.comp (measurable_snd.sub measurable_fst)).mul hratio |>.mul
      (hback.comp measurable_snd)
  have hmeas : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal
      (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (p.2 - p.1) *
        (τ / (p.1 * (p.1 - τ))) * backwardWeight T p.2)) := by
    exact hreal.ennreal_ofReal
  rw [lintegral_openTriangle_eq hmeas]
  have houter := lintegral_backwardBlock_outer_le hτ.le hτS hS hblock
  have houterScaled :
      ENNReal.ofReal (Cinner / (-Real.log T)) *
        (∫⁻ x in Ioo S T, ENNReal.ofReal
          ((τ / (x * (x - τ))) * backwardWeight T x)) ≤
      ENNReal.ofReal (Cinner / (-Real.log T)) *
        ENNReal.ofReal (Couter * (τ / S) * backwardWeight S τ) :=
    by gcongr
  have hlogT : 0 < -Real.log T := by
    have hlog := Real.log_lt_log hTpos hT
    rw [Real.log_one] at hlog
    linarith
  have hconst : 0 ≤ Cinner / (-Real.log T) := div_nonneg hCinner.le hlogT.le
  have hpoint : ∀ x ∈ Ioo S T,
      (∫⁻ y in Ioo x T, ENNReal.ofReal
        (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (y - x) *
          (τ / (x * (x - τ))) * backwardWeight T y)) ≤
        ENNReal.ofReal (Cinner / (-Real.log T)) *
          ENNReal.ofReal ((τ / (x * (x - τ))) * backwardWeight T x) := by
    intro x hx
    have hx0 : 0 ≤ x := le_of_lt (lt_trans hS hx.1)
    have hxt : x < T := hx.2
    have hR : 0 ≤ τ / (x * (x - τ)) := by
      apply div_nonneg hτ.le
      exact mul_nonneg (le_of_lt (lt_trans hS hx.1))
        (le_of_lt (sub_pos.mpr (lt_trans hτS hx.1)))
    have hinnerX := hinner ϑ hϑ x T hx0 hxt hT
    rw [← restrict_Ioo_eq_restrict_Ioc] at hinnerX
    have hslice : Measurable (fun y : ℝ => ENNReal.ofReal
        (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (y - x) *
          backwardWeight T y)) := by
      exact ((hscalar.comp (measurable_id.sub measurable_const)).mul hback).ennreal_ofReal
    have hfactor (y : ℝ) :
        ENNReal.ofReal (DeltaBose.scalarDensity
          (ϑ - Real.eulerMascheroniConstant) (y - x) *
            (τ / (x * (x - τ))) * backwardWeight T y) =
        ENNReal.ofReal (τ / (x * (x - τ))) * ENNReal.ofReal
          (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (y - x) *
            backwardWeight T y) := by
      rw [show DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (y - x) *
          (τ / (x * (x - τ))) * backwardWeight T y =
            (τ / (x * (x - τ))) *
              (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (y - x) *
                backwardWeight T y) by ring]
      rw [ENNReal.ofReal_mul hR]
    calc
      _ = ENNReal.ofReal (τ / (x * (x - τ))) *
          (∫⁻ y in Ioo x T, ENNReal.ofReal
            (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (y - x) *
              backwardWeight T y)) := by
            rw [show (fun y : ℝ => ENNReal.ofReal
                (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (y - x) *
                  (τ / (x * (x - τ))) * backwardWeight T y)) =
                fun y => ENNReal.ofReal (τ / (x * (x - τ))) *
                  ENNReal.ofReal (DeltaBose.scalarDensity
                    (ϑ - Real.eulerMascheroniConstant) (y - x) * backwardWeight T y) by
              funext y
              exact hfactor y]
            rw [lintegral_const_mul _ hslice]
      _ ≤ ENNReal.ofReal (τ / (x * (x - τ))) *
          ENNReal.ofReal (Cinner * backwardWeight T x / (-Real.log T)) :=
            by gcongr
      _ = ENNReal.ofReal (Cinner / (-Real.log T)) *
          ENNReal.ofReal ((τ / (x * (x - τ))) * backwardWeight T x) := by
            rw [← ENNReal.ofReal_mul hconst, ← ENNReal.ofReal_mul hR]
            congr 1
            ring
  have hdouble :
      (∫⁻ x in Ioo S T, ∫⁻ y in Ioo x T,
        ENNReal.ofReal (DeltaBose.scalarDensity
          (ϑ - Real.eulerMascheroniConstant) (y - x) *
            (τ / (x * (x - τ))) * backwardWeight T y)) ≤
        ENNReal.ofReal (Cinner / (-Real.log T)) *
          (∫⁻ x in Ioo S T, ENNReal.ofReal
            ((τ / (x * (x - τ))) * backwardWeight T x)) := by
    calc
      _ ≤ ∫⁻ x in Ioo S T,
          ENNReal.ofReal (Cinner / (-Real.log T)) *
            ENNReal.ofReal ((τ / (x * (x - τ))) * backwardWeight T x) := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
              exact hpoint x hx
      _ = _ := by
        have houtMeas : Measurable (fun x : ℝ => ENNReal.ofReal
            ((τ / (x * (x - τ))) * backwardWeight T x)) := by
          have hratx : Measurable (fun x : ℝ => τ / (x * (x - τ))) := by fun_prop
          exact (hratx.mul hback).ennreal_ofReal
        rw [lintegral_const_mul _ houtMeas]
  calc
    _ ≤ ENNReal.ofReal (Cinner / (-Real.log T)) *
        (∫⁻ x in Ioo S T, ENNReal.ofReal
          ((τ / (x * (x - τ))) * backwardWeight T x)) := hdouble
    _ ≤ ENNReal.ofReal (Cinner / (-Real.log T)) *
        ENNReal.ofReal (Couter * (τ / S) * backwardWeight S τ) := houterScaled
    _ = ENNReal.ofReal (C / (-Real.log T) * (τ / S) * backwardWeight S τ) := by
      rw [← ENNReal.ofReal_mul hconst]
      congr 1
      dsimp [C, Couter]
      ring

/-- The initial backward-weight estimate expressed as a nonnegative integral. -/
theorem lintegral_backwardInitial_outer_le {S T : ℝ} (hS : 0 < S)
    (hST : 2 * S ≤ T) :
    ∫⁻ x in Ioo S T, ENNReal.ofReal (x⁻¹ * backwardWeight T x) ≤
      ENNReal.ofReal ((4 + 4 / Real.log 2) * Real.log (T / S)) := by
  have hT : 0 < T := by linarith
  have hST' : S ≤ T := by linarith
  have hinvCont : ContinuousOn (fun x : ℝ => x⁻¹) (uIcc S T) := by
    rw [uIcc_of_le hST']
    have hcont : ContinuousOn (fun x : ℝ => (1 : ℝ) / x) (Icc S T) := by
      apply continuousOn_const.div continuousOn_id
      intro x hx
      exact (lt_of_lt_of_le hS hx.1).ne'
    simpa only [one_div] using hcont
  have hprod : IntervalIntegrable
      (fun x : ℝ => x⁻¹ * backwardWeight T x) volume S T := by
    have h := backwardWeight_intervalIntegrable.continuousOn_mul hinvCont
    simpa only [one_div, mul_comm] using h
  have hIntIoc : IntegrableOn (fun x : ℝ => x⁻¹ * backwardWeight T x) (Ioc S T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hST').1 hprod
  have hIntIoo : IntegrableOn (fun x : ℝ => x⁻¹ * backwardWeight T x) (Ioo S T) :=
    hIntIoc.mono_set Ioo_subset_Ioc_self
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo S T)]
      (fun x : ℝ => x⁻¹ * backwardWeight T x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt (lt_trans hS hx.1)))
      (backwardWeight_nonneg hT (le_trans hS.le hx.1.le) hx.2)
  have hlin :
      (∫⁻ x in Ioo S T, ENNReal.ofReal (x⁻¹ * backwardWeight T x)) =
        ENNReal.ofReal (∫ x in S..T, x⁻¹ * backwardWeight T x) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hIntIoo hnonneg]
    rw [← integral_Ioc_eq_integral_Ioo]
    rw [← intervalIntegral.integral_of_le hST']
  rw [hlin]
  apply ENNReal.ofReal_le_ofReal
  simpa only [one_div] using integral_backwardWeight_initial hS hST

/-- The initial backward integral satisfies the logarithmic bound in equation (A.17). -/
theorem lintegral_backwardInitial_le (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ϑ ∈ Set.Icc (-A) A, ∀ S T : ℝ,
      0 < S → 2 * S ≤ T → T < 1 →
      ∫⁻ p : ℝ × ℝ in {p | S < p.1 ∧ p.1 < p.2 ∧ p.2 < T},
          ENNReal.ofReal (p.1⁻¹ *
            DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (p.2 - p.1) *
              backwardWeight T p.2) ≤
        ENNReal.ofReal (C / (-Real.log T) * Real.log (T / S)) := by
  obtain ⟨Cinner, hCinner, hinner⟩ := lintegral_backwardRenewal_inner_bound A
  let Couter : ℝ := 4 + 4 / Real.log 2
  let C : ℝ := Cinner * Couter
  have hCouter : 0 < Couter := by
    dsimp [Couter]
    positivity
  have hC : 0 < C := mul_pos hCinner hCouter
  refine ⟨C, hC, fun ϑ hϑ S T hS hST hT => ?_⟩
  have hTpos : 0 < T := by linarith
  have hscalar : Measurable (fun t : ℝ => DeltaBose.scalarDensity
      (ϑ - Real.eulerMascheroniConstant) t) := by
    exact DeltaBose.measurable_scalarDensity.comp
      (measurable_const.prodMk measurable_id)
  have hback : Measurable (backwardWeight T) := by
    change Measurable (fun t : ℝ => Real.log (2 * T) - Real.log (T - t))
    fun_prop
  have hinv : Measurable (fun x : ℝ × ℝ => x.1⁻¹) := by fun_prop
  have hreal : Measurable (fun p : ℝ × ℝ =>
      p.1⁻¹ * DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (p.2 - p.1) *
        backwardWeight T p.2) := by
    exact hinv.mul (hscalar.comp (measurable_snd.sub measurable_fst)) |>.mul
      (hback.comp measurable_snd)
  have hmeas : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal
      (p.1⁻¹ * DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (p.2 - p.1) *
        backwardWeight T p.2)) := hreal.ennreal_ofReal
  rw [lintegral_openTriangle_eq hmeas]
  have houter := lintegral_backwardInitial_outer_le hS hST
  have hlogT : 0 < -Real.log T := by
    have hlog := Real.log_lt_log hTpos hT
    rw [Real.log_one] at hlog
    linarith
  have hconst : 0 ≤ Cinner / (-Real.log T) := div_nonneg hCinner.le hlogT.le
  have houterScaled :
      ENNReal.ofReal (Cinner / (-Real.log T)) *
        (∫⁻ x in Ioo S T, ENNReal.ofReal (x⁻¹ * backwardWeight T x)) ≤
      ENNReal.ofReal (Cinner / (-Real.log T)) *
        ENNReal.ofReal (Couter * Real.log (T / S)) := by
    gcongr
  have hpoint : ∀ x ∈ Ioo S T,
      (∫⁻ y in Ioo x T, ENNReal.ofReal
        (x⁻¹ * DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (y - x) *
          backwardWeight T y)) ≤
        ENNReal.ofReal (Cinner / (-Real.log T)) *
          ENNReal.ofReal (x⁻¹ * backwardWeight T x) := by
    intro x hx
    have hx0 : 0 ≤ x := le_of_lt (lt_trans hS hx.1)
    have hxt : x < T := hx.2
    have hR : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0
    have hinnerX := hinner ϑ hϑ x T hx0 hxt hT
    rw [← restrict_Ioo_eq_restrict_Ioc] at hinnerX
    have hslice : Measurable (fun y : ℝ => ENNReal.ofReal
        (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (y - x) *
          backwardWeight T y)) := by
      exact ((hscalar.comp (measurable_id.sub measurable_const)).mul hback).ennreal_ofReal
    have hfactor (y : ℝ) :
        ENNReal.ofReal (x⁻¹ * DeltaBose.scalarDensity
          (ϑ - Real.eulerMascheroniConstant) (y - x) * backwardWeight T y) =
        ENNReal.ofReal (x⁻¹) * ENNReal.ofReal
          (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (y - x) *
            backwardWeight T y) := by
      rw [show x⁻¹ * DeltaBose.scalarDensity
          (ϑ - Real.eulerMascheroniConstant) (y - x) * backwardWeight T y =
          x⁻¹ * (DeltaBose.scalarDensity
            (ϑ - Real.eulerMascheroniConstant) (y - x) * backwardWeight T y) by ring]
      rw [ENNReal.ofReal_mul hR]
    calc
      _ = ENNReal.ofReal (x⁻¹) *
          (∫⁻ y in Ioo x T, ENNReal.ofReal
            (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (y - x) *
              backwardWeight T y)) := by
            rw [show (fun y : ℝ => ENNReal.ofReal
                (x⁻¹ * DeltaBose.scalarDensity
                  (ϑ - Real.eulerMascheroniConstant) (y - x) * backwardWeight T y)) =
                fun y => ENNReal.ofReal x⁻¹ * ENNReal.ofReal
                  (DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (y - x) *
                    backwardWeight T y) by
              funext y
              exact hfactor y]
            rw [lintegral_const_mul _ hslice]
      _ ≤ ENNReal.ofReal x⁻¹ *
          ENNReal.ofReal (Cinner * backwardWeight T x / (-Real.log T)) := by
            gcongr
      _ = ENNReal.ofReal (Cinner / (-Real.log T)) *
          ENNReal.ofReal (x⁻¹ * backwardWeight T x) := by
            rw [← ENNReal.ofReal_mul hconst, ← ENNReal.ofReal_mul hR]
            congr 1
            ring
  have hdouble :
      (∫⁻ x in Ioo S T, ∫⁻ y in Ioo x T,
        ENNReal.ofReal (x⁻¹ *
          DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (y - x) *
            backwardWeight T y)) ≤
        ENNReal.ofReal (Cinner / (-Real.log T)) *
          (∫⁻ x in Ioo S T, ENNReal.ofReal (x⁻¹ * backwardWeight T x)) := by
    calc
      _ ≤ ∫⁻ x in Ioo S T,
          ENNReal.ofReal (Cinner / (-Real.log T)) *
            ENNReal.ofReal (x⁻¹ * backwardWeight T x) := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
              exact hpoint x hx
      _ = _ := by
        have houtMeas : Measurable (fun x : ℝ => ENNReal.ofReal
            (x⁻¹ * backwardWeight T x)) := by
          exact ((by fun_prop : Measurable (fun x : ℝ => x⁻¹)).mul hback).ennreal_ofReal
        rw [lintegral_const_mul _ houtMeas]
  calc
    _ ≤ ENNReal.ofReal (Cinner / (-Real.log T)) *
        (∫⁻ x in Ioo S T, ENNReal.ofReal (x⁻¹ * backwardWeight T x)) := hdouble
    _ ≤ ENNReal.ofReal (Cinner / (-Real.log T)) *
        ENNReal.ofReal (Couter * Real.log (T / S)) := houterScaled
    _ = ENNReal.ofReal (C / (-Real.log T) * Real.log (T / S)) := by
      rw [← ENNReal.ofReal_mul hconst]
      congr 1
      dsimp [C, Couter]
      ring

end Critical2DKPZ.Collision
