/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SmallScales.DeterministicComparison
public import Critical2DKPZ.Smoothing.EnergyDilatePerturb
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! # Logarithmic heat-energy control for shrinking test functions -/

@[expose] public section

open MeasureTheory
open Critical2DKPZ.Smoothing
open scoped BoundedContinuousFunction Interval

namespace Critical2DKPZ.SmallScales

private theorem continuumHeatProfile_le_mass_sq_div (ψ : Plane → ℝ)
    (hψ : Measurable ψ) (hψint : Integrable ψ) (B : ℝ)
    (hB : ∀ x, |ψ x| ≤ B) {r : ℝ} (hr : 0 < r) :
    continuumHeatProfile ψ r ≤ (∫ x, |ψ x|) ^ 2 / (4 * Real.pi * r) := by
  have hprofile := Smoothing.continuumHeatProfile_integrable_bound ψ hψ hψint B hB hr
  let F : Plane × Plane → ℝ := fun p => |ψ p.1| * |ψ p.2|
  have hnorm : Integrable (fun x : Plane => |ψ x|) := by
    simpa only [Real.norm_eq_abs] using hψint.norm
  have hFint : Integrable F (volume.prod volume) := by
    simpa only [F] using hnorm.mul_prod hnorm
  let K : ℝ := (4 * Real.pi * r)⁻¹
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hmajor : Integrable (fun p : Plane × Plane => F p * K) (volume.prod volume) :=
    hFint.mul_const K
  have hpoint (p : Plane × Plane) :
      F p * heatKernel (2 * r) (p.2 - p.1) ≤ F p * K := by
    dsimp [F, K]
    have hk := heatKernel_le_at_zero (by positivity : 0 ≤ 2 * r) (p.2 - p.1)
    have hker : (2 * Real.pi * (2 * r))⁻¹ = (4 * Real.pi * r)⁻¹ := by
      congr 1
      ring
    rw [hker] at hk
    exact mul_le_mul_of_nonneg_left hk (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hle := integral_mono hprofile.1 hmajor hpoint
  have hFmass : (∫ p : Plane × Plane, F p ∂(volume.prod volume)) =
      (∫ x : Plane, |ψ x|) ^ 2 := by
    simpa only [F, pow_two] using
      (integral_prod_mul (fun x : Plane => |ψ x|) (fun x : Plane => |ψ x|))
  calc
    continuumHeatProfile ψ r = ∫ p : Plane × Plane,
        F p * heatKernel (2 * r) (p.2 - p.1) ∂(volume.prod volume) := by rfl
    _ ≤ ∫ p : Plane × Plane, F p * K ∂(volume.prod volume) := hle
    _ = (∫ p : Plane × Plane, F p ∂(volume.prod volume)) * K := integral_mul_const _ _
    _ = (∫ x : Plane, |ψ x|) ^ 2 / (4 * Real.pi * r) := by
      rw [hFmass]
      dsimp [K]
      ring

/-- The absolute mass of a translated and rescaled test function is unchanged. -/
theorem integral_abs_testFn_dilate_eq (φ : TestFn) {ε : ℝ} (hε : 0 < ε) (x : Plane) :
    (∫ y, |φ.dilate ε x y|) = ∫ y, |φ y| := by
  have hshift : (∫ y : Plane, |φ (ε⁻¹ • (y - x))|) =
      ∫ y : Plane, |φ (ε⁻¹ • y)| := by
    have h := integral_add_left_eq_self (μ := (volume : Measure Plane))
      (fun y : Plane => |φ (ε⁻¹ • y)|) (-x)
    convert h using 1
    congr 1
    ext y
    simp [sub_eq_add_neg, add_comm]
  have hscale := Smoothing.integral_plane_sqrt_scale (a := ε ^ 2)
    (sq_pos_of_pos hε) (fun y : Plane => |φ (ε⁻¹ • y)|)
  have hsqrt : Real.sqrt (ε ^ 2) = ε := Real.sqrt_sq_eq_abs ε ▸ abs_of_pos hε
  have hscale' : (∫ y : Plane, |φ (ε⁻¹ • y)|) =
      ε ^ 2 * (∫ y : Plane, |φ y|) := by
    calc
      (∫ y : Plane, |φ (ε⁻¹ • y)|) =
          ε ^ 2 * (∫ y : Plane, |φ (ε⁻¹ • Real.sqrt (ε ^ 2) • y)|) := hscale
      _ = ε ^ 2 * (∫ y : Plane, |φ y|) := by
        rw [hsqrt]
        congr 1
        apply integral_congr_ae
        filter_upwards [] with y
        rw [smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
  have hfun : (fun y : Plane => |φ.dilate ε x y|) =
      fun y => ε⁻¹ ^ 2 * |φ (ε⁻¹ • (y - x))| := by
    funext y
    change |ε⁻¹ ^ 2 * φ (ε⁻¹ • (y - x))| = _
    rw [abs_mul, abs_of_pos (sq_pos_of_pos (inv_pos.mpr hε))]
  calc
    (∫ y, |φ.dilate ε x y|) = ε⁻¹ ^ 2 *
        (∫ y : Plane, |φ (ε⁻¹ • (y - x))|) := by
      rw [show (∫ y, |φ.dilate ε x y|) =
        ∫ y, ε⁻¹ ^ 2 * |φ (ε⁻¹ • (y - x))| by
          apply integral_congr_ae
          filter_upwards [] with y
          exact congrFun hfun y]
      exact integral_const_mul _ _
    _ = ε⁻¹ ^ 2 * (∫ y : Plane, |φ (ε⁻¹ • y)|) := by rw [hshift]
    _ = ε⁻¹ ^ 2 * (ε ^ 2 * ∫ y : Plane, |φ y|) := by rw [hscale']
    _ = ∫ y, |φ y| := by field_simp [hε.ne']

/-- The heat-energy time integrand of a shrinking test function is integrable, and its integral has at most logarithmic growth in the inverse scale. -/
theorem heatEnergy_testFn_dilate_le_log (φ : TestFn) (B : ℝ)
    (hB : ∀ x, |φ x| ≤ B) (x : Plane) {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) :
    IntegrableOn (fun u : ℝ => Smoothing.continuumHeatProfile (fun y => φ.dilate ε x y) u)
        (Set.Icc 0 s) ∧
      Smoothing.heatEnergy s (fun y => φ.dilate ε x y) ≤
        4 * B * (∫ y, |φ y|) +
          (∫ y, |φ y|) ^ 2 / Real.pi * max 0 (Real.log (s / ε ^ 2)) := by
  let ψ : Plane → ℝ := fun y => φ.dilate ε x y
  have hψ : Continuous ψ := (φ.dilate ε x).continuous
  have hψmeas : Measurable ψ := hψ.measurable
  have hψint : Integrable ψ := hψ.integrable_of_hasCompactSupport
    (φ.dilate ε x).hasCompactSupport
  have hψB : ∀ y, |ψ y| ≤ ε⁻¹ ^ 2 * B := by
    intro y
    change |ε⁻¹ ^ 2 * φ (ε⁻¹ • (y - x))| ≤ _
    rw [abs_mul, abs_of_pos (sq_pos_of_pos (inv_pos.mpr hε))]
    exact mul_le_mul_of_nonneg_left (hB _) (sq_nonneg ε⁻¹)
  have hmass : (∫ y, |ψ y|) = ∫ y, |φ y| := by
    exact integral_abs_testFn_dilate_eq φ hε x
  have henergy := Smoothing.heatEnergy_eq_profile_timeIntegral ψ hψmeas hψint
    (ε⁻¹ ^ 2 * B) hψB hs
  have hprofInterval : IntervalIntegrable (Smoothing.continuumHeatProfile ψ) volume 0 s := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hs.le]
    exact henergy.1
  have hBnonneg : 0 ≤ B := by
    have h := hB (0 : Plane)
    exact (abs_nonneg _).trans h
  have hmassNonneg : 0 ≤ ∫ y : Plane, |φ y| := integral_nonneg fun y => abs_nonneg _
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  by_cases hsmall : s ≤ ε ^ 2
  · have hcoarse := Smoothing.heatEnergy_le_of_bounded ψ hψmeas hψint
      (ε⁻¹ ^ 2 * B) hψB hs
    refine ⟨henergy.1, ?_⟩
    calc
      Smoothing.heatEnergy s ψ ≤ 4 * s * (ε⁻¹ ^ 2 * B) * (∫ y, |ψ y|) := hcoarse.2
      _ ≤ 4 * B * (∫ y, |φ y|) := by
        rw [hmass]
        have hprod : s * ε⁻¹ ^ 2 ≤ 1 := by
          calc
            s * ε⁻¹ ^ 2 = s / ε ^ 2 := by rw [div_eq_mul_inv, inv_pow]
            _ ≤ 1 := (div_le_one hεsq).2 hsmall
        calc
          4 * s * (ε⁻¹ ^ 2 * B) * (∫ y, |φ y|) =
              (4 * B * (∫ y, |φ y|)) * (s * ε⁻¹ ^ 2) := by ring
          _ ≤ 4 * B * (∫ y, |φ y|) := by
            apply mul_le_of_le_one_right
            · positivity
            · exact hprod
      _ ≤ 4 * B * (∫ y, |φ y|) +
          (∫ y, |φ y|) ^ 2 / Real.pi * max 0 (Real.log (s / ε ^ 2)) := by
        exact le_add_of_nonneg_right (mul_nonneg
          (div_nonneg (sq_nonneg _) (le_of_lt Real.pi_pos)) (le_max_left _ _))
  · have hsmall' : ε ^ 2 ≤ s := le_of_not_ge hsmall
    have hfirstOn : IntegrableOn (Smoothing.continuumHeatProfile ψ) (Set.Icc 0 (ε ^ 2)) :=
      henergy.1.mono_measure (Measure.restrict_mono
        (Set.Icc_subset_Icc_right hsmall') le_rfl)
    have hfirstInterval : IntervalIntegrable (Smoothing.continuumHeatProfile ψ)
        volume 0 (ε ^ 2) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hεsq.le).2 hfirstOn
    have hsecondOn : IntegrableOn (Smoothing.continuumHeatProfile ψ) (Set.Icc (ε ^ 2) s) :=
      henergy.1.mono_measure (Measure.restrict_mono
        (Set.Icc_subset_Icc hεsq.le le_rfl) le_rfl)
    have hsecondInterval : IntervalIntegrable (Smoothing.continuumHeatProfile ψ)
        volume (ε ^ 2) s :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hsmall').2 hsecondOn
    have hsmallBound : ∀ u ∈ Set.Icc (0 : ℝ) (ε ^ 2),
        Smoothing.continuumHeatProfile ψ u ≤ ε⁻¹ ^ 2 * B * (∫ y, |ψ y|) := by
      intro u hu
      by_cases hu0 : u = 0
      · simp [Smoothing.continuumHeatProfile, hu0]
        positivity
      · have huPos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
        exact (Smoothing.continuumHeatProfile_integrable_bound ψ hψmeas hψint
          (ε⁻¹ ^ 2 * B) hψB huPos).2.2
    have hlargeBound : ∀ u ∈ Set.Icc (ε ^ 2) s,
        Smoothing.continuumHeatProfile ψ u ≤
          (∫ y, |ψ y|) ^ 2 / (4 * Real.pi * u) := by
      intro u hu
      exact continuumHeatProfile_le_mass_sq_div ψ hψmeas hψint
        (ε⁻¹ ^ 2 * B) hψB (lt_of_lt_of_le hεsq hu.1)
    have hsmallConstInt : IntervalIntegrable
        (fun _ : ℝ => ε⁻¹ ^ 2 * B * (∫ y, |ψ y|)) volume 0 (ε ^ 2) :=
      intervalIntegrable_const
    have hfirstBound := intervalIntegral.integral_mono_on hεsq.le hfirstInterval
      hsmallConstInt hsmallBound
    have hmem (u : ℝ) (hu : u ∈ Set.uIcc (ε ^ 2) s) : u ∈ Set.Icc (ε ^ 2) s := by
      rw [Set.uIcc_of_le hsmall'] at hu
      exact hu
    have hinvInt : IntervalIntegrable (fun u : ℝ => u⁻¹) volume (ε ^ 2) s :=
      intervalIntegral.intervalIntegrable_inv (fun u hu =>
        ne_of_gt (lt_of_lt_of_le hεsq (hmem u hu).1))
        continuousOn_id
    have hlargeConstInt : IntervalIntegrable
        (fun u : ℝ => (∫ y, |ψ y|) ^ 2 / (4 * Real.pi) * u⁻¹) volume (ε ^ 2) s :=
      hinvInt.const_mul _
    have hsecondBound := intervalIntegral.integral_mono_on hsmall' hsecondInterval
      hlargeConstInt (fun u hu => by
        have hu' : u ∈ Set.Icc (ε ^ 2) s := hu
        have h : Smoothing.continuumHeatProfile ψ u ≤
            (∫ y, |ψ y|) ^ 2 / (4 * Real.pi * u) := hlargeBound u hu'
        have huPos : u ≠ 0 := ne_of_gt (lt_of_lt_of_le hεsq hu'.1)
        calc
          Smoothing.continuumHeatProfile ψ u ≤
              (∫ y, |ψ y|) ^ 2 / (4 * Real.pi * u) := h
          _ = (∫ y, |ψ y|) ^ 2 / (4 * Real.pi) * u⁻¹ := by
            field_simp [huPos, Real.pi_ne_zero])
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      hfirstInterval hsecondInterval
    have hlargeEval : (∫ u in (ε ^ 2)..s, u⁻¹) = Real.log (s / ε ^ 2) :=
      integral_inv_of_pos hεsq hs
    refine ⟨henergy.1, ?_⟩
    rw [henergy.2, ← hsplit]
    rw [hmass] at hfirstBound hsecondBound
    have hsecondBound' :
        (∫ u in (ε ^ 2)..s, Smoothing.continuumHeatProfile ψ u) ≤
          (∫ y, |φ y|) ^ 2 / (4 * Real.pi) * Real.log (s / ε ^ 2) := by
      calc
        (∫ u in (ε ^ 2)..s, Smoothing.continuumHeatProfile ψ u) ≤
            ∫ u in (ε ^ 2)..s,
              ((∫ y, |φ y|) ^ 2 / (4 * Real.pi)) * u⁻¹ := hsecondBound
        _ = (∫ y, |φ y|) ^ 2 / (4 * Real.pi) *
            (∫ u in (ε ^ 2)..s, u⁻¹) := intervalIntegral.integral_const_mul _ _
        _ = (∫ y, |φ y|) ^ 2 / (4 * Real.pi) * Real.log (s / ε ^ 2) := by
          rw [hlargeEval]
    have hlognonneg : 0 ≤ Real.log (s / ε ^ 2) := by
      apply Real.log_nonneg
      exact (one_le_div hεsq).2 hsmall'
    have hmulfirst : ε ^ 2 * (ε⁻¹ ^ 2 * B * (∫ y, |φ y|)) =
        B * (∫ y, |φ y|) := by
      have hinv : ε ^ 2 * ε⁻¹ ^ 2 = 1 := by field_simp
      calc
        ε ^ 2 * (ε⁻¹ ^ 2 * B * (∫ y, |φ y|)) =
            (ε ^ 2 * ε⁻¹ ^ 2) * (B * (∫ y, |φ y|)) := by ring
        _ = B * (∫ y, |φ y|) := by rw [hinv, one_mul]
    calc
      4 * ((∫ u in (0 : ℝ)..ε ^ 2, Smoothing.continuumHeatProfile ψ u) +
          ∫ u in (ε ^ 2)..s, Smoothing.continuumHeatProfile ψ u) ≤
          4 * (ε ^ 2 * (ε⁻¹ ^ 2 * B * (∫ y, |φ y|))) +
          4 * ((∫ y, |φ y|) ^ 2 / (4 * Real.pi) * Real.log (s / ε ^ 2)) := by
        have hfirstBound' := hfirstBound
        simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hfirstBound'
        nlinarith [hfirstBound', hsecondBound']
      _ = 4 * B * (∫ y, |φ y|) +
          ((∫ y, |φ y|) ^ 2 / Real.pi) * Real.log (s / ε ^ 2) := by
        rw [hmulfirst]
        ring
      _ = 4 * B * (∫ y, |φ y|) +
          (∫ y, |φ y|) ^ 2 / Real.pi * max 0 (Real.log (s / ε ^ 2)) := by
        rw [max_eq_right hlognonneg]

end Critical2DKPZ.SmallScales

end
