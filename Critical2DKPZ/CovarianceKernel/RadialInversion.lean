/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.RadialAsymptotic
public import Critical2DKPZ.Spectral.RadialBessel
public import Critical2DKPZ.CovarianceKernel.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! # Integrability of the Bessel inversion -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal

namespace Critical2DKPZ.CovarianceKernel




/-- Double-logarithmic spectral ball growth gives a logarithmic upper bound outside the unit ball. -/
theorem spectralBallMass_logGrowth_of_tendsto (ν : Measure Plane)
    [IsLocallyFiniteMeasure ν]
    (hM : Tendsto (fun R => spectralBallMass ν R / Real.log (Real.log R)) atTop (𝓝 1)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ R : ℝ, 1 ≤ R →
      spectralBallMass ν R ≤ A * (1 + Real.log R) := by
  have hup : ∀ᶠ R : ℝ in atTop,
      spectralBallMass ν R / Real.log (Real.log R) < 2 :=
    hM.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  obtain ⟨S, hS⟩ := Filter.eventually_atTop.mp hup
  let R₀ : ℝ := max S (Real.exp (Real.exp 1) + 1)
  let A : ℝ := max (spectralBallMass ν R₀) 2
  have hR₀one : 1 ≤ R₀ := by
    dsimp [R₀]
    have hpos : 0 < Real.exp (Real.exp 1) := by positivity
    have hone : 1 ≤ Real.exp (Real.exp 1) + 1 := by linarith
    exact hone.trans (le_max_right _ _)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  refine ⟨A, hA_nonneg, fun R hR => ?_⟩
  by_cases hlarge : R₀ ≤ R
  · have hS' : S ≤ R := le_trans (le_max_left _ _) hlarge
    have hratio := hS R hS'
    have hthreshold : Real.exp (Real.exp 1) < R := by
      have hle : Real.exp (Real.exp 1) + 1 ≤ R₀ := le_max_right _ _
      linarith
    have hlogR : 1 < Real.log R := by
      have h := Real.log_lt_log
        (by positivity : (0 : ℝ) < Real.exp (Real.exp 1)) hthreshold
      have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
      rw [Real.log_exp] at h
      exact he.trans h
    have hLpos : 0 < Real.log (Real.log R) := Real.log_pos hlogR
    have hmass : spectralBallMass ν R ≤ 2 * Real.log (Real.log R) := by
      have := (div_lt_iff₀ hLpos).mp hratio
      linarith
    have hloglog : Real.log (Real.log R) ≤ Real.log R := by
      calc
        Real.log (Real.log R) ≤ Real.log R - 1 :=
          Real.log_le_sub_one_of_pos (by linarith : 0 < Real.log R)
        _ ≤ Real.log R := by linarith
    calc
      spectralBallMass ν R ≤ 2 * Real.log (Real.log R) := hmass
      _ ≤ 2 * (1 + Real.log R) := by nlinarith
      _ ≤ A * (1 + Real.log R) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [A]
        exact le_max_right _ _
  · have hRlt : R < R₀ := lt_of_not_ge hlarge
    have hmass : spectralBallMass ν R ≤ spectralBallMass ν R₀ :=
      spectralBallMass_mono ν hRlt.le
    have hlognonneg : 0 ≤ Real.log R := Real.log_nonneg hR
    calc
      spectralBallMass ν R ≤ spectralBallMass ν R₀ := hmass
      _ ≤ A := le_max_left _ _
      _ ≤ A * (1 + Real.log R) := by
        calc
          A = A * 1 := by ring
          _ ≤ A * (1 + Real.log R) :=
            mul_le_mul_of_nonneg_left (by linarith) hA_nonneg

private theorem invSq_radius_log_bound {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    1 ≤ a ^ (-(2 : ℝ)) ∧
      1 + Real.log (a ^ (-(2 : ℝ))) ≤ 5 * a ^ (-(1 / 2 : ℝ)) := by
  have hR : 1 ≤ a ^ (-(2 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos ha ha1 (by norm_num)
  have hroot : 1 ≤ a ^ (-(1 / 2 : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos ha ha1 (by norm_num)
  have hrootEq : (a ^ (-(2 : ℝ))) ^ (1 / 4 : ℝ) = a ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_mul ha.le]
    congr 1
    ring
  have hlog := Real.log_le_rpow_div (by linarith : 0 ≤ a ^ (-(2 : ℝ)))
    (by norm_num : (0 : ℝ) < 1 / 4)
  have hlog' : Real.log (a ^ (-(2 : ℝ))) ≤ 4 * a ^ (-(1 / 2 : ℝ)) := by
    rw [hrootEq] at hlog
    norm_num at hlog ⊢
    linarith
  constructor
  · exact hR
  · nlinarith

/-- The radial weight is `|ξ|^(-1/2)` on and outside the unit sphere and zero inside it. -/
def spectralInverseSqrtTail (ξ : Plane) : ℝ :=
  if 1 ≤ ‖ξ‖ then (Real.sqrt ‖ξ‖)⁻¹ else 0

/-- The inverse-square-root radial weight restricted to the exterior of a ball. -/
def spectralInverseSqrtTailAbove (S : ℝ) (ξ : Plane) : ℝ :=
  {ξ : Plane | S < ‖ξ‖}.indicator spectralInverseSqrtTail ξ

/-- The inverse-square-root radial weight `spectralInverseSqrtTail` is integrable against a locally
finite measure on the plane whose ball mass `spectralBallMass ν R` is at most
`A * (1 + log R)` for every `R ≥ 1`. -/
theorem integrable_spectralInverseSqrtTail_of_logGrowth (ν : Measure Plane)
    [IsLocallyFiniteMeasure ν] {A : ℝ} (hA : 0 ≤ A)
    (hGrowth : ∀ R : ℝ, 1 ≤ R → spectralBallMass ν R ≤ A * (1 + Real.log R)) :
    Integrable (spectralInverseSqrtTail) ν := by
  have hnormMeas : Measurable (fun ξ : Plane => ‖ξ‖) := measurable_norm
  have hbranch : MeasurableSet {ξ : Plane | 1 ≤ ‖ξ‖} :=
    (measurableSet_Ici.preimage hnormMeas)
  have htailMeas : Measurable spectralInverseSqrtTail := by
    unfold spectralInverseSqrtTail
    exact Measurable.ite hbranch
      ((Real.continuous_sqrt.measurable.comp hnormMeas).inv) measurable_const
  have htailNN : ∀ ξ : Plane, 0 ≤ spectralInverseSqrtTail ξ := by
    intro ξ
    by_cases hξ : 1 ≤ ‖ξ‖
    · simp [spectralInverseSqrtTail, hξ]
    · simp [spectralInverseSqrtTail, hξ]
  have htailLeOne : ∀ ξ : Plane, spectralInverseSqrtTail ξ ≤ 1 := by
    intro ξ
    by_cases hξ : 1 ≤ ‖ξ‖
    · simpa [spectralInverseSqrtTail, hξ] using
        (inv_le_one₀ (Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hξ))).2
          (Real.one_le_sqrt.mpr hξ)
    · simp [spectralInverseSqrtTail, hξ]
  have hformula :
      (∫⁻ ξ, ENNReal.ofReal (spectralInverseSqrtTail ξ) ∂ν) =
        ∫⁻ a in Set.Ioi (0 : ℝ), ν {ξ : Plane | a < spectralInverseSqrtTail ξ} := by
    exact MeasureTheory.lintegral_eq_lintegral_meas_lt ν
      (Eventually.of_forall htailNN) htailMeas.aemeasurable
  have hmassBound : ∀ a : ℝ, 0 < a → a < 1 →
      ν {ξ : Plane | a < spectralInverseSqrtTail ξ} ≤
        ENNReal.ofReal (5 * A * a ^ (-(1 / 2 : ℝ))) := by
    intro a ha ha1
    let R : ℝ := a ^ (-(2 : ℝ))
    have hRinfo := invSq_radius_log_bound ha (le_of_lt ha1)
    have hsubset : {ξ : Plane | a < spectralInverseSqrtTail ξ} ⊆
        Metric.closedBall (0 : Plane) R := by
      intro ξ hξ
      have hnorm : 1 ≤ ‖ξ‖ := by
        by_contra hnot
        have hlt : ‖ξ‖ < 1 := lt_of_not_ge hnot
        have : spectralInverseSqrtTail ξ = 0 := by
          simp [spectralInverseSqrtTail, not_le.mpr hlt]
        change a < spectralInverseSqrtTail ξ at hξ
        rw [this] at hξ
        linarith
      have hnormPos : 0 < ‖ξ‖ := by linarith
      have hsqrtPos : 0 < Real.sqrt ‖ξ‖ := Real.sqrt_pos.2 hnormPos
      have hfa : a < (Real.sqrt ‖ξ‖)⁻¹ := by
        simpa [spectralInverseSqrtTail, hnorm] using hξ
      have hfa' : a < 1 * (Real.sqrt ‖ξ‖)⁻¹ := by simpa using hfa
      have hmul : a * Real.sqrt ‖ξ‖ < 1 := by
        simpa [mul_comm] using (lt_mul_inv_iff₀ hsqrtPos).mp hfa'
      have hsqrtBound : Real.sqrt ‖ξ‖ < a⁻¹ := by
        have hmul' : Real.sqrt ‖ξ‖ * a < 1 := by nlinarith [hmul]
        simpa using (lt_mul_inv_iff₀ ha).mpr hmul'
      have hsquares : (Real.sqrt ‖ξ‖) ^ 2 < (a⁻¹) ^ 2 :=
        (sq_lt_sq₀ (Real.sqrt_nonneg _) (inv_nonneg.mpr ha.le)).mpr hsqrtBound
      have hrad : ‖ξ‖ < R := by
        dsimp [R]
        calc
          ‖ξ‖ = (Real.sqrt ‖ξ‖) ^ 2 := (Real.sq_sqrt hnormPos.le).symm
          _ < (a⁻¹) ^ 2 := hsquares
          _ = a ^ (-(2 : ℝ)) := by
            rw [Real.rpow_neg ha.le]
            field_simp
            exact Real.rpow_natCast a 2
      exact Metric.mem_closedBall.mpr (by simpa [dist_zero_right] using hrad.le)
    have hballFinite : ν (Metric.closedBall (0 : Plane) R) ≠ ⊤ :=
      (isCompact_closedBall (0 : Plane) R).measure_ne_top
    have hmass : spectralBallMass ν R ≤ A * (1 + Real.log R) :=
      hGrowth R hRinfo.1
    have hbound : A * (1 + Real.log R) ≤ 5 * A * a ^ (-(1 / 2 : ℝ)) := by
      have hfactor := hRinfo.2
      have := mul_le_mul_of_nonneg_left hfactor hA
      nlinarith
    calc
      ν {ξ : Plane | a < spectralInverseSqrtTail ξ} ≤ ν (Metric.closedBall 0 R) :=
        measure_mono hsubset
      _ = ENNReal.ofReal (spectralBallMass ν R) := (ENNReal.ofReal_toReal hballFinite).symm
      _ ≤ ENNReal.ofReal (A * (1 + Real.log R)) := ENNReal.ofReal_le_ofReal hmass
      _ ≤ ENNReal.ofReal (5 * A * a ^ (-(1 / 2 : ℝ))) := ENNReal.ofReal_le_ofReal hbound
  have hpoint : ∀ a : ℝ,
      (Set.Ioi (0 : ℝ)).indicator
          (fun x => ν {ξ : Plane | x < spectralInverseSqrtTail ξ}) a ≤
        (Set.Ioo (0 : ℝ) 1).indicator
          (fun x => ENNReal.ofReal (5 * A * x ^ (-(1 / 2 : ℝ)))) a := by
    intro a
    by_cases ha : 0 < a
    · by_cases ha1 : a < 1
      · simp only [Set.indicator_of_mem (Set.mem_Ioi.mpr ha),
          Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨ha, ha1⟩)]
        exact hmassBound a ha ha1
      · have hempty : {ξ : Plane | a < spectralInverseSqrtTail ξ} = ∅ := by
          ext ξ
          change (a < spectralInverseSqrtTail ξ) ↔ False
          constructor
          · intro hξ
            exact (not_lt_of_ge ((htailLeOne ξ).trans (le_of_not_gt ha1))) hξ
          · intro hfalse
            exact False.elim hfalse
        simp [Set.indicator, Set.mem_Ioi, Set.mem_Ioo, ha, ha1, hempty]
    · simp [Set.indicator, Set.mem_Ioi, Set.mem_Ioo, ha]
  have hlayerBound :
      (∫⁻ a in Set.Ioi (0 : ℝ), ν {ξ : Plane | a < spectralInverseSqrtTail ξ}) ≤
        ∫⁻ a in Set.Ioo (0 : ℝ) 1,
          ENNReal.ofReal (5 * A * a ^ (-(1 / 2 : ℝ))) := by
    rw [← lintegral_indicator measurableSet_Ioi,
      ← lintegral_indicator measurableSet_Ioo]
    exact lintegral_mono hpoint
  have hpowInt : IntegrableOn (fun a : ℝ => a ^ (-(1 / 2 : ℝ)))
      (Set.Ioo (0 : ℝ) 1) volume := by
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)]
    norm_num
  have hmajorInt : IntegrableOn
      (fun a : ℝ => 5 * A * a ^ (-(1 / 2 : ℝ))) (Set.Ioo (0 : ℝ) 1) volume :=
    hpowInt.const_mul (5 * A)
  have hmajorFinite :
      (∫⁻ a in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (5 * A * a ^ (-(1 / 2 : ℝ)))) < ⊤ :=
    hmajorInt.lintegral_lt_top
  have hfinite :
      (∫⁻ ξ, ENNReal.ofReal (spectralInverseSqrtTail ξ) ∂ν) < ⊤ := by
    rw [hformula]
    exact lt_of_le_of_lt hlayerBound hmajorFinite
  have hfi : HasFiniteIntegral spectralInverseSqrtTail ν :=
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall htailNN)).2 hfinite
  exact ⟨htailMeas.aestronglyMeasurable, hfi⟩

/-- A logarithmic dilation bound gives integrability of the exterior inverse-square-root weight and bounds its integral by the spectral mass at the cutoff radius. -/
theorem integrable_inverseSqrtTailAbove_integral_bound (ν : Measure Plane)
    [IsLocallyFiniteMeasure ν] {A S : ℝ} (hA : 0 ≤ A) (hS : 1 ≤ S)
    (hGrowth : ∀ R : ℝ, 1 ≤ R → spectralBallMass ν R ≤ A * (1 + Real.log R))
    (hDilation : ∀ u : ℝ, 1 ≤ u →
      spectralBallMass ν (S * u) ≤ A * (1 + Real.log u) * spectralBallMass ν S) :
    Integrable (spectralInverseSqrtTailAbove S) ν ∧
      (∫ ξ, spectralInverseSqrtTailAbove S ξ ∂ν) ≤
        10 * A * spectralBallMass ν S / Real.sqrt S := by
  let E : Set Plane := {ξ : Plane | S < ‖ξ‖}
  let c : ℝ := 1 / Real.sqrt S
  let G : ℝ → ℝ := fun a => c * Real.sqrt S * 5 * A * spectralBallMass ν S *
    ((a * Real.sqrt S) ^ (-(1 / 2 : ℝ)))
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hsqrtSpos : 0 < Real.sqrt S := Real.sqrt_pos.2 hSpos
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hEmeas : MeasurableSet E := by
    dsimp [E]
    exact measurableSet_Ioi.preimage measurable_norm
  have htail : Integrable spectralInverseSqrtTail ν :=
    integrable_spectralInverseSqrtTail_of_logGrowth ν hA hGrowth
  have htailAboveMeas : Measurable (spectralInverseSqrtTailAbove S) := by
    unfold spectralInverseSqrtTailAbove
    have htailBaseMeas : Measurable spectralInverseSqrtTail := by
      unfold spectralInverseSqrtTail
      exact Measurable.ite (measurableSet_Ici.preimage measurable_norm)
        ((Real.continuous_sqrt.measurable.comp measurable_norm).inv) measurable_const
    exact htailBaseMeas.indicator (measurableSet_Ioi.preimage measurable_norm)
  have htailAboveNN : ∀ ξ : Plane, 0 ≤ spectralInverseSqrtTailAbove S ξ := by
    intro ξ
    by_cases hξ : ξ ∈ E
    · have hnorm : 1 ≤ ‖ξ‖ := le_trans hS (le_of_lt hξ)
      simp [spectralInverseSqrtTailAbove, E, hξ, spectralInverseSqrtTail, hnorm]
    · simp [spectralInverseSqrtTailAbove, E, hξ]
  have htailAboveLe : ∀ ξ : Plane,
      spectralInverseSqrtTailAbove S ξ ≤ spectralInverseSqrtTail ξ := by
    intro ξ
    by_cases hξ : ξ ∈ E
    · have hnorm : 1 ≤ ‖ξ‖ := le_trans hS (le_of_lt hξ)
      simp [spectralInverseSqrtTailAbove, E, hξ, spectralInverseSqrtTail, hnorm]
    · by_cases hnorm : 1 ≤ ‖ξ‖ <;>
        simp [spectralInverseSqrtTailAbove, E, hξ, spectralInverseSqrtTail, hnorm]
  have htailAboveInt : Integrable (spectralInverseSqrtTailAbove S) ν :=
    htail.mono' htailAboveMeas.aestronglyMeasurable
      (Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (htailAboveNN ξ)]
        exact htailAboveLe ξ)
  have hcutoff : 0 < c := hcpos
  have hGint : Integrable G (volume.restrict (Set.Ioc (0 : ℝ) c)) := by
    have hpower : IntervalIntegrable (fun a : ℝ => a ^ (-(1 / 2 : ℝ))) volume 0 c :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num : -1 < -(1 / 2 : ℝ))
    have hpowerOn : IntegrableOn (fun a : ℝ => a ^ (-(1 / 2 : ℝ)))
        (Set.Ioc (0 : ℝ) c) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hcutoff.le).1 hpower
    have hGae : G =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) c)] fun a =>
        (c * Real.sqrt S * 5 * A * spectralBallMass ν S *
          (Real.sqrt S ^ (-(1 / 2 : ℝ)))) * a ^ (-(1 / 2 : ℝ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
      dsimp [G]
      rw [Real.mul_rpow ha.1.le (Real.sqrt_nonneg _)]
      ring
    exact ((hpowerOn.const_mul
      (c * Real.sqrt S * 5 * A * spectralBallMass ν S *
        (Real.sqrt S ^ (-(1 / 2 : ℝ))))).congr hGae.symm)
  have hGnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) c)] G := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
    dsimp [G]
    have hmassNN : 0 ≤ spectralBallMass ν S := ENNReal.toReal_nonneg
    have hpowNN : 0 ≤ (a * Real.sqrt S) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_nonneg (mul_nonneg ha.1.le (Real.sqrt_nonneg _)) _
    have hcoeff : 0 ≤ c * Real.sqrt S * 5 * A * spectralBallMass ν S := by
      positivity
    exact mul_nonneg hcoeff hpowNN
  have hGintegral : (∫ a in Set.Ioc (0 : ℝ) c, G a) =
      10 * A * spectralBallMass ν S / Real.sqrt S := by
    have hbase : (∫ a in Set.Ioc (0 : ℝ) c,
        (a * Real.sqrt S) ^ (-(1 / 2 : ℝ))) = 2 / Real.sqrt S := by
      rw [← intervalIntegral.integral_of_le hcutoff.le]
      have hcomp := intervalIntegral.integral_comp_mul_left
        (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (ne_of_gt hsqrtSpos)
        (a := 0) (b := c) (c := Real.sqrt S)
      have hcomm : (∫ a : ℝ in (0 : ℝ)..c, (a * Real.sqrt S) ^ (-(1 / 2 : ℝ))) =
          ∫ a : ℝ in (0 : ℝ)..c, (Real.sqrt S * a) ^ (-(1 / 2 : ℝ)) := by
        apply intervalIntegral.integral_congr
        intro a _
        exact congrArg (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (mul_comm a (Real.sqrt S))
      rw [hcomm, hcomp]
      simp only [mul_zero]
      have hsc : Real.sqrt S * c = 1 := by
        dsimp [c]
        field_simp
      rw [hsc]
      rw [integral_rpow (Or.inl (by norm_num : -1 < -(1 / 2 : ℝ)))]
      norm_num [Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)]
      field_simp
    calc
      (∫ a in Set.Ioc (0 : ℝ) c, G a) =
          c * Real.sqrt S * 5 * A * spectralBallMass ν S *
            (∫ a in Set.Ioc (0 : ℝ) c, (a * Real.sqrt S) ^ (-(1 / 2 : ℝ))) := by
              simp only [G, integral_const_mul]
      _ = 10 * A * spectralBallMass ν S / Real.sqrt S := by
        rw [hbase]
        dsimp [c]
        field_simp
        ring
  have hlevel : ∀ a : ℝ,
      (Set.Ioi (0 : ℝ)).indicator
          (fun r => ν {ξ : Plane | r < spectralInverseSqrtTailAbove S ξ}) a ≤
        (Set.Ioc (0 : ℝ) c).indicator (fun r => ENNReal.ofReal (G r)) a := by
    intro a
    by_cases ha : 0 < a
    · by_cases hac : a < c
      · simp only [Set.indicator_of_mem (Set.mem_Ioi.mpr ha),
          Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨ha, hac.le⟩)]
        have hvalPos : 0 < a * Real.sqrt S := mul_pos ha hsqrtSpos
        let u : ℝ := (a * Real.sqrt S) ^ (-(2 : ℝ))
        have huInfo := invSq_radius_log_bound hvalPos (le_of_lt (show a * Real.sqrt S < 1 by
          have h := (lt_mul_inv_iff₀ hsqrtSpos).mp hac
          simpa [c] using h))
        have hu : 1 ≤ u := by simpa [u] using huInfo.1
        have huEq : u = a ^ (-(2 : ℝ)) / S := by
          dsimp [u]
          rw [Real.rpow_neg hvalPos.le, Real.rpow_neg ha.le]
          rw [Real.rpow_two, Real.rpow_two]
          rw [mul_pow, Real.sq_sqrt hSpos.le]
          field_simp
        have hSu : S * u = a ^ (-(2 : ℝ)) := by
          rw [huEq]
          field_simp
        have hlevelSub : {ξ : Plane | a < spectralInverseSqrtTailAbove S ξ} ⊆
            Metric.closedBall (0 : Plane) (a ^ (-(2 : ℝ))) := by
          intro ξ hξ
          change a < spectralInverseSqrtTailAbove S ξ at hξ
          have hξE : ξ ∈ E := by
            by_contra hnot
            have hzero : spectralInverseSqrtTailAbove S ξ = 0 := by
              simp [spectralInverseSqrtTailAbove, E, hnot]
            rw [hzero] at hξ
            linarith
          have hnormOne : 1 ≤ ‖ξ‖ := le_trans hS (le_of_lt hξE)
          have hrootPos : 0 < Real.sqrt ‖ξ‖ :=
            Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hnormOne)
          have hfa : a < (Real.sqrt ‖ξ‖)⁻¹ := by
            simpa [spectralInverseSqrtTailAbove, E, hξE,
              spectralInverseSqrtTail, hnormOne] using hξ
          have hfa' : a < 1 * (Real.sqrt ‖ξ‖)⁻¹ := by simpa using hfa
          have hmul : a * Real.sqrt ‖ξ‖ < 1 :=
            (lt_mul_inv_iff₀ hrootPos).mp hfa'
          have hrootBound : Real.sqrt ‖ξ‖ < a⁻¹ := by
            have hmul' : Real.sqrt ‖ξ‖ * a < 1 := by nlinarith [hmul]
            simpa using (lt_mul_inv_iff₀ ha).mpr hmul'
          have hsquares : (Real.sqrt ‖ξ‖) ^ 2 < (a⁻¹) ^ 2 :=
            (sq_lt_sq₀ (Real.sqrt_nonneg _) (inv_nonneg.mpr ha.le)).mpr hrootBound
          have hrad : ‖ξ‖ < a ^ (-(2 : ℝ)) := by
            calc
              ‖ξ‖ = (Real.sqrt ‖ξ‖) ^ 2 := (Real.sq_sqrt (norm_nonneg ξ)).symm
              _ < (a⁻¹) ^ 2 := hsquares
              _ = a ^ (-(2 : ℝ)) := by
                rw [Real.rpow_neg ha.le]
                simp [inv_pow]
          exact Metric.mem_closedBall.mpr (by simpa [dist_zero_right] using hrad.le)
        have hballFinite : ν (Metric.closedBall (0 : Plane) (a ^ (-(2 : ℝ)))) ≠ ⊤ :=
          (isCompact_closedBall (0 : Plane) (a ^ (-(2 : ℝ)))).measure_ne_top
        have hmass : spectralBallMass ν (a ^ (-(2 : ℝ))) ≤
            A * (1 + Real.log u) * spectralBallMass ν S := by
          rw [← hSu]
          exact hDilation u hu
        have hbound : A * (1 + Real.log u) * spectralBallMass ν S ≤ G a := by
          have hmassNN : 0 ≤ spectralBallMass ν S := ENNReal.toReal_nonneg
          calc
            A * (1 + Real.log u) * spectralBallMass ν S ≤
                A * (5 * (a * Real.sqrt S) ^ (-(1 / 2 : ℝ))) *
                  spectralBallMass ν S := by
              apply mul_le_mul_of_nonneg_right _ hmassNN
              exact mul_le_mul_of_nonneg_left huInfo.2 hA
            _ = G a := by
              dsimp [G, c]
              field_simp
        calc
          ν {ξ : Plane | a < spectralInverseSqrtTailAbove S ξ} ≤
              ν (Metric.closedBall (0 : Plane) (a ^ (-(2 : ℝ)))) :=
            measure_mono hlevelSub
          _ = ENNReal.ofReal (spectralBallMass ν (a ^ (-(2 : ℝ)))) :=
            (ENNReal.ofReal_toReal hballFinite).symm
          _ ≤ ENNReal.ofReal (A * (1 + Real.log u) * spectralBallMass ν S) :=
            ENNReal.ofReal_le_ofReal hmass
          _ ≤ ENNReal.ofReal (G a) := ENNReal.ofReal_le_ofReal hbound
      · have hempty : {ξ : Plane | a < spectralInverseSqrtTailAbove S ξ} = ∅ := by
          ext ξ
          constructor
          · intro hξ
            change a < spectralInverseSqrtTailAbove S ξ at hξ
            have hξE : ξ ∈ E := by
              by_contra hnot
              change a < spectralInverseSqrtTailAbove S ξ at hξ
              have hzero : spectralInverseSqrtTailAbove S ξ = 0 := by
                simp [spectralInverseSqrtTailAbove, E, hnot]
              rw [hzero] at hξ
              linarith
            have hradOne : 1 ≤ ‖ξ‖ := le_trans hS (le_of_lt hξE)
            have htailValue : spectralInverseSqrtTailAbove S ξ = (Real.sqrt ‖ξ‖)⁻¹ := by
              simp [spectralInverseSqrtTailAbove, E, hξE,
                spectralInverseSqrtTail, hradOne]
            have hrootLe : Real.sqrt S ≤ Real.sqrt ‖ξ‖ := Real.sqrt_le_sqrt (le_of_lt hξE)
            have hinvLe : (Real.sqrt ‖ξ‖)⁻¹ ≤ c := by
              dsimp [c]
              simpa [one_div] using (inv_le_inv₀ (Real.sqrt_pos.2
                (lt_of_lt_of_le zero_lt_one hradOne)) hsqrtSpos).2 hrootLe
            rw [htailValue] at hξ
            exact (not_lt_of_ge (hinvLe.trans (le_of_not_gt hac))) hξ
          · intro hfalse
            exact False.elim hfalse
        have hleft : (Set.Ioi (0 : ℝ)).indicator
            (fun r => ν {ξ : Plane | r < spectralInverseSqrtTailAbove S ξ}) a = 0 := by
          simp [Set.indicator, Set.mem_Ioi, ha, hempty]
        rw [hleft]
        exact zero_le
    · have hleft : (Set.Ioi (0 : ℝ)).indicator
          (fun r => ν {ξ : Plane | r < spectralInverseSqrtTailAbove S ξ}) a = 0 := by
        simp [Set.indicator, Set.mem_Ioi, ha]
      rw [hleft]
      exact zero_le
  have hlayerBound :
      (∫⁻ a in Set.Ioi (0 : ℝ), ν {ξ : Plane | a < spectralInverseSqrtTailAbove S ξ}) ≤
        ∫⁻ a in Set.Ioc (0 : ℝ) c, ENNReal.ofReal (G a) := by
    rw [← lintegral_indicator measurableSet_Ioi,
      ← lintegral_indicator measurableSet_Ioc]
    exact lintegral_mono hlevel
  have hmajorFin :
      (∫⁻ a in Set.Ioc (0 : ℝ) c, ENNReal.ofReal (G a)) < ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hGint hGnonneg]
    rw [hGintegral]
    exact lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top
  have hLayerEq :
      (∫⁻ ξ, ENNReal.ofReal (spectralInverseSqrtTailAbove S ξ) ∂ν) =
        ∫⁻ a in Set.Ioi (0 : ℝ),
          ν {ξ : Plane | a < spectralInverseSqrtTailAbove S ξ} :=
    lintegral_eq_lintegral_meas_lt ν
      (Eventually.of_forall htailAboveNN) htailAboveMeas.aemeasurable
  have hOfRealTail := ofReal_integral_eq_lintegral_ofReal htailAboveInt
    (Eventually.of_forall htailAboveNN)
  have hIntegralBound :
      (∫ ξ, spectralInverseSqrtTailAbove S ξ ∂ν) ≤
        10 * A * spectralBallMass ν S / Real.sqrt S := by
    have hmassNN : 0 ≤ spectralBallMass ν S := ENNReal.toReal_nonneg
    have hnonneg : 0 ≤ 10 * A * spectralBallMass ν S / Real.sqrt S := by positivity
    apply (ENNReal.ofReal_le_ofReal_iff hnonneg).mp
    have hboundENN := hlayerBound
    rw [← hLayerEq, ← hOfRealTail,
      ← ofReal_integral_eq_lintegral_ofReal hGint hGnonneg, hGintegral] at hboundENN
    exact hboundENN
  exact ⟨htailAboveInt, hIntegralBound⟩

/-- For a nonzero spatial radius, the angular Bessel transform is integrable against a spectral
measure with logarithmic ball growth. The local part is bounded on a compact ball; the exterior
part is controlled by the inverse square-root tail. -/
theorem integrable_besselJ0_of_logGrowth (ν : Measure Plane)
    [IsLocallyFiniteMeasure ν] {A : ℝ} (hA : 0 ≤ A)
    (hGrowth : ∀ R : ℝ, 1 ≤ R → spectralBallMass ν R ≤ A * (1 + Real.log R))
    (z : Plane) (hz : z ≠ 0) :
    Integrable (fun ξ : Plane => Spectral.besselJ0Angular (‖ξ‖ * ‖z‖)) ν := by
  let q : ℝ := ‖z‖
  let R : ℝ := max 1 q⁻¹
  let B : Set Plane := Metric.closedBall (0 : Plane) R
  let J : Plane → ℝ := fun ξ => Spectral.besselJ0Angular (‖ξ‖ * q)
  let C : ℝ := 3 / Real.sqrt q
  have hq : 0 < q := norm_pos_iff.mpr hz
  have hRone : 1 ≤ R := le_max_left _ _
  have hRinv : q⁻¹ ≤ R := le_max_right _ _
  have hBcompact : IsCompact B := by
    dsimp [B]
    exact isCompact_closedBall (0 : Plane) R
  have hBfinite : ν B ≠ ⊤ := hBcompact.measure_ne_top
  have hBmeas : MeasurableSet B := hBcompact.measurableSet
  have hJcont : Continuous J := by
    dsimp [J, q]
    exact Spectral.continuous_besselJ0Angular.comp (continuous_norm.mul continuous_const)
  have hJmeas : Measurable J := hJcont.measurable
  have hCnn : 0 ≤ C := by positivity
  have hTail : Integrable (spectralInverseSqrtTail) ν :=
    integrable_spectralInverseSqrtTail_of_logGrowth ν hA hGrowth
  have htailNN : ∀ ξ : Plane, 0 ≤ spectralInverseSqrtTail ξ := by
    intro ξ
    by_cases hξ : 1 ≤ ‖ξ‖
    · simp [spectralInverseSqrtTail, hξ]
    · simp [spectralInverseSqrtTail, hξ]
  have hballOne : Integrable (B.indicator (fun _ : Plane => (1 : ℝ))) ν := by
    exact (integrableOn_const (μ := ν) (s := B) (C := (1 : ℝ))
      (hs := hBfinite)).integrable_indicator hBmeas
  have htailScale : Integrable (fun ξ : Plane => C * spectralInverseSqrtTail ξ) ν :=
    hTail.const_mul C
  have hmajor : Integrable
      (fun ξ : Plane => B.indicator (fun _ : Plane => (1 : ℝ)) ξ +
        C * spectralInverseSqrtTail ξ) ν := hballOne.add htailScale
  have houtside : ∀ ξ : Plane, ξ ∉ B → |J ξ| ≤ C * spectralInverseSqrtTail ξ := by
    intro ξ hξ
    have hnormGt : R < ‖ξ‖ := by
      have hnot : ¬ ‖ξ‖ ≤ R := by
        intro hle
        apply hξ
        exact Metric.mem_closedBall.mpr (by simpa [B, dist_zero_right] using hle)
      exact lt_of_not_ge hnot
    have hnormOne : 1 ≤ ‖ξ‖ := le_trans hRone hnormGt.le
    have hnormPos : 0 ≤ ‖ξ‖ := norm_nonneg _
    have hqInvLe : q⁻¹ ≤ ‖ξ‖ := le_trans hRinv hnormGt.le
    have hprod : 1 ≤ ‖ξ‖ * q := by
      calc
        1 = q⁻¹ * q := by field_simp
        _ ≤ ‖ξ‖ * q := mul_le_mul_of_nonneg_right hqInvLe hq.le
    have hJbound : |J ξ| ≤ 3 / Real.sqrt (‖ξ‖ * q) := by
      dsimp [J]
      exact Spectral.abs_besselJ0Angular_le_three_div_sqrt hprod
    have hsqrtMul : Real.sqrt (‖ξ‖ * q) = Real.sqrt ‖ξ‖ * Real.sqrt q :=
      Real.sqrt_mul hnormPos q
    calc
      |J ξ| ≤ 3 / Real.sqrt (‖ξ‖ * q) := hJbound
      _ = C * spectralInverseSqrtTail ξ := by
        have htailEq : spectralInverseSqrtTail ξ = (Real.sqrt ‖ξ‖)⁻¹ := by
          simp [spectralInverseSqrtTail, hnormOne]
        rw [hsqrtMul, htailEq]
        dsimp [C]
        field_simp
  have hpoint : ∀ ξ : Plane,
      ‖J ξ‖ ≤ B.indicator (fun _ : Plane => (1 : ℝ)) ξ +
        C * spectralInverseSqrtTail ξ := by
    intro ξ
    by_cases hξ : ξ ∈ B
    · have hJone := Spectral.abs_besselJ0Angular_le_one (‖ξ‖ * q)
      have htailnn := htailNN ξ
      simp [Set.indicator, hξ, Real.norm_eq_abs]
      nlinarith [hJone, mul_nonneg hCnn htailnn]
    · simp [Set.indicator, hξ, Real.norm_eq_abs]
      exact houtside ξ hξ
  have hJ : Integrable J ν :=
    hmajor.mono' hJmeas.aestronglyMeasurable (Eventually.of_forall hpoint)
  simpa [J, q] using hJ

/-- The compensated Bessel integrand defining `besselInversion` is integrable away from the
origin. -/
theorem integrable_besselInversion_integrand_of_logGrowth (ν : Measure Plane)
    [IsLocallyFiniteMeasure ν] {A : ℝ} (hA : 0 ≤ A)
    (hGrowth : ∀ R : ℝ, 1 ≤ R → spectralBallMass ν R ≤ A * (1 + Real.log R))
    (z : Plane) (hz : z ≠ 0) :
    Integrable (fun ξ : Plane => Spectral.besselJ0Angular (‖ξ‖ * ‖z‖) -
      (Metric.closedBall (0 : Plane) 1).indicator (fun _ : Plane => (1 : ℝ)) ξ) ν := by
  have hJ := integrable_besselJ0_of_logGrowth ν hA hGrowth z hz
  have hball : IsCompact (Metric.closedBall (0 : Plane) 1) := isCompact_closedBall _ _
  have hballFinite : ν (Metric.closedBall (0 : Plane) 1) ≠ ⊤ := hball.measure_ne_top
  have hindicator : Integrable
      ((Metric.closedBall (0 : Plane) 1).indicator (fun _ : Plane => (1 : ℝ))) ν := by
    exact (integrableOn_const (μ := ν) (s := Metric.closedBall 0 1) (C := (1 : ℝ))
      (hs := hballFinite)).integrable_indicator hball.measurableSet
  exact hJ.sub hindicator

/-- The Bessel inversion is continuous at every nonzero point when the spectral ball masses have
logarithmic growth. Dominated convergence applies locally because the spatial radius stays bounded
away from zero. -/
theorem continuousAt_besselInversion_of_logGrowth (ν : Measure Plane)
    [IsLocallyFiniteMeasure ν] {A : ℝ} (hA : 0 ≤ A)
    (hGrowth : ∀ R : ℝ, 1 ≤ R → spectralBallMass ν R ≤ A * (1 + Real.log R))
    (z : Plane) (hz : z ≠ 0) : ContinuousAt (besselInversion ν) z := by
  let q : ℝ := ‖z‖
  let ρ : ℝ := q / 2
  let R : ℝ := max 1 (2 / q)
  let B : Set Plane := Metric.closedBall (0 : Plane) R
  let F : Plane → Plane → ℝ := fun y ξ =>
    Spectral.besselJ0Angular (‖ξ‖ * ‖y‖) -
      (Metric.closedBall (0 : Plane) 1).indicator (fun _ : Plane => (1 : ℝ)) ξ
  have hq : 0 < q := norm_pos_iff.mpr hz
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hRone : 1 ≤ R := le_max_left _ _
  have hRscale : 2 / q ≤ R := le_max_right _ _
  have hBcompact : IsCompact B := by
    dsimp [B]
    exact isCompact_closedBall (0 : Plane) R
  have hBfinite : ν B ≠ ⊤ := hBcompact.measure_ne_top
  have hBmeas : MeasurableSet B := hBcompact.measurableSet
  have hnear : ∀ᶠ y in 𝓝 z, ρ < ‖y‖ := by
    filter_upwards [Metric.ball_mem_nhds z hρ] with y hy
    have hy' : ‖y - z‖ < ρ := by simpa [dist_eq_norm] using hy
    have htriangle : ‖z‖ ≤ ‖z - y‖ + ‖y‖ := by
      calc
        ‖z‖ = ‖(z - y) + y‖ := by congr 1; abel
        _ ≤ ‖z - y‖ + ‖y‖ := norm_add_le _ _
    have hzy : ‖z - y‖ = ‖y - z‖ := norm_sub_rev z y
    change ‖y - z‖ < ‖z‖ / 2 at hy'
    have hρeq : ρ = ‖z‖ / 2 := by simp [ρ, q]
    rw [hzy] at htriangle
    rw [hρeq]
    linarith
  have hmajorInt : Integrable
      (fun ξ : Plane => B.indicator (fun _ => (2 : ℝ)) ξ +
        (3 / Real.sqrt ρ) * spectralInverseSqrtTail ξ) ν := by
    have hball : Integrable (B.indicator (fun _ : Plane => (2 : ℝ))) ν := by
      exact (integrableOn_const (μ := ν) (s := B) (C := (2 : ℝ))
        (hs := hBfinite)).integrable_indicator hBmeas
    have htail := integrable_spectralInverseSqrtTail_of_logGrowth ν hA hGrowth
    exact hball.add (htail.const_mul (3 / Real.sqrt ρ))
  have hFmeas : ∀ᶠ y in 𝓝 z, AEStronglyMeasurable (fun ξ => F y ξ) ν := by
    filter_upwards [hnear] with y hy
    exact (integrable_besselInversion_integrand_of_logGrowth ν hA hGrowth y
      (norm_pos_iff.mp (lt_trans hρ hy))).aestronglyMeasurable
  have houtside : ∀ y : Plane, ρ < ‖y‖ → ∀ ξ : Plane, ξ ∉ B →
      |F y ξ| ≤ (3 / Real.sqrt ρ) * spectralInverseSqrtTail ξ := by
    intro y hy ξ hξ
    have hrad : R < ‖ξ‖ := by
      have hnot : ¬ ‖ξ‖ ≤ R := by
        intro hle
        apply hξ
        exact Metric.mem_closedBall.mpr (by simpa [B, dist_zero_right] using hle)
      exact lt_of_not_ge hnot
    have hradOne : 1 ≤ ‖ξ‖ := le_trans hRone hrad.le
    have hradScale : 2 / q < ‖ξ‖ := lt_of_le_of_lt hRscale hrad
    have hprod : 1 ≤ ‖ξ‖ * ‖y‖ := by
      have hqhalf : 0 < q / 2 := hρ
      have hqhalfEq : (2 / q) * (q / 2) = 1 := by
        field_simp [ne_of_gt hq]
      calc
        1 = (2 / q) * (q / 2) := hqhalfEq.symm
        _ ≤ ‖ξ‖ * (q / 2) := mul_le_mul_of_nonneg_right hradScale.le hqhalf.le
        _ ≤ ‖ξ‖ * ‖y‖ := mul_le_mul_of_nonneg_left hy.le (norm_nonneg _)
    have hJ : |Spectral.besselJ0Angular (‖ξ‖ * ‖y‖)| ≤
        3 / Real.sqrt (‖ξ‖ * ‖y‖) :=
      Spectral.abs_besselJ0Angular_le_three_div_sqrt hprod
    have hballIndicator :
        (Metric.closedBall (0 : Plane) 1).indicator (fun _ : Plane => (1 : ℝ)) ξ = 0 := by
      have hξone : ¬ ξ ∈ Metric.closedBall (0 : Plane) 1 := by
        intro hmem
        have hnorm : ‖ξ‖ ≤ 1 := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hmem
        linarith
      simp [Set.indicator, hξone]
    have hsqrtMul : Real.sqrt (‖ξ‖ * ‖y‖) = Real.sqrt ‖ξ‖ * Real.sqrt ‖y‖ :=
      Real.sqrt_mul (norm_nonneg ξ) _
    have htailEq : spectralInverseSqrtTail ξ = (Real.sqrt ‖ξ‖)⁻¹ := by
      simp [spectralInverseSqrtTail, hradOne]
    change |Spectral.besselJ0Angular (‖ξ‖ * ‖y‖) -
      (Metric.closedBall (0 : Plane) 1).indicator (fun _ : Plane => (1 : ℝ)) ξ| ≤ _
    rw [hballIndicator, sub_zero]
    calc
      |Spectral.besselJ0Angular (‖ξ‖ * ‖y‖)| ≤
          3 / Real.sqrt (‖ξ‖ * ‖y‖) := hJ
      _ ≤ 3 / (Real.sqrt ‖ξ‖ * Real.sqrt ρ) := by
        rw [hsqrtMul]
        have hξpos : 0 < ‖ξ‖ := lt_of_lt_of_le zero_lt_one hradOne
        have hdenPos : 0 < Real.sqrt ‖ξ‖ * Real.sqrt ρ :=
          mul_pos (Real.sqrt_pos.2 hξpos) (Real.sqrt_pos.2 hρ)
        have hdenle : Real.sqrt ‖ξ‖ * Real.sqrt ρ ≤
            Real.sqrt ‖ξ‖ * Real.sqrt ‖y‖ :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hy.le) (Real.sqrt_nonneg _)
        exact div_le_div_of_nonneg_left (by norm_num) hdenPos hdenle
      _ = (3 / Real.sqrt ρ) * spectralInverseSqrtTail ξ := by
        rw [htailEq]
        field_simp [ne_of_gt (Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hradOne)),
          ne_of_gt (Real.sqrt_pos.2 hρ)]
  have hbound : ∀ᶠ y in 𝓝 z, ∀ᵐ ξ ∂ν, ‖F y ξ‖ ≤
      B.indicator (fun _ : Plane => (2 : ℝ)) ξ +
        (3 / Real.sqrt ρ) * spectralInverseSqrtTail ξ := by
    filter_upwards [hnear] with y hy
    filter_upwards [] with ξ
    by_cases hξ : ξ ∈ B
    · have hJ := Spectral.abs_besselJ0Angular_le_one (‖ξ‖ * ‖y‖)
      have hI : |(Metric.closedBall (0 : Plane) 1).indicator
          (fun _ : Plane => (1 : ℝ)) ξ| ≤ 1 := by
        by_cases h1 : ξ ∈ Metric.closedBall (0 : Plane) 1
        · simp [Set.indicator, h1]
        · simp [Set.indicator, h1]
      have htailnn : 0 ≤ spectralInverseSqrtTail ξ := by
        by_cases h1 : 1 ≤ ‖ξ‖ <;> simp [spectralInverseSqrtTail, h1]
      change |Spectral.besselJ0Angular (‖ξ‖ * ‖y‖) -
        (Metric.closedBall (0 : Plane) 1).indicator (fun _ : Plane => (1 : ℝ)) ξ| ≤
        B.indicator (fun _ : Plane => (2 : ℝ)) ξ +
          (3 / Real.sqrt ρ) * spectralInverseSqrtTail ξ
      rw [Set.indicator_of_mem hξ]
      have habs := abs_sub_le (Spectral.besselJ0Angular (‖ξ‖ * ‖y‖)) 0
        ((Metric.closedBall (0 : Plane) 1).indicator (fun _ : Plane => (1 : ℝ)) ξ)
      have habs' : |Spectral.besselJ0Angular (‖ξ‖ * ‖y‖) -
          (Metric.closedBall (0 : Plane) 1).indicator (fun _ : Plane => (1 : ℝ)) ξ| ≤
          |Spectral.besselJ0Angular (‖ξ‖ * ‖y‖)| +
            |(Metric.closedBall (0 : Plane) 1).indicator (fun _ : Plane => (1 : ℝ)) ξ| := by
        simpa using habs
      nlinarith [hJ, hI, mul_nonneg (by positivity : 0 ≤ 3 / Real.sqrt ρ) htailnn]
    · rw [Real.norm_eq_abs]
      exact le_trans (houtside y hy ξ hξ) (by
        simp [Set.indicator, hξ])
  have hFcont : ∀ ξ : Plane, Continuous (fun y : Plane => F y ξ) := by
    intro ξ
    dsimp [F]
    exact (Spectral.continuous_besselJ0Angular.comp
      (continuous_const.mul continuous_norm)).sub continuous_const
  have hlim : ∀ᵐ ξ ∂ν, Tendsto (fun y : Plane => F y ξ) (𝓝 z) (𝓝 (F z ξ)) := by
    filter_upwards [] with ξ
    exact (hFcont ξ).continuousAt.tendsto
  have hconv := tendsto_integral_filter_of_dominated_convergence
    (fun ξ : Plane => B.indicator (fun _ => (2 : ℝ)) ξ +
      (3 / Real.sqrt ρ) * spectralInverseSqrtTail ξ) hFmeas hbound hmajorInt hlim
  change Tendsto (fun y : Plane => (ν (Metric.closedBall 0 1)).toReal +
      ∫ ξ, F y ξ ∂ν) (𝓝 z)
    (𝓝 ((ν (Metric.closedBall 0 1)).toReal + ∫ ξ, F z ξ ∂ν))
  exact tendsto_const_nhds.add hconv

/-- Logarithmic spectral growth gives continuity of the Bessel inversion on the punctured plane. -/
theorem continuousOn_besselInversion_of_logGrowth (ν : Measure Plane)
    [IsLocallyFiniteMeasure ν] {A : ℝ} (hA : 0 ≤ A)
    (hGrowth : ∀ R : ℝ, 1 ≤ R → spectralBallMass ν R ≤ A * (1 + Real.log R)) :
    ContinuousOn (besselInversion ν) {0}ᶜ := by
  intro z hz
  exact (continuousAt_besselInversion_of_logGrowth ν hA hGrowth z hz).continuousWithinAt

end Critical2DKPZ.CovarianceKernel

end
