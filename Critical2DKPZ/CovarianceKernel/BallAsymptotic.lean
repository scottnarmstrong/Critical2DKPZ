/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.Asymptotic
public import Critical2DKPZ.SmallScales.Inputs
import Mathlib.Tactic

/-! # Spectral mass asymptotics from shrinking variance -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BoundedContinuousFunction ComplexConjugate Topology

universe u

namespace Critical2DKPZ.CovarianceKernel

/-- Rescaling the radius by any fixed positive factor preserves the double-logarithmic scale. -/
theorem tendsto_logLog_mul_div_of_pos_const (a : ℝ) (ha : 0 < a) :
    Tendsto (fun R : ℝ => Real.log (Real.log (a * R)) / Real.log (Real.log R))
      atTop (𝓝 1) := by
  have hlog : Tendsto (fun R : ℝ => Real.log R) atTop atTop := Real.tendsto_log_atTop
  have hdiffBase := (Real.tendsto_log_comp_add_sub_log (Real.log a)).comp hlog
  have hdiff : Tendsto
      (fun R : ℝ => Real.log (Real.log (a * R)) - Real.log (Real.log R)) atTop (𝓝 0) := by
    apply hdiffBase.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    simp only [Function.comp_apply, Real.log_mul ha.ne' hR.ne',
      add_comm (Real.log a) (Real.log R)]
  have hden : Tendsto (fun R : ℝ => Real.log (Real.log R)) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hquot := hdiff.div_atTop hden
  have hsum : Tendsto (fun R : ℝ => 1 +
      (Real.log (Real.log (a * R)) - Real.log (Real.log R)) / Real.log (Real.log R))
      atTop (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add hquot
  have hEqEvent : (fun R : ℝ => 1 +
      (Real.log (Real.log (a * R)) - Real.log (Real.log R)) / Real.log (Real.log R)) =ᶠ[atTop]
      fun R => Real.log (Real.log (a * R)) / Real.log (Real.log R) := by
    filter_upwards [eventually_gt_atTop (Real.exp (Real.exp 1))] with R hR
    have hRpos : 0 < R := by
      have h0 : 0 < Real.exp (Real.exp 1) := by positivity
      linarith
    have hlogR : 1 < Real.log R := by
      have h := Real.log_lt_log (by positivity : 0 < Real.exp (Real.exp 1)) hR
      have h1 : 1 < Real.exp 1 := by
        exact Real.one_lt_exp_iff.mpr (by norm_num)
      rw [Real.log_exp] at h
      exact h1.trans h
    have hdenpos : 0 < Real.log (Real.log R) := Real.log_pos hlogR
    have hEq : Real.log (Real.log (a * R)) / Real.log (Real.log R) =
        1 + (Real.log (Real.log (a * R)) - Real.log (Real.log R)) /
          Real.log (Real.log R) := by
      field_simp
      ring
    exact hEq.symm
  simpa only [add_zero] using hsum.congr' hEqEvent

private theorem log_log_pos_of_exp_exp_one_lt {x : ℝ}
    (hx : Real.exp (Real.exp 1) < x) : 0 < Real.log (Real.log x) := by
  have hlog : Real.exp 1 < Real.log x := by
    have h := Real.log_lt_log (by positivity : 0 < Real.exp (Real.exp 1)) hx
    simpa using h
  exact Real.log_pos (lt_trans (by norm_num) hlog)

/-- Rescaling the radius by a fixed positive factor preserves a double-logarithmic energy
asymptotic. -/
private theorem tendsto_scaled_energy_div_logLog {E : ℝ → ℝ} (hE :
    Tendsto (fun R : ℝ => E R / Real.log (Real.log R)) atTop (𝓝 1))
    (a : ℝ) (ha : 0 < a) :
    Tendsto (fun R : ℝ => E (a * R) / Real.log (Real.log R)) atTop (𝓝 1) := by
  have hEscale := hE.comp (tendsto_id.const_mul_atTop ha)
  have hLscale := tendsto_logLog_mul_div_of_pos_const a ha
  have hprod := hEscale.mul hLscale
  have hlarge : ∀ᶠ R : ℝ in atTop,
      Real.exp (Real.exp 1) < R ∧ Real.exp (Real.exp 1) < a * R := by
    have haTop : Tendsto (fun R : ℝ => a * R) atTop atTop :=
      tendsto_id.const_mul_atTop ha
    filter_upwards [eventually_gt_atTop (Real.exp (Real.exp 1)),
      haTop.eventually (eventually_gt_atTop (Real.exp (Real.exp 1)))] with R hR hR'
    exact ⟨hR, hR'⟩
  have hEqEvent : (fun R : ℝ =>
      ((fun S : ℝ => E S / Real.log (Real.log S)) (a * R)) *
        (Real.log (Real.log (a * R)) / Real.log (Real.log R))) =ᶠ[atTop]
      fun R => E (a * R) / Real.log (Real.log R) := by
    filter_upwards [hlarge] with R hR
    have hD1 : Real.log (Real.log (a * R)) ≠ 0 :=
      (log_log_pos_of_exp_exp_one_lt hR.2).ne'
    have hD2 : Real.log (Real.log R) ≠ 0 :=
      (log_log_pos_of_exp_exp_one_lt hR.1).ne'
    have hEq : (E (a * R) / Real.log (Real.log (a * R))) *
        (Real.log (Real.log (a * R)) / Real.log (Real.log R)) =
        E (a * R) / Real.log (Real.log R) := by
      field_simp [hD1, hD2]
    exact hEq
  simpa only [mul_one] using hprod.congr' hEqEvent

/-- The spectral energy of the dilated unit-mass test has the same double-logarithmic
asymptotic as its field variance. -/
theorem unitMass_fourierEnergy_tendsto_of {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr)
    (hShrinkingVarianceInput : SmallScales.ShrinkingVarianceAt P H) (t : ℝ) (ht : 0 < t)
    (ν : Measure Plane)
    (hν : ∀ f g : TestFn,
      cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P] =
        ∫ ξ, (Spectral.fourierKPZ f ξ * conj (Spectral.fourierKPZ g ξ)).re ∂ν) :
    Tendsto (fun R : ℝ =>
      (∫ ξ, ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn (R⁻¹ • ξ)‖ ^ 2 ∂ν) /
        Real.log (Real.log R)) atTop (𝓝 1) := by
  let φ : TestFn := Analysis.Sobolev.unitMassTestFn
  have hφnonneg : ∀ y, 0 ≤ φ y := by
    intro y
    exact Analysis.Sobolev.unitMassTestFn_nonneg y
  have hφmass : ∫ y, φ y = 1 := Analysis.Sobolev.integral_unitMassTestFn
  have hK := hShrinkingVarianceInput ht φ hφnonneg hφmass (0 : Plane)
  have hInv0 : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero
  have hInvPos : ∀ᶠ R : ℝ in atTop, R⁻¹ ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact inv_pos.mpr hR
  have hInv : Tendsto (fun R : ℝ => R⁻¹) atTop (nhdsWithin 0 (Set.Ioi (0 : ℝ))) :=
    tendsto_nhdsWithin_iff.mpr ⟨hInv0, hInvPos⟩
  have hVar := hK.2.comp hInv
  have hMem : ∀ᶠ R : ℝ in atTop, MemLp (fun ω => H t 0 ω (φ.dilate R⁻¹ 0)) 2 P := by
    filter_upwards [hInv.eventually hK.1] with R hR
    exact hR
  have hEq : ∀ᶠ R : ℝ in atTop,
      (∫ ξ, ‖Spectral.fourierKPZ φ (R⁻¹ • ξ)‖ ^ 2 ∂ν) =
        Var[fun ω => H t 0 ω (φ.dilate R⁻¹ 0); P] := by
    filter_upwards [hMem, eventually_gt_atTop (0 : ℝ)] with R hR hRpos
    have henergy := integral_fourierEnergy_eq_variance_of P H t ν hν
      (φ.dilate R⁻¹ 0) hR
    have hFourier (ξ : Plane) :
        Spectral.fourierKPZ (φ.dilate R⁻¹ 0) ξ =
          Spectral.fourierKPZ φ (R⁻¹ • ξ) :=
      fourierKPZ_dilate_center φ (inv_pos.mpr hRpos) ξ
    calc
      (∫ ξ, ‖Spectral.fourierKPZ φ (R⁻¹ • ξ)‖ ^ 2 ∂ν) =
          ∫ ξ, ‖Spectral.fourierKPZ (φ.dilate R⁻¹ 0) ξ‖ ^ 2 ∂ν := by
            apply integral_congr_ae
            filter_upwards [] with ξ
            rw [← hFourier ξ]
      _ = Var[fun ω => H t 0 ω (φ.dilate R⁻¹ 0); P] := henergy
  have hVar' : Tendsto
      (fun R : ℝ => Var[fun ω => H t 0 ω (φ.dilate R⁻¹ 0); P] /
        Real.log (Real.log R)) atTop (𝓝 1) := by
    apply hVar.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
    simp
  apply hVar'.congr'
  filter_upwards [hEq] with R hR
  rw [hR]

/-- The spectral energy of the dilated unit-mass test is eventually integrable. -/
theorem eventually_integrable_unitMass_fourierEnergy_of {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr)
    (hShrinkingVarianceInput : SmallScales.ShrinkingVarianceAt P H) (t : ℝ) (ht : 0 < t)
    (ν : Measure Plane)
    (hν : ∀ f g : TestFn,
      cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P] =
        ∫ ξ, (Spectral.fourierKPZ f ξ * conj (Spectral.fourierKPZ g ξ)).re ∂ν) :
    ∀ᶠ R : ℝ in atTop,
      Integrable (fun ξ => ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn
        (R⁻¹ • ξ)‖ ^ 2) ν := by
  let φ : TestFn := Analysis.Sobolev.unitMassTestFn
  have hφnonneg : ∀ y, 0 ≤ φ y := fun y => Analysis.Sobolev.unitMassTestFn_nonneg y
  have hφmass : ∫ y, φ y = 1 := Analysis.Sobolev.integral_unitMassTestFn
  have hK := hShrinkingVarianceInput ht φ hφnonneg hφmass (0 : Plane)
  have hInv0 : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
  have hInvPos : ∀ᶠ R : ℝ in atTop, R⁻¹ ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact inv_pos.mpr hR
  have hInv : Tendsto (fun R : ℝ => R⁻¹) atTop (nhdsWithin 0 (Set.Ioi (0 : ℝ))) :=
    tendsto_nhdsWithin_iff.mpr ⟨hInv0, hInvPos⟩
  have hVar := hK.2.comp hInv
  have hMem : ∀ᶠ R : ℝ in atTop,
      MemLp (fun ω => H t 0 ω (φ.dilate R⁻¹ 0)) 2 P := by
    filter_upwards [hInv.eventually hK.1] with R hR
    exact hR
  have hEq : ∀ᶠ R : ℝ in atTop,
      (∫ ξ, ‖Spectral.fourierKPZ φ (R⁻¹ • ξ)‖ ^ 2 ∂ν) =
        Var[fun ω => H t 0 ω (φ.dilate R⁻¹ 0); P] := by
    filter_upwards [hMem, eventually_gt_atTop (0 : ℝ)] with R hR hRpos
    have henergy := integral_fourierEnergy_eq_variance_of P H t ν hν
      (φ.dilate R⁻¹ 0) hR
    have hFourier (ξ : Plane) :
        Spectral.fourierKPZ (φ.dilate R⁻¹ 0) ξ = Spectral.fourierKPZ φ (R⁻¹ • ξ) :=
      fourierKPZ_dilate_center φ (inv_pos.mpr hRpos) ξ
    calc
      (∫ ξ, ‖Spectral.fourierKPZ φ (R⁻¹ • ξ)‖ ^ 2 ∂ν) =
          ∫ ξ, ‖Spectral.fourierKPZ (φ.dilate R⁻¹ 0) ξ‖ ^ 2 ∂ν := by
            apply integral_congr_ae
            filter_upwards [] with ξ
            rw [← hFourier ξ]
      _ = Var[fun ω => H t 0 ω (φ.dilate R⁻¹ 0); P] := henergy
  have hVar' : Tendsto
      (fun R : ℝ => Var[fun ω => H t 0 ω (φ.dilate R⁻¹ 0); P] /
        Real.log (Real.log R)) atTop (𝓝 1) := by
    apply hVar.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
    simp
  have hVarPos : ∀ᶠ R : ℝ in atTop,
      0 < Var[fun ω => H t 0 ω (φ.dilate R⁻¹ 0); P] := by
    filter_upwards [hVar'.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
      eventually_gt_atTop (Real.exp (Real.exp 1))] with R hratio hR
    have hL : 0 < Real.log (Real.log R) := log_log_pos_of_exp_exp_one_lt hR
    have hratio0 : 0 <
        Var[fun ω => H t 0 ω (φ.dilate R⁻¹ 0); P] / Real.log (Real.log R) := by
      linarith
    have hmul : 0 <
        (Var[fun ω => H t 0 ω (φ.dilate R⁻¹ 0); P] / Real.log (Real.log R)) *
          Real.log (Real.log R) := mul_pos hratio0 hL
    have hcancel :
        (Var[fun ω => H t 0 ω (φ.dilate R⁻¹ 0); P] / Real.log (Real.log R)) *
          Real.log (Real.log R) = Var[fun ω => H t 0 ω (φ.dilate R⁻¹ 0); P] :=
      div_mul_cancel₀ _ hL.ne'
    rw [hcancel] at hmul
    exact hmul
  filter_upwards [hMem, hEq, hVarPos] with R hmem henergy hvar
  apply Integrable.of_integral_ne_zero
  rw [henergy]
  exact hvar.ne'

/-- A Fourier profile bounded below near zero controls the spectral mass of the matching ball.
The energy integrability premise is explicit because the real-valued integral is zero when its
integrand is not integrable. -/
private theorem ball_toReal_div_four_le_unitMassEnergy {ν : Measure Plane}
    [IsLocallyFiniteMeasure ν] {R c : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hlow : ∀ ξ : Plane, ‖ξ‖ ≤ c →
      (1 / 4 : ℝ) ≤ ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn ξ‖ ^ 2)
    (hInt : Integrable (fun ξ : Plane =>
      ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn ((R / c)⁻¹ • ξ)‖ ^ 2) ν) :
    (1 / 4 : ℝ) * (ν (Metric.closedBall (0 : Plane) R)).toReal ≤
      ∫ ξ, ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn
        ((R / c)⁻¹ • ξ)‖ ^ 2 ∂ν := by
  have hball := isCompact_closedBall (0 : Plane) R
  have hfinite : ν (Metric.closedBall (0 : Plane) R) ≠ ⊤ := hball.measure_ne_top
  have hmeas : MeasurableSet (Metric.closedBall (0 : Plane) R) := hball.measurableSet
  have hpoint : ∀ ξ ∈ Metric.closedBall (0 : Plane) R,
      (1 / 4 : ℝ) ≤ ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn
        ((R / c)⁻¹ • ξ)‖ ^ 2 := by
    intro ξ hξ
    have hnormξ : ‖ξ‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hξ
    have hscale : (R / c)⁻¹ = c / R := by
      field_simp
    have hnorm : ‖(R / c)⁻¹ • ξ‖ ≤ c := by
      rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hc hR)]
      calc
        c / R * ‖ξ‖ ≤ c / R * R := mul_le_mul_of_nonneg_left hnormξ (div_nonneg hc.le hR.le)
        _ = c := by field_simp
    exact hlow _ hnorm
  have hballLower := setIntegral_ge_of_const_le_real hmeas hfinite hpoint hInt.integrableOn
  have hwhole :
      (∫ ξ in Metric.closedBall (0 : Plane) R,
        ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn ((R / c)⁻¹ • ξ)‖ ^ 2 ∂ν) ≤
        ∫ ξ, ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn ((R / c)⁻¹ • ξ)‖ ^ 2 ∂ν :=
    setIntegral_le_integral (s := Metric.closedBall (0 : Plane) R) hInt
      (Filter.Eventually.of_forall (fun ξ => sq_nonneg _))
  calc
    (1 / 4 : ℝ) * (ν (Metric.closedBall (0 : Plane) R)).toReal ≤
        ∫ ξ in Metric.closedBall (0 : Plane) R,
          ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn ((R / c)⁻¹ • ξ)‖ ^ 2 ∂ν := by
            simpa [Measure.real] using hballLower
    _ ≤ ∫ ξ, ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn ((R / c)⁻¹ • ξ)‖ ^ 2 ∂ν := hwhole

/-- A Fourier profile lower bound on a neighborhood of zero gives a corresponding lower bound
on the spectral energy over the ball. Integrability is explicit. -/
private theorem ball_toReal_mul_le_unitMassEnergy {ν : Measure Plane}
    [IsLocallyFiniteMeasure ν] {R c d : ℝ} (hR : 0 < R) (hc : 0 < c)
    (hlow : ∀ ξ : Plane, ‖ξ‖ ≤ c →
      d ≤ ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn ξ‖ ^ 2)
    (hInt : Integrable (fun ξ : Plane =>
      ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn ((R / c)⁻¹ • ξ)‖ ^ 2) ν) :
    d * (ν (Metric.closedBall (0 : Plane) R)).toReal ≤
      ∫ ξ, ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn
        ((R / c)⁻¹ • ξ)‖ ^ 2 ∂ν := by
  have hball := isCompact_closedBall (0 : Plane) R
  have hfinite : ν (Metric.closedBall (0 : Plane) R) ≠ ⊤ := hball.measure_ne_top
  have hmeas : MeasurableSet (Metric.closedBall (0 : Plane) R) := hball.measurableSet
  have hpoint : ∀ ξ ∈ Metric.closedBall (0 : Plane) R,
      d ≤ ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn
        ((R / c)⁻¹ • ξ)‖ ^ 2 := by
    intro ξ hξ
    have hnormξ : ‖ξ‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hξ
    have hscale : (R / c)⁻¹ = c / R := by field_simp
    have hnorm : ‖(R / c)⁻¹ • ξ‖ ≤ c := by
      rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hc hR)]
      calc
        c / R * ‖ξ‖ ≤ c / R * R := mul_le_mul_of_nonneg_left hnormξ (div_nonneg hc.le hR.le)
        _ = c := by field_simp
    exact hlow _ hnorm
  have hballLower := setIntegral_ge_of_const_le_real hmeas hfinite hpoint hInt.integrableOn
  have hwhole :
      (∫ ξ in Metric.closedBall (0 : Plane) R,
        ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn ((R / c)⁻¹ • ξ)‖ ^ 2 ∂ν) ≤
        ∫ ξ, ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn ((R / c)⁻¹ • ξ)‖ ^ 2 ∂ν :=
    setIntegral_le_integral (s := Metric.closedBall (0 : Plane) R) hInt
      (Filter.Eventually.of_forall (fun ξ => sq_nonneg _))
  calc
    d * (ν (Metric.closedBall (0 : Plane) R)).toReal ≤
        ∫ ξ in Metric.closedBall (0 : Plane) R,
          ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn ((R / c)⁻¹ • ξ)‖ ^ 2 ∂ν := by
            simpa [Measure.real] using hballLower
    _ ≤ ∫ ξ, ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn
        ((R / c)⁻¹ • ξ)‖ ^ 2 ∂ν := hwhole

/-- Every radius above `R` lies in a dyadic annulus with lower endpoint at least `R`. -/
private theorem exists_dyadic_annulus {R r : ℝ} (hR : 0 < R) (hr : R < r) :
    ∃ n : ℕ, (2 : ℝ) ^ n * R ≤ r ∧ r ≤ (2 : ℝ) ^ (n + 1) * R := by
  have hx : 1 ≤ r / R := (le_div_iff₀ hR).2 (by simpa using hr.le)
  obtain ⟨n, hlow, hhigh⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
  refine ⟨n, ?_, ?_⟩
  · calc
      (2 : ℝ) ^ n * R ≤ (r / R) * R := mul_le_mul_of_nonneg_right hlow hR.le
      _ = r := div_mul_cancel₀ r hR.ne'
  · calc
      r = (r / R) * R := (div_mul_cancel₀ r hR.ne').symm
      _ ≤ (2 : ℝ) ^ (n + 1) * R := (mul_le_mul_of_nonneg_right hhigh.le hR.le)

/-- The linear dyadic index is dominated by the next power of two. -/
private theorem nat_add_two_le_two_pow (n : ℕ) : (n : ℝ) + 2 ≤ (2 : ℝ) ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      calc
        (↑(n + 1) : ℝ) + 2 = (n : ℝ) + 3 := by push_cast; ring
        _ ≤ 2 * ((n : ℝ) + 2) := by
          have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        _ ≤ 2 * (2 : ℝ) ^ (n + 1) := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 : ℝ) ^ ((n + 1) + 1) := by rw [pow_succ]; ring

/-- A dyadic radius changes `log log R` by at most its index plus one once `R` is large. -/
private theorem log_log_dyadic_le {R : ℝ} (hR : Real.exp (Real.exp 1) < R)
    (n : ℕ) :
    Real.log (Real.log ((2 : ℝ) ^ (n + 1) * R)) ≤
      Real.log (Real.log R) + (n : ℝ) + 1 := by
  have hRpos : 0 < R := by
    have h0 : 0 < Real.exp (Real.exp 1) := by positivity
    linarith
  have hlogR : Real.exp 1 < Real.log R := by
    have h := Real.log_lt_log (by positivity : 0 < Real.exp (Real.exp 1)) hR
    simpa using h
  have hlogR1 : 1 ≤ Real.log R := by
    have h1 : 1 < Real.exp 1 := by
      exact Real.one_lt_exp_iff.mpr (by norm_num)
    linarith
  have hn : 0 ≤ (n : ℝ) + 1 := by positivity
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hpowpos : 0 < (2 : ℝ) ^ (n + 1) := by positivity
  have hpowone : 1 ≤ (2 : ℝ) ^ (n + 1) := by
    have hpowgt : 1 < (2 : ℝ) ^ (n + 1) :=
      one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (by omega)
    exact hpowgt.le
  have hS : R < (2 : ℝ) ^ (n + 1) * R := by
    calc
      R = 1 * R := by ring
      _ < (2 : ℝ) ^ (n + 1) * R := mul_lt_mul_of_pos_right
        (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (by omega)) hRpos
  have hSpos : 0 < (2 : ℝ) ^ (n + 1) * R := mul_pos hpowpos hRpos
  have hlogSpos : 0 < Real.log ((2 : ℝ) ^ (n + 1) * R) := by
    have h := Real.log_lt_log hRpos hS
    have h0 : 0 < Real.log R := by linarith
    linarith
  have hlogS : Real.log ((2 : ℝ) ^ (n + 1) * R) ≤ Real.log R + (n : ℝ) + 1 := by
    rw [Real.log_mul hpowpos.ne' hRpos.ne', Real.log_pow]
    push_cast
    have hmulLog := mul_le_mul_of_nonneg_left hlog2 hn
    calc
      (↑n + 1) * Real.log 2 + Real.log R =
          Real.log R + (↑n + 1) * Real.log 2 := by ring
      _ ≤ Real.log R + (↑n + 1) * 1 := add_le_add_right hmulLog _
      _ = Real.log R + ↑n + 1 := by ring
  have hfactor : Real.log R + (n : ℝ) + 1 ≤ Real.log R * ((n : ℝ) + 2) := by
    have hmul := mul_le_mul_of_nonneg_right hlogR1 (by positivity : 0 ≤ (n : ℝ) + 1)
    calc
      Real.log R + (n : ℝ) + 1 ≤ Real.log R + Real.log R * ((n : ℝ) + 1) := by
        linarith only [hmul]
      _ = Real.log R * ((n : ℝ) + 2) := by ring
  have hleftpos : 0 < Real.log R + (n : ℝ) + 1 := by positivity
  have hrightpos : 0 < Real.log R * ((n : ℝ) + 2) := by positivity
  have hlogfactor := Real.log_le_log hleftpos hfactor
  rw [Real.log_mul (ne_of_gt (by linarith : 0 < Real.log R))
    (ne_of_gt (by positivity : 0 < (n : ℝ) + 2))] at hlogfactor
  have hlogn : Real.log ((n : ℝ) + 2) ≤ (n : ℝ) + 1 := by
    calc
      Real.log ((n : ℝ) + 2) ≤ ((n : ℝ) + 2) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      _ = (n : ℝ) + 1 := by ring
  calc
    Real.log (Real.log ((2 : ℝ) ^ (n + 1) * R)) ≤
        Real.log (Real.log R + (n : ℝ) + 1) := Real.log_le_log hlogSpos hlogS
    _ ≤ Real.log (Real.log R) + Real.log ((n : ℝ) + 2) := hlogfactor
    _ ≤ Real.log (Real.log R) + ((n : ℝ) + 1) := add_le_add_right hlogn _
    _ = Real.log (Real.log R) + (n : ℝ) + 1 := by ring

/-- The fixed unit-mass Fourier energy gives a coarse eventual logarithmic bound on ball mass.
This is used to control the tail when comparing the energy back to a ball. -/
private theorem eventually_ball_toReal_le_eight_logLog {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr)
    (hShrinkingVarianceInput : SmallScales.ShrinkingVarianceAt P H) {t : ℝ} (ht : 0 < t)
    (ν : Measure Plane) [IsLocallyFiniteMeasure ν]
    (hν : ∀ f g : TestFn,
      cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P] =
        ∫ ξ, (Spectral.fourierKPZ f ξ * conj (Spectral.fourierKPZ g ξ)).re ∂ν) :
    ∀ᶠ R : ℝ in atTop,
      (ν (Metric.closedBall (0 : Plane) R)).toReal ≤ 8 * Real.log (Real.log R) := by
  obtain ⟨c, hc, hlow⟩ := exists_unitMass_fourier_lower_near_zero
  let E : ℝ → ℝ := fun s =>
    ∫ ξ, ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn (s⁻¹ • ξ)‖ ^ 2 ∂ν
  have hE : Tendsto (fun s : ℝ => E s / Real.log (Real.log s)) atTop (𝓝 1) := by
    simpa only [E] using unitMass_fourierEnergy_tendsto_of P H hShrinkingVarianceInput t ht ν hν
  have hEscale := tendsto_scaled_energy_div_logLog hE c⁻¹ (inv_pos.mpr hc)
  have hEscale' : Tendsto (fun R : ℝ => E (R / c) / Real.log (Real.log R))
      atTop (𝓝 1) := by
    apply hEscale.congr'
    filter_upwards [] with R
    have harg : c⁻¹ * R = R / c := by
      rw [div_eq_mul_inv]
      ring
    exact congrArg (fun x : ℝ => x / Real.log (Real.log R)) (congrArg E harg)
  have hI : ∀ᶠ R : ℝ in atTop, Integrable
      (fun ξ : Plane => ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn
        ((R / c)⁻¹ • ξ)‖ ^ 2) ν := by
    have hscale : Tendsto (fun R : ℝ => R / c) atTop atTop :=
      (tendsto_div_const_atTop_of_pos hc).2 tendsto_id
    exact hscale.eventually
      (eventually_integrable_unitMass_fourierEnergy_of P H hShrinkingVarianceInput t ht ν hν)
  filter_upwards [hEscale'.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2)),
    hI, eventually_gt_atTop (Real.exp (Real.exp 1))] with R hEbound hInt hR
  have hL : 0 < Real.log (Real.log R) := log_log_pos_of_exp_exp_one_lt hR
  have hEupper : E (R / c) < 2 * Real.log (Real.log R) :=
    (div_lt_iff₀ hL).mp hEbound
  have hRpos : 0 < R := by
    have h0 : 0 < Real.exp (Real.exp 1) := by positivity
    linarith
  have hball := ball_toReal_div_four_le_unitMassEnergy hRpos hc hlow hInt
  dsimp [E] at hEupper hball
  have hmass :
      (ν (Metric.closedBall (0 : Plane) R)).toReal ≤ 8 * Real.log (Real.log R) := by
    linarith only [hball, hEupper]
  exact hmass

/-- Outside a ball, Fourier decay is majorized by a summable family of larger dyadic balls. -/
private theorem unitMass_energy_le_dyadic_ball_sum {R a C : ℝ} (hR : 0 < R)
    (ha : 1 ≤ a) (hC : 0 < C)
    (hdecay : ∀ ξ : Plane, 1 ≤ ‖ξ‖ →
      ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn ξ‖ ≤ C / ‖ξ‖ ^ 2)
    (ξ : Plane) (hξ : R < ‖ξ‖) :
    ENNReal.ofReal (‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn
        ((R / a)⁻¹ • ξ)‖ ^ 2) ≤
      (∑' n : ℕ,
        ENNReal.ofReal (C ^ 2 / (a ^ 4 * (16 : ℝ) ^ n)) *
          Set.indicator (Metric.closedBall (0 : Plane) ((2 : ℝ) ^ (n + 1) * R))
            (fun _ => (1 : ENNReal)) ξ) := by
  obtain ⟨n, hnlo, hnhi⟩ := exists_dyadic_annulus hR hξ
  have haPos : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hpow1 : 1 ≤ (2 : ℝ) ^ n :=
    one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hq : 1 ≤ a * (2 : ℝ) ^ n := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ a * (2 : ℝ) ^ n := mul_le_mul ha hpow1 (by norm_num) (by linarith)
  have hscale : (R / a)⁻¹ = a / R := by field_simp
  have huNorm : ‖(R / a)⁻¹ • ξ‖ = (a / R) * ‖ξ‖ := by
    rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos haPos hR)]
  have huLower : a * (2 : ℝ) ^ n ≤ ‖(R / a)⁻¹ • ξ‖ := by
    rw [huNorm]
    calc
      a * (2 : ℝ) ^ n = (a / R) * ((2 : ℝ) ^ n * R) := by field_simp
      _ ≤ (a / R) * ‖ξ‖ := mul_le_mul_of_nonneg_left hnlo (div_nonneg haPos.le hR.le)
  have huone : 1 ≤ ‖(R / a)⁻¹ • ξ‖ := hq.trans huLower
  have hF : ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn
      ((R / a)⁻¹ • ξ)‖ ≤ C / ‖(R / a)⁻¹ • ξ‖ ^ 2 := hdecay _ huone
  have hF0 : 0 ≤ ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn
      ((R / a)⁻¹ • ξ)‖ := norm_nonneg _
  have hFbound : ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn
      ((R / a)⁻¹ • ξ)‖ ^ 2 ≤
      C ^ 2 / ‖(R / a)⁻¹ • ξ‖ ^ 4 := by
    have hsq := (sq_le_sq₀ hF0 (div_nonneg hC.le (sq_nonneg _))).2 hF
    calc
      _ ≤ (C / ‖(R / a)⁻¹ • ξ‖ ^ 2) ^ 2 := hsq
      _ = C ^ 2 / ‖(R / a)⁻¹ • ξ‖ ^ 4 := by
        rw [div_pow]
        congr 1
        ring
  have hqpos : 0 < a * (2 : ℝ) ^ n := mul_pos haPos (by positivity)
  have hqpow : (a * (2 : ℝ) ^ n) ^ 4 ≤ ‖(R / a)⁻¹ • ξ‖ ^ 4 := by
    gcongr
  have hdiv : C ^ 2 / ‖(R / a)⁻¹ • ξ‖ ^ 4 ≤ C ^ 2 / (a * (2 : ℝ) ^ n) ^ 4 :=
    div_le_div_of_nonneg_left (sq_nonneg C) (pow_pos hqpos 4) hqpow
  have hpowid : ((2 : ℝ) ^ n) ^ 4 = (16 : ℝ) ^ n := by
    calc
      ((2 : ℝ) ^ n) ^ 4 = (2 : ℝ) ^ (n * 4) := by rw [pow_mul]
      _ = (2 : ℝ) ^ (4 * n) := by rw [Nat.mul_comm n 4]
      _ = ((2 : ℝ) ^ 4) ^ n := by rw [pow_mul]
      _ = (16 : ℝ) ^ n := by norm_num
  have hden : (a * (2 : ℝ) ^ n) ^ 4 = a ^ 4 * (16 : ℝ) ^ n := by
    rw [mul_pow, hpowid]
  have henergy :
      ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn ((R / a)⁻¹ • ξ)‖ ^ 2 ≤
        C ^ 2 / (a ^ 4 * (16 : ℝ) ^ n) := by
    calc
      _ ≤ C ^ 2 / ‖(R / a)⁻¹ • ξ‖ ^ 4 := hFbound
      _ ≤ C ^ 2 / (a * (2 : ℝ) ^ n) ^ 4 := hdiv
      _ = _ := by rw [hden]
  have hcoeff : 0 ≤ C ^ 2 / (a ^ 4 * (16 : ℝ) ^ n) := by positivity
  have hmass : 0 ≤ ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn
      ((R / a)⁻¹ • ξ)‖ ^ 2 := by positivity
  have hout : ξ ∈ (Metric.closedBall (0 : Plane) R)ᶜ := by
    rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right]
    exact not_le_of_gt hξ
  have hmem : ξ ∈ Metric.closedBall (0 : Plane) ((2 : ℝ) ^ (n + 1) * R) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hnhi
  have hterm :
      ENNReal.ofReal (C ^ 2 / (a ^ 4 * (16 : ℝ) ^ n)) *
        Set.indicator (Metric.closedBall (0 : Plane) ((2 : ℝ) ^ (n + 1) * R))
          (fun _ => (1 : ENNReal)) ξ =
      ENNReal.ofReal (C ^ 2 / (a ^ 4 * (16 : ℝ) ^ n)) := by
    simp [Set.indicator, hmem]
  calc
    _ = ENNReal.ofReal (‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn
          ((R / a)⁻¹ • ξ)‖ ^ 2) := rfl
    _ ≤ ENNReal.ofReal (C ^ 2 / (a ^ 4 * (16 : ℝ) ^ n)) :=
      ENNReal.ofReal_le_ofReal henergy
    _ = ENNReal.ofReal (C ^ 2 / (a ^ 4 * (16 : ℝ) ^ n)) *
        Set.indicator (Metric.closedBall (0 : Plane) ((2 : ℝ) ^ (n + 1) * R))
          (fun _ => (1 : ENNReal)) ξ := hterm.symm
    _ ≤ ∑' k : ℕ,
        ENNReal.ofReal (C ^ 2 / (a ^ 4 * (16 : ℝ) ^ k)) *
          Set.indicator (Metric.closedBall (0 : Plane) ((2 : ℝ) ^ (k + 1) * R))
            (fun _ => (1 : ENNReal)) ξ := by
              exact ENNReal.le_tsum (f := fun k : ℕ =>
                ENNReal.ofReal (C ^ 2 / (a ^ 4 * (16 : ℝ) ^ k)) *
                  Set.indicator (Metric.closedBall (0 : Plane) ((2 : ℝ) ^ (k + 1) * R))
                    (fun _ => (1 : ENNReal)) ξ) n

/-- The Fourier-energy tail outside a ball is controlled by the logarithmic growth of larger
balls. The integral is a nonnegative Lebesgue integral, so the inequality does not assume integrability. -/
private theorem unitMass_energy_tail_lintegral_le {ν : Measure Plane}
    [IsLocallyFiniteMeasure ν] {R a C : ℝ}
    (hR : Real.exp (Real.exp 1) < R) (ha : 1 ≤ a) (hC : 0 < C)
    (hdecay : ∀ ξ : Plane, 1 ≤ ‖ξ‖ →
      ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn ξ‖ ≤ C / ‖ξ‖ ^ 2)
    (hGrowth : ∀ s : ℝ, R ≤ s →
      (ν (Metric.closedBall (0 : Plane) s)).toReal ≤ 8 * Real.log (Real.log s)) :
    ∫⁻ ξ, (Metric.closedBall (0 : Plane) R)ᶜ.indicator
      (fun ξ => ENNReal.ofReal (‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn
        ((R / a)⁻¹ • ξ)‖ ^ 2)) ξ ∂ν ≤
      ENNReal.ofReal (32 * C ^ 2 / a ^ 4 * Real.log (Real.log R)) := by
  let coeff : ℕ → ENNReal := fun n =>
    ENNReal.ofReal (C ^ 2 / (a ^ 4 * (16 : ℝ) ^ n))
  let ballFn : ℕ → Plane → ENNReal := fun n ξ =>
    Set.indicator (Metric.closedBall (0 : Plane) ((2 : ℝ) ^ (n + 1) * R))
      (fun _ => (1 : ENNReal)) ξ
  let majorant : ℕ → Plane → ENNReal := fun n ξ => coeff n * ballFn n ξ
  have hRpos : 0 < R := by
    have h0 : 0 < Real.exp (Real.exp 1) := by positivity
    linarith
  have hL : 1 < Real.log (Real.log R) := by
    have hlog : Real.exp 1 < Real.log R := by
      have h := Real.log_lt_log (by positivity : (0 : ℝ) < Real.exp (Real.exp 1)) hR
      simpa using h
    have hloglog : Real.log (Real.exp 1) < Real.log (Real.log R) :=
      Real.log_lt_log (by positivity) hlog
    simpa using hloglog
  have hLpos : 0 < Real.log (Real.log R) := by linarith
  have hcoeff (n : ℕ) : 0 ≤ C ^ 2 / (a ^ 4 * (16 : ℝ) ^ n) := by positivity
  have hcoeffNe (n : ℕ) : coeff n ≠ ⊤ := by
    change ENNReal.ofReal (C ^ 2 / (a ^ 4 * (16 : ℝ) ^ n)) ≠ ⊤
    exact ENNReal.ofReal_ne_top
  have hballMeas (n : ℕ) :
      MeasurableSet (Metric.closedBall (0 : Plane) ((2 : ℝ) ^ (n + 1) * R)) :=
    (isCompact_closedBall (0 : Plane) _).measurableSet
  have hmajorMeas (n : ℕ) : Measurable (majorant n) := by
    simp only [majorant, ballFn]
    exact measurable_const.mul (measurable_const.indicator (hballMeas n))
  have hmajorAEMeas (n : ℕ) : AEMeasurable (majorant n) ν := (hmajorMeas n).aemeasurable
  have hpoint (ξ : Plane) :
      (Metric.closedBall (0 : Plane) R)ᶜ.indicator
          (fun ξ => ENNReal.ofReal (‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn
            ((R / a)⁻¹ • ξ)‖ ^ 2)) ξ ≤ ∑' n : ℕ, majorant n ξ := by
    by_cases hξ : ξ ∈ (Metric.closedBall (0 : Plane) R)ᶜ
    · have hnorm : R < ‖ξ‖ := by
        rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right] at hξ
        exact lt_of_not_ge hξ
      have hsum := unitMass_energy_le_dyadic_ball_sum hRpos ha hC hdecay ξ hnorm
      simpa [Set.indicator, hξ, majorant, ballFn, coeff] using hsum
    · simp [Set.indicator, hξ]
  have hlin :
      ∫⁻ ξ, (Metric.closedBall (0 : Plane) R)ᶜ.indicator
        (fun ξ => ENNReal.ofReal (‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn
          ((R / a)⁻¹ • ξ)‖ ^ 2)) ξ ∂ν ≤
        ∫⁻ ξ, ∑' n : ℕ, majorant n ξ ∂ν := by
    exact lintegral_mono hpoint
  have htsumIntegral :
      ∫⁻ ξ, ∑' n : ℕ, majorant n ξ ∂ν = ∑' n : ℕ, ∫⁻ ξ, majorant n ξ ∂ν :=
    lintegral_tsum hmajorAEMeas
  have hterm (n : ℕ) :
      ∫⁻ ξ, majorant n ξ ∂ν ≤
        ENNReal.ofReal (16 * C ^ 2 / a ^ 4 * Real.log (Real.log R)) *
          ((1 / 2 : ENNReal) ^ n) := by
    let s : ℝ := (2 : ℝ) ^ (n + 1) * R
    have hsR : R ≤ s := by
      dsimp [s]
      have hp : 1 ≤ (2 : ℝ) ^ (n + 1) :=
        one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      calc
        R = 1 * R := by ring
        _ ≤ (2 : ℝ) ^ (n + 1) * R := mul_le_mul_of_nonneg_right hp hRpos.le
    have hsGrowth := hGrowth s hsR
    have hsLog := log_log_dyadic_le hR n
    have hmass :
        (ν (Metric.closedBall (0 : Plane) s)).toReal ≤
          8 * Real.log (Real.log R) * ((n : ℝ) + 2) := by
      dsimp [s] at hsGrowth
      have hstep : Real.log (Real.log s) ≤ Real.log (Real.log R) + (n : ℝ) + 1 := by
        simpa [s] using hsLog
      have hmul := mul_le_mul_of_nonneg_left hstep (by norm_num : (0 : ℝ) ≤ 8)
      have hmain : Real.log (Real.log R) + (n : ℝ) + 1 ≤
          Real.log (Real.log R) * ((n : ℝ) + 2) := by
        have hn : 0 ≤ (n : ℝ) + 1 := by positivity
        have hmul' := mul_le_mul_of_nonneg_right (le_of_lt hL) hn
        nlinarith
      calc
        (ν (Metric.closedBall (0 : Plane) s)).toReal ≤ 8 * Real.log (Real.log s) := hsGrowth
        _ ≤ 8 * (Real.log (Real.log R) + (n : ℝ) + 1) := by nlinarith
        _ ≤ _ := by nlinarith
    have hsfinite : ν (Metric.closedBall (0 : Plane) s) ≠ ⊤ :=
      (isCompact_closedBall (0 : Plane) s).measure_ne_top
    have hmassNonneg : 0 ≤ (ν (Metric.closedBall (0 : Plane) s)).toReal := ENNReal.toReal_nonneg
    have hcoeffReal : 0 ≤ C ^ 2 / (a ^ 4 * (16 : ℝ) ^ n) := hcoeff n
    have hrealBound :
        C ^ 2 / (a ^ 4 * (16 : ℝ) ^ n) * (ν (Metric.closedBall (0 : Plane) s)).toReal ≤
          (16 * C ^ 2 / a ^ 4 * Real.log (Real.log R)) * (1 / 2 : ℝ) ^ n := by
      have hnPow : (n : ℝ) + 2 ≤ (2 : ℝ) ^ (n + 1) := nat_add_two_le_two_pow n
      have hthree : (1 / 8 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ n :=
        pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 8)
          (by norm_num : (1 / 8 : ℝ) ≤ 1 / 2) n
      have hcoefRewrite :
          C ^ 2 / (a ^ 4 * (16 : ℝ) ^ n) *
              (8 * Real.log (Real.log R) * ((n : ℝ) + 2)) ≤
            (16 * C ^ 2 / a ^ 4 * Real.log (Real.log R)) * (1 / 8 : ℝ) ^ n := by
        have hp16 : (16 : ℝ) ^ n = 16 ^ n := rfl
        have h16n : (16 : ℝ) ^ n = (8 : ℝ) ^ n * (2 : ℝ) ^ n := by
          rw [← mul_pow]
          norm_num
        have hpowpos : 0 < (8 : ℝ) ^ n := by positivity
        have hmulBound := mul_le_mul_of_nonneg_left hnPow
          (by positivity : (0 : ℝ) ≤ 8 * Real.log (Real.log R))
        rw [h16n]
        have hstep :
            C ^ 2 / (a ^ 4 * ((8 : ℝ) ^ n * (2 : ℝ) ^ n)) *
                (8 * Real.log (Real.log R) * ((n : ℝ) + 2)) ≤
              C ^ 2 / (a ^ 4 * ((8 : ℝ) ^ n * (2 : ℝ) ^ n)) *
                (8 * Real.log (Real.log R) * (2 : ℝ) ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left hmulBound (div_nonneg (sq_nonneg C) (by positivity))
        have hcalc :
            C ^ 2 / (a ^ 4 * ((8 : ℝ) ^ n * (2 : ℝ) ^ n)) *
                (8 * Real.log (Real.log R) * (2 : ℝ) ^ (n + 1)) =
              (16 * C ^ 2 / a ^ 4 * Real.log (Real.log R)) * (1 / 8 : ℝ) ^ n := by
          rw [pow_succ, div_pow]
          field_simp
          ring_nf
        exact hstep.trans_eq hcalc
      have hmassMul := mul_le_mul_of_nonneg_left hmass hcoeffReal
      calc
        _ ≤ C ^ 2 / (a ^ 4 * (16 : ℝ) ^ n) *
              (8 * Real.log (Real.log R) * ((n : ℝ) + 2)) := hmassMul
        _ ≤ (16 * C ^ 2 / a ^ 4 * Real.log (Real.log R)) * (1 / 8 : ℝ) ^ n :=
          hcoefRewrite
        _ ≤ _ := mul_le_mul_of_nonneg_left hthree (by positivity)
    have hmassIntegral :
        ∫⁻ ξ, majorant n ξ ∂ν = coeff n * ν (Metric.closedBall (0 : Plane) s) := by
      dsimp [majorant, coeff, ballFn, s]
      rw [lintegral_const_mul' _ _ (hcoeffNe n),
        lintegral_indicator_const (isCompact_closedBall (0 : Plane) _).measurableSet]
      simp only [one_mul]
      change ENNReal.ofReal (C ^ 2 / (a ^ 4 * (16 : ℝ) ^ n)) *
        ν (Metric.closedBall (0 : Plane) ((2 : ℝ) ^ (n + 1) * R)) = _
      rfl
    rw [hmassIntegral]
    rw [← ENNReal.ofReal_toReal hsfinite, ← ENNReal.ofReal_mul hcoeffReal]
    have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2⁻¹ : ENNReal) := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    have hqcast : ((1 / 2 : ENNReal) ^ n) = ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
      rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2), hhalf]
      simp [one_div]
    rw [hqcast, ← ENNReal.ofReal_mul (by positivity :
      0 ≤ 16 * C ^ 2 / a ^ 4 * Real.log (Real.log R))]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (16 * C ^ 2 / a ^ 4 * Real.log (Real.log R)) * (1 / 2 : ℝ) ^ n := by
        exact hrealBound
      _ ≤ _ := by
        exact le_rfl
  have hsumBound :
      (∑' n : ℕ, ∫⁻ ξ, majorant n ξ ∂ν) ≤
        ENNReal.ofReal (16 * C ^ 2 / a ^ 4 * Real.log (Real.log R)) * 2 := by
    calc
      _ ≤ ∑' n : ℕ,
          ENNReal.ofReal (16 * C ^ 2 / a ^ 4 * Real.log (Real.log R)) *
            ((1 / 2 : ENNReal) ^ n) := ENNReal.tsum_le_tsum hterm
      _ = _ := by
        rw [ENNReal.tsum_mul_left]
        have hseries : ∑' n : ℕ, ((1 / 2 : ENNReal) ^ n) = 2 := by
          simp [one_div]
        rw [hseries]
  calc
    _ ≤ ∫⁻ ξ, ∑' n : ℕ, majorant n ξ ∂ν := hlin
    _ = ∑' n : ℕ, ∫⁻ ξ, majorant n ξ ∂ν := htsumIntegral
    _ ≤ ENNReal.ofReal (16 * C ^ 2 / a ^ 4 * Real.log (Real.log R)) * 2 := hsumBound
    _ = ENNReal.ofReal (32 * C ^ 2 / a ^ 4 * Real.log (Real.log R)) := by
      have h2 : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_num
      rw [h2, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 16 * C ^ 2 / a ^ 4 * Real.log (Real.log R))]
      congr 1
      ring

/-- The integrable exterior Fourier energy is bounded by a constant times a⁻⁴ log(log R). -/
private theorem unitMass_energy_tail_integral_le {ν : Measure Plane}
    [IsLocallyFiniteMeasure ν] {R a C : ℝ}
    (hR : Real.exp (Real.exp 1) < R) (ha : 1 ≤ a) (hC : 0 < C)
    (hdecay : ∀ ξ : Plane, 1 ≤ ‖ξ‖ →
      ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn ξ‖ ≤ C / ‖ξ‖ ^ 2)
    (hGrowth : ∀ s : ℝ, R ≤ s →
      (ν (Metric.closedBall (0 : Plane) s)).toReal ≤ 8 * Real.log (Real.log s))
    (hInt : Integrable (fun ξ : Plane =>
      ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn ((R / a)⁻¹ • ξ)‖ ^ 2) ν) :
    ∫ ξ in (Metric.closedBall (0 : Plane) R)ᶜ,
      ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn ((R / a)⁻¹ • ξ)‖ ^ 2 ∂ν ≤
      32 * C ^ 2 / a ^ 4 * Real.log (Real.log R) := by
  let f : Plane → ℝ := fun ξ =>
    ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn ((R / a)⁻¹ • ξ)‖ ^ 2
  let s : Set Plane := (Metric.closedBall (0 : Plane) R)ᶜ
  have hs : MeasurableSet s := (isCompact_closedBall (0 : Plane) R).measurableSet.compl
  have hfi : Integrable (fun ξ => s.indicator f ξ) ν := hInt.indicator hs
  have hnonneg : ∀ᵐ ξ ∂ν, 0 ≤ s.indicator f ξ := by
    filter_upwards [] with ξ
    by_cases hξ : ξ ∈ s
    · simp [Set.indicator, hξ, f]
    · simp [Set.indicator, hξ]
  have hlin := ofReal_integral_eq_lintegral_ofReal hfi hnonneg
  have hset : (∫ ξ, s.indicator f ξ ∂ν) =
      ∫ ξ in (Metric.closedBall (0 : Plane) R)ᶜ, f ξ ∂ν := by
    exact integral_indicator hs
  have hlinEq :
      (∫⁻ ξ, ENNReal.ofReal (s.indicator f ξ) ∂ν) =
        ∫⁻ ξ, (Metric.closedBall (0 : Plane) R)ᶜ.indicator (fun ξ => ENNReal.ofReal (f ξ)) ξ ∂ν := by
    apply lintegral_congr_ae
    filter_upwards [] with ξ
    by_cases hξ : ξ ∈ s
    · simp [s, f, Set.indicator, hξ]
    · simp [s, Set.indicator, hξ]
  have htail := unitMass_energy_tail_lintegral_le hR ha hC hdecay hGrowth
  have hbound : ENNReal.ofReal (∫ ξ in (Metric.closedBall (0 : Plane) R)ᶜ, f ξ ∂ν) ≤
      ENNReal.ofReal (32 * C ^ 2 / a ^ 4 * Real.log (Real.log R)) := by
    calc
      _ = ∫⁻ ξ, ENNReal.ofReal (s.indicator f ξ) ∂ν := by rw [← hset, ← hlin]
      _ = ∫⁻ ξ, (Metric.closedBall (0 : Plane) R)ᶜ.indicator
          (fun ξ => ENNReal.ofReal (f ξ)) ξ ∂ν := hlinEq
      _ ≤ _ := htail
  have hL : 0 < Real.log (Real.log R) := log_log_pos_of_exp_exp_one_lt hR
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity :
    0 ≤ 32 * C ^ 2 / a ^ 4 * Real.log (Real.log R))).mp hbound

/-- The normalized spectral ball mass is eventually below any number strictly larger than one. -/
private theorem eventually_unitMass_ball_ratio_lt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr)
    (hShrinkingVarianceInput : SmallScales.ShrinkingVarianceAt P H) (t : ℝ) (ht : 0 < t)
    (ν : Measure Plane) [IsLocallyFiniteMeasure ν]
    (hν : ∀ f g : TestFn,
      cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P] =
        ∫ ξ, (Spectral.fourierKPZ f ξ * conj (Spectral.fourierKPZ g ξ)).re ∂ν)
    {b : ℝ} (hb : 1 < b) :
    ∀ᶠ R : ℝ in atTop,
      (ν (Metric.closedBall (0 : Plane) R)).toReal / Real.log (Real.log R) < b := by
  let E : ℝ → ℝ := fun s =>
    ∫ ξ, ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn (s⁻¹ • ξ)‖ ^ 2 ∂ν
  let M : ℝ → ℝ := fun s => (ν (Metric.closedBall (0 : Plane) s)).toReal
  let η : ℝ := (b - 1) / (4 * b)
  let d : ℝ := (1 - η) ^ 2
  have hbpos : 0 < b := lt_trans zero_lt_one hb
  have hηpos : 0 < η := by dsimp [η]; positivity
  have hηlt : η < 1 := by
    dsimp [η]
    rw [div_lt_one (by positivity : 0 < 4 * b)]
    nlinarith
  have hdpos : 0 < d := by
    dsimp [d]
    exact sq_pos_of_pos (by linarith)
  have hfac : 0 < (b - 1) * (9 * b - 1) :=
    mul_pos (by linarith) (by nlinarith)
  have hdbcalc : d * b - 1 = ((b - 1) * (9 * b - 1)) / (16 * b) := by
    dsimp [d, η]
    field_simp
    ring
  have hdb : 1 < d * b := by
    have hden : 0 < 16 * b := by positivity
    have hpos : 0 < ((b - 1) * (9 * b - 1)) / (16 * b) := div_pos hfac hden
    linarith [hdbcalc]
  have hE : Tendsto (fun s : ℝ => E s / Real.log (Real.log s)) atTop (𝓝 1) := by
    simpa only [E] using unitMass_fourierEnergy_tendsto_of P H hShrinkingVarianceInput t ht ν hν
  obtain ⟨c, hc, hlow⟩ := exists_unitMass_fourier_lower_near_zero_of η hηpos hηlt
  have hEscale := tendsto_scaled_energy_div_logLog hE c⁻¹ (inv_pos.mpr hc)
  have hEscale' : Tendsto (fun R : ℝ => E (R / c) / Real.log (Real.log R))
      atTop (𝓝 1) := by
    apply hEscale.congr'
    filter_upwards [] with R
    have harg : c⁻¹ * R = R / c := by rw [div_eq_mul_inv]; ring
    exact congrArg (fun x : ℝ => x / Real.log (Real.log R)) (congrArg E harg)
  have hI : ∀ᶠ R : ℝ in atTop,
      Integrable (fun ξ : Plane => ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn
        ((R / c)⁻¹ • ξ)‖ ^ 2) ν := by
    have hscale : Tendsto (fun R : ℝ => R / c) atTop atTop :=
      (tendsto_div_const_atTop_of_pos hc).2 tendsto_id
    exact hscale.eventually
      (eventually_integrable_unitMass_fourierEnergy_of P H hShrinkingVarianceInput t ht ν hν)
  filter_upwards [hEscale'.eventually (Iio_mem_nhds hdb), hI,
    eventually_gt_atTop (Real.exp (Real.exp 1))] with R hEr hInt hR
  have hL : 0 < Real.log (Real.log R) := log_log_pos_of_exp_exp_one_lt hR
  have hEupper : E (R / c) / Real.log (Real.log R) < d * b := hEr
  have hRpos : 0 < R := by
    have h0 : 0 < Real.exp (Real.exp 1) := by positivity
    linarith
  have hball := ball_toReal_mul_le_unitMassEnergy (ν := ν)
    hRpos hc (d := d) hlow hInt
  have hscaled : d * (M R / Real.log (Real.log R)) ≤
      E (R / c) / Real.log (Real.log R) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hball hL.le
  have hmul : d * (M R / Real.log (Real.log R)) < d * b :=
    hscaled.trans_lt hEupper
  have hratio : M R / Real.log (Real.log R) < b := lt_of_mul_lt_mul_left hmul hdpos.le
  simpa only [M] using hratio

/-- The normalized spectral ball mass is eventually above any number strictly below one. -/
private theorem eventually_unitMass_ball_ratio_gt {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr)
    (hShrinkingVarianceInput : SmallScales.ShrinkingVarianceAt P H) (t : ℝ) (ht : 0 < t)
    (ν : Measure Plane) [IsLocallyFiniteMeasure ν]
    (hν : ∀ f g : TestFn,
      cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P] =
        ∫ ξ, (Spectral.fourierKPZ f ξ * conj (Spectral.fourierKPZ g ξ)).re ∂ν)
    {a₀ : ℝ} (ha₀ : a₀ < 1) :
    ∀ᶠ R : ℝ in atTop,
      a₀ < (ν (Metric.closedBall (0 : Plane) R)).toReal / Real.log (Real.log R) := by
  let E : ℝ → ℝ := fun s =>
    ∫ ξ, ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn (s⁻¹ • ξ)‖ ^ 2 ∂ν
  let M : ℝ → ℝ := fun s => (ν (Metric.closedBall (0 : Plane) s)).toReal
  let q : ℝ := 1 - a₀
  have hq : 0 < q := by dsimp [q]; linarith
  have hE : Tendsto (fun s : ℝ => E s / Real.log (Real.log s)) atTop (𝓝 1) := by
    simpa only [E] using unitMass_fourierEnergy_tendsto_of P H hShrinkingVarianceInput t ht ν hν
  obtain ⟨C, hC, hdecay⟩ :=
    exists_fourierKPZ_quadratic_decay Analysis.Sobolev.unitMassTestFn
  let A : ℝ := max 1 (128 * C ^ 2 / q)
  have hA1 : 1 ≤ A := le_max_left _ _
  have hAquot : 128 * C ^ 2 / q ≤ A := le_max_right _ _
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hA4 : A ≤ A ^ 4 := by
    calc
      A = A * 1 := by ring
      _ ≤ A * A ^ 3 := mul_le_mul_of_nonneg_left
        (one_le_pow₀ hA1) hApos.le
      _ = A ^ 4 := by ring
  have hδ : 32 * C ^ 2 / A ^ 4 ≤ q / 4 := by
    calc
      32 * C ^ 2 / A ^ 4 ≤ 32 * C ^ 2 / A :=
        div_le_div_of_nonneg_left (by positivity) hApos hA4
      _ ≤ q / 4 := by
        apply (div_le_iff₀ hApos).2
        have hAraw : 128 * C ^ 2 ≤ A * q := (div_le_iff₀ hq).mp hAquot
        nlinarith
  have hEscale := tendsto_scaled_energy_div_logLog hE A⁻¹ (inv_pos.mpr hApos)
  have hEscale' : Tendsto (fun R : ℝ => E (R / A) / Real.log (Real.log R))
      atTop (𝓝 1) := by
    apply hEscale.congr'
    filter_upwards [] with R
    have harg : A⁻¹ * R = R / A := by rw [div_eq_mul_inv]; ring
    exact congrArg (fun x : ℝ => x / Real.log (Real.log R)) (congrArg E harg)
  have hI : ∀ᶠ R : ℝ in atTop,
      Integrable (fun ξ : Plane => ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn
        ((R / A)⁻¹ • ξ)‖ ^ 2) ν := by
    have hscale : Tendsto (fun R : ℝ => R / A) atTop atTop :=
      (tendsto_div_const_atTop_of_pos hApos).2 tendsto_id
    exact hscale.eventually
      (eventually_integrable_unitMass_fourierEnergy_of P H hShrinkingVarianceInput t ht ν hν)
  have hmassEvent := eventually_ball_toReal_le_eight_logLog P H hShrinkingVarianceInput ht ν hν
  obtain ⟨R₀, hmassAfter⟩ := eventually_atTop.1 hmassEvent
  have hqthreshold : 1 - q / 4 < 1 := by linarith
  filter_upwards [hEscale'.eventually (Ioi_mem_nhds hqthreshold),
    hI, eventually_ge_atTop R₀, eventually_gt_atTop (Real.exp (Real.exp 1))]
      with R hEr hInt hR₀ hR
  have hL : 0 < Real.log (Real.log R) := log_log_pos_of_exp_exp_one_lt hR
  have hRpos : 0 < R := by
    have h0 : 0 < Real.exp (Real.exp 1) := by positivity
    linarith
  have hGrowth : ∀ s : ℝ, R ≤ s →
      (ν (Metric.closedBall (0 : Plane) s)).toReal ≤ 8 * Real.log (Real.log s) := by
    intro s hs
    exact hmassAfter s (le_trans hR₀ hs)
  have hFourierNorm (ξ : Plane) :
      ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn
        ((R / A)⁻¹ • ξ)‖ ≤ 1 := by
    have hL1 : ∫ x : Plane, ‖Analysis.Sobolev.unitMassTestFn x‖ = 1 := by
      calc
        _ = ∫ x : Plane, Analysis.Sobolev.unitMassTestFn x := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [Real.norm_eq_abs, abs_of_nonneg (Analysis.Sobolev.unitMassTestFn_nonneg x)]
        _ = 1 := Analysis.Sobolev.integral_unitMassTestFn
    exact (Spectral.norm_fourierKPZ_le Analysis.Sobolev.unitMassTestFn
      ((R / A)⁻¹ • ξ)).trans_eq hL1
  have hEnergyPoint (ξ : Plane) :
      ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn
        ((R / A)⁻¹ • ξ)‖ ^ 2 ≤ 1 :=
    by simpa using (sq_le_sq₀ (norm_nonneg _) (by norm_num)).2 (hFourierNorm ξ)
  have hball := isCompact_closedBall (0 : Plane) R
  have hballFinite : ν (Metric.closedBall (0 : Plane) R) ≠ ⊤ := hball.measure_ne_top
  have hballIntegrableOne : IntegrableOn (fun _ : Plane => (1 : ℝ))
      (Metric.closedBall (0 : Plane) R) ν := integrableOn_const hballFinite
  have hinside :
      ∫ ξ in Metric.closedBall (0 : Plane) R,
        ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn
          ((R / A)⁻¹ • ξ)‖ ^ 2 ∂ν ≤ M R := by
    calc
      _ ≤ ∫ ξ in Metric.closedBall (0 : Plane) R, (1 : ℝ) ∂ν :=
        setIntegral_mono_on hInt.integrableOn hballIntegrableOne hball.measurableSet
          (fun ξ _ => hEnergyPoint ξ)
      _ = M R := by simp [M, Measure.real]
  have htail := unitMass_energy_tail_integral_le hR hA1 hC hdecay hGrowth hInt
  let δ : ℝ := 32 * C ^ 2 / A ^ 4
  have hδ' : δ ≤ q / 4 := by simpa [δ] using hδ
  have hsplit : E (R / A) =
      (∫ ξ in Metric.closedBall (0 : Plane) R,
        ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn
          ((R / A)⁻¹ • ξ)‖ ^ 2 ∂ν) +
      (∫ ξ in (Metric.closedBall (0 : Plane) R)ᶜ,
        ‖Spectral.fourierKPZ Analysis.Sobolev.unitMassTestFn
          ((R / A)⁻¹ • ξ)‖ ^ 2 ∂ν) := by
    dsimp [E]
    exact (integral_add_compl hball.measurableSet hInt).symm
  have hEupper : E (R / A) ≤ M R + δ * Real.log (Real.log R) := by
    rw [hsplit]
    exact add_le_add hinside (by simpa [δ] using htail)
  have hEratioLower : 1 - q / 4 < E (R / A) / Real.log (Real.log R) := hEr
  have hMratioLower : E (R / A) / Real.log (Real.log R) ≤
      M R / Real.log (Real.log R) + δ := by
    have hdiv := div_le_div_of_nonneg_right hEupper hL.le
    have hEq : (M R + δ * Real.log (Real.log R)) / Real.log (Real.log R) =
        M R / Real.log (Real.log R) + δ := by field_simp [hL.ne']
    rw [hEq] at hdiv
    exact hdiv
  have hfinal : a₀ < M R / Real.log (Real.log R) := by
    dsimp [q] at hδ' hEratioLower hq
    linarith
  simpa only [M] using hfinal

/-- The spectral mass of large balls grows with the same double-logarithmic asymptotic as the
shrinking variance. -/
theorem kpz_spectralMeasure_ball_asymp_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (_hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (_hH : IsCriticalKPZ P Z H)
    (hShrinkingVarianceInput : SmallScales.ShrinkingVarianceAt P H) {t : ℝ} (ht : 0 < t)
    (ν : Measure Plane) [IsLocallyFiniteMeasure ν]
    (hν : ∀ f g : TestFn, cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P] =
      ∫ ξ, (Spectral.fourierKPZ f ξ * conj (Spectral.fourierKPZ g ξ)).re ∂ν) :
    Tendsto (fun R => (ν (Metric.closedBall 0 R)).toReal / Real.log (Real.log R)) atTop (𝓝 1) := by
  let M : ℝ → ℝ := fun R => (ν (Metric.closedBall (0 : Plane) R)).toReal
  have hlim : Tendsto (fun R : ℝ => M R / Real.log (Real.log R)) atTop (𝓝 1) := by
    apply tendsto_order.2
    constructor
    · intro a ha
      exact eventually_unitMass_ball_ratio_gt P H hShrinkingVarianceInput t ht ν hν ha
    · intro b hb
      exact eventually_unitMass_ball_ratio_lt P H hShrinkingVarianceInput t ht ν hν hb
  simpa only [M] using hlim
end Critical2DKPZ.CovarianceKernel

end
