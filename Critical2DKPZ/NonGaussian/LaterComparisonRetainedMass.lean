/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.LaterComparisonProbability
import Critical2DKPZ.SmallScales.GaussianJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic

/-! # Positive mass after retaining ratios bounded away from zero -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.NonGaussian

universe u

/-- A conditional ratio bound survives retaining only samples where the normalizing ratio is at
least `a`; the loss is at most the deterministic factor `a⁻¹`. -/
theorem condExp_retained_ratio_le_of {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (m : MeasurableSpace Ω) (a c : ℝ)
    (W Y V : Ω → ℝ) (ha : 0 < a)
    (hWint : Integrable W P) (hYint : Integrable Y P)
    (hWle : W ≤ᵐ[P] fun ω => Y ω / a)
    (hcond : P[Y | m] ≤ᵐ[P] fun ω => c * V ω) :
    P[W | m] ≤ᵐ[P] fun ω => (c / a) * V ω := by
  have hWle' : W ≤ᵐ[P] a⁻¹ • Y := by
    filter_upwards [hWle] with ω hω
    simpa [div_eq_mul_inv, smul_eq_mul, mul_comm] using hω
  have hYscaledInt : Integrable (a⁻¹ • Y) P := hYint.smul a⁻¹
  have hmono := condExp_mono (m := m) hWint hYscaledInt hWle'
  have hscale := condExp_smul (μ := P) (c := a⁻¹) Y m
  filter_upwards [hmono, hscale, hcond] with ω hωmono hωscale hωcond
  calc
    P[W | m] ω ≤ P[a⁻¹ • Y | m] ω := hωmono
    _ = a⁻¹ * P[Y | m] ω := by simpa [smul_eq_mul] using hωscale
    _ ≤ a⁻¹ * (c * V ω) :=
      mul_le_mul_of_nonneg_left hωcond (inv_nonneg.mpr ha.le)
    _ = (c / a) * V ω := by ring


/-- A positive variable bounded by one retains positive expected mass above a positive threshold of a mean-at-most-one variable when both logarithmic means have lower bounds. -/
theorem retained_mass_lower_of_log_bounds {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (R X : Ω → ℝ) (C D : ℝ)
    (hC : 0 ≤ C)
    (hRmeas : Measurable R) (hRpos : ∀ᵐ ω ∂P, 0 < R ω)
    (hRint : Integrable R P) (hRmean : ∫ ω, R ω ∂P ≤ 1)
    (hRlog : Integrable (fun ω => Real.log (R ω)) P)
    (hRlogmean : -C ≤ ∫ ω, Real.log (R ω) ∂P)
    (hXpos : ∀ᵐ ω ∂P, 0 < X ω) (hXle : X ≤ᵐ[P] fun _ => 1)
    (hXint : Integrable X P)
    (hXlog : Integrable (fun ω => Real.log (X ω)) P)
    (hXlogmean : -D ≤ ∫ ω, Real.log (X ω) ∂P) :
    let a : ℝ := Real.exp (-(2 * (1 + C) * Real.exp D))
    let c : ℝ := Real.exp (-D) - (1 + C) / (2 * (1 + C) * Real.exp D)
    0 < a ∧ a < 1 ∧ 0 < c ∧
      Integrable (fun ω => Set.indicator {ω | a ≤ R ω} X ω) P ∧
      c ≤ ∫ ω, Set.indicator {ω | a ≤ R ω} X ω ∂P := by
  have hExpAE : (fun ω => Real.exp (Real.log (X ω))) =ᵐ[P] X := by
    filter_upwards [hXpos] with ω hω
    exact Real.exp_log hω
  have hExpInt : Integrable (fun ω => Real.exp (Real.log (X ω))) P :=
    hXint.congr hExpAE.symm
  have hJ := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hXlog hExpInt
  have hExp : ∫ ω, Real.exp (Real.log (X ω)) ∂P = ∫ ω, X ω ∂P :=
    integral_congr_ae hExpAE
  have hXmeanLower : Real.exp (-D) ≤ ∫ ω, X ω ∂P := by
    have hJ' : Real.exp (∫ ω, Real.log (X ω) ∂P) ≤
        ∫ ω, Real.exp (Real.log (X ω)) ∂P := hJ
    calc
      Real.exp (-D) ≤ Real.exp (∫ ω, Real.log (X ω) ∂P) :=
        Real.exp_le_exp.mpr hXlogmean
      _ ≤ ∫ ω, Real.exp (Real.log (X ω)) ∂P := hJ'
      _ = ∫ ω, X ω ∂P := hExp
  let q : ℝ := (1 + C) / (2 * (1 + C) * Real.exp D)
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hqsmall : q < Real.exp (-D) := by
    have hqEq : q = Real.exp (-D) / 2 := by
      dsimp [q]
      rw [Real.exp_neg]
      field_simp
    rw [hqEq]
    nlinarith [Real.exp_pos (-D)]
  let a : ℝ := Real.exp (-(2 * (1 + C) * Real.exp D))
  have ha : 0 < a := Real.exp_pos _
  have ha1 : a < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have : 0 < 2 * (1 + C) * Real.exp D := by positivity
    linarith
  have htail := measure_lt_of_log_mean_lower Ω P R C a ha ha1 hRpos hRint hRmean hRlog hRlogmean
  have hlogInv : Real.log a⁻¹ = 2 * (1 + C) * Real.exp D := by
    dsimp [a]
    rw [Real.exp_neg, inv_inv, Real.log_exp]
  have htailReal : (P {ω | R ω < a}).toReal ≤ q := by
    have hq : (1 + C) / Real.log a⁻¹ = q := by
      dsimp [q]
      rw [hlogInv]
    have htailq : P {ω | R ω < a} ≤ ENNReal.ofReal q := by
      simpa only [hq] using htail
    exact ENNReal.toReal_le_of_le_ofReal hqpos.le htailq
  have hset : MeasurableSet {ω | a ≤ R ω} := by
    exact measurableSet_le measurable_const hRmeas
  have hRetInt : Integrable (Set.indicator {ω | a ≤ R ω} X) P := hXint.indicator hset
  have hOutsideBound : ∫ ω in {ω | R ω < a}, X ω ∂P ≤ q := by
    have hS : MeasurableSet {ω | R ω < a} := measurableSet_lt hRmeas measurable_const
    have hleOne : X ≤ᵐ[P.restrict {ω | R ω < a}] fun _ => (1 : ℝ) :=
      (ae_restrict_iff' hS).2 (hXle.mono fun _ hω _ => hω)
    have hconst : Integrable (fun _ : Ω => (1 : ℝ)) (P.restrict {ω | R ω < a}) := integrable_const 1
    have hmono := integral_mono_ae hXint.integrableOn hconst hleOne
    have hreal : (∫ ω in {ω | R ω < a}, (1 : ℝ) ∂P) = (P {ω | R ω < a}).toReal := by
      simp [Measure.real_def]
    rw [hreal] at hmono
    exact hmono.trans htailReal
  have hcompl : ({ω | a ≤ R ω}ᶜ) = {ω | R ω < a} := by
    ext ω
    simp [not_le]
  have hretEq :
      (∫ ω, Set.indicator {ω | a ≤ R ω} X ω ∂P) +
        (∫ ω in {ω | a ≤ R ω}ᶜ, X ω ∂P) = ∫ ω, X ω ∂P := by
    rw [integral_indicator hset]
    exact integral_add_compl hset hXint
  let c : ℝ := Real.exp (-D) - q
  have hdenEq : (1 + C) / (2 * (1 + C) * Real.exp D) = Real.exp (-D) / 2 := by
    rw [Real.exp_neg]
    field_simp [ne_of_gt (show 0 < 1 + C by linarith)]
  refine ⟨ha, ha1, ?_, hRetInt, ?_⟩
  ·
    rw [hdenEq]
    nlinarith [Real.exp_pos (-D)]
  · rw [hcompl] at hretEq
    linarith [hXmeanLower, hOutsideBound, hretEq, hdenEq]

end Critical2DKPZ.NonGaussian

end
