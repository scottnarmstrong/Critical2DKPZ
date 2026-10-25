/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SmallScales.HeatStartLogCLT
public import Critical2DKPZ.SmallScales.ShrinkingRegularizedReversed
public import Critical2DKPZ.JointConvergence.ThmToyJointLimit
import Critical2DKPZ.JointConvergence.HeatStartLogFieldConvergence
import Mathlib.Tactic

/-! # Integrability identities for the fixed reversed check field

These auxiliary proofs are adapted from the private helpers in
`Critical2DKPZ.SmallScales.PointMatchedComparison`. Their extension names allow
one fixed joint toy-limit field to be used at every test and smoothing width.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.LocalSobolev Critical2DKPZ.SHF.Positivity
open Critical2DKPZ.SHF.Limit Critical2DKPZ.JointConvergence Critical2DKPZ.SmallScales
open scoped BoundedContinuousFunction ENNReal Topology

universe u

namespace Critical2DKPZ.Extensions.ScaleLimit

theorem checkField_integral_abs_le_eLpNorm_two {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ) (C : ℝ)
    (hbound : eLpNorm f 2 P ≤ ENNReal.ofReal C) :
    Integrable f P ∧ ∫ ω, |f ω| ∂P ≤ max C 0 := by
  have hbound' : eLpNorm f 2 P ≤ ENNReal.ofReal (max C 0) :=
    hbound.trans (ENNReal.ofReal_le_ofReal (le_max_left C 0))
  have hfinite : eLpNorm f 2 P < ⊤ := hbound'.trans_lt ENNReal.ofReal_lt_top
  have hsm : AEStronglyMeasurable f P := aestronglyMeasurable_of_eLpNorm_ne_top hfinite.ne
  have hbound1 : eLpNorm f 1 P ≤ ENNReal.ofReal (max C 0) := by
    exact (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans hbound'
  have hfinite1 : eLpNorm f 1 P < ⊤ := hbound1.trans_lt ENNReal.ofReal_lt_top
  have hmem1 : MemLp f 1 P := hfinite1
  have hint : Integrable f P := memLp_one_iff_integrable.mp hmem1
  have habs : ∫ ω, |f ω| ∂P = (eLpNorm f 1 P).toReal := by
    calc
      ∫ ω, |f ω| ∂P = ∫ ω, ‖f ω‖ ∂P := by simp only [Real.norm_eq_abs]
      _ = (∫⁻ ω, ‖f ω‖ₑ ∂P).toReal := integral_norm_eq_lintegral_enorm hsm
      _ = (eLpNorm f 1 P).toReal := by rw [← eLpNorm_one_eq_lintegral_enorm hsm]
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound1
  rw [ENNReal.toReal_ofReal (le_max_right C 0)] at hreal
  exact ⟨hint, habs ▸ hreal⟩

theorem checkField_heatStartLog_test_integrable (ϑ : ℝ) {Ω : Type u}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {σ T : ℝ} (hσ : 0 < σ) (hσT : σ < T) (φ : TestFn) :
    ∀ᵐ ω ∂P, Integrable (fun y => φ y * heatStartLog Z σ T σ y ω) := by
  have hpair : ∀ {s t δ : ℝ}, 0 ≤ s → s < t → 0 < δ → ∀ (x : Plane)
      (g : Plane →ᵇ ℝ),
      (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane =>
        heatKernel δ (p.1 - x) * g p.2) (Z s t ω)) ∧
      Integrable (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) P ∧
      (∫ ω, |shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω| ∂P ≤ ‖g‖) ∧
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) =>
          ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(polymerMeasure ϑ N s t ω))
        atTop (shfPairing Z s t (fun y => heatKernel δ (y - x)) g)
        (fun _ => disorderLaw) P := by
    intro s t δ hs hst hδ x g
    exact isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hs hst hδ x g
  have hjoint := isCriticalSHF_heat_bounded_pairing_joint ϑ P Z hZ
  have hpos : ∀ (s t δ : ℝ) (x : Plane) (h₀ : Plane →ᵇ ℝ),
      0 ≤ s → s < t → 0 < δ →
      (∀ᵐ ω ∂P, 0 < shfPairing Z s t (fun y => heatKernel δ (y - x))
        (fun y => Real.exp (h₀ y)) ω) ∧
      AEMeasurable (fun ω => Real.log (shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)) P := by
    intro s t δ x h₀ hs hst hδ
    have h := isCriticalSHF_heat_pairing_pos_isEhrhardType
      ϑ P Z hZ s t δ x h₀ hs hst hδ
    exact ⟨h.1, h.2.1⟩
  let μ : Ω → Measure (Plane × Plane) := Z σ T
  have hlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
    filter_upwards [hZ.2.1 σ T (le_of_lt hσ) hσT] with ω hω
    exact hω.1
  have hg : Measurable (fun y : Plane => Real.exp ((0 : Plane →ᵇ ℝ) y)) := by fun_prop
  have hF : AEMeasurable (fun q : Plane × Ω => heatStartLog Z σ T σ q.1 q.2)
      (volume.prod P) := by
    have h := aemeasurable_log_heatPairing_joint P μ (hZ.1 σ T (le_of_lt hσ) hσT)
      hlocal σ hσ (fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) hg
      (fun y => Real.exp_nonneg _)
    simpa [μ, heatStartLog, shfPairing, Real.exp_zero] using h
  have hFsec (x : Plane) : AEStronglyMeasurable
      (fun ω => heatStartLog Z σ T σ x ω) P := by
    have h := hpos σ T σ x 0 (le_of_lt hσ) hσT hσ
    change AEStronglyMeasurable (fun ω => Real.log
      (shfPairing Z σ T (fun y => heatKernel σ (y - x)) (fun _ => 1) ω)) P
    simpa only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] using
      h.2.aestronglyMeasurable
  obtain ⟨M, hM, hSq⟩ := shf_heatStartLogField_square_bound ϑ P Z hZ hpair hjoint hpos
    T 0 (s := σ) (δ := σ) (le_of_lt hσ) hσT hσ
  have hSq' : ∀ x : Plane, Integrable (fun ω =>
      |heatStartLog Z σ T σ x ω| ^ 2) P ∧
      ∫ ω, |heatStartLog Z σ T σ x ω| ^ 2 ∂P ≤ M := by
    intro x
    simpa only [heatStartLog, BoundedContinuousFunction.coe_zero, Pi.zero_apply,
      Real.exp_zero] using hSq x
  have hprod := integrable_test_mul_joint P hF hFsec hM hSq' φ
  exact Integrable.prod_left_ae hprod

theorem checkField_regularized_integral_sub_ae (ϑ : ℝ) {Ω : Type u}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {T α β : ℝ} (hα : 0 < α) (hαT : α < T) (hβ : 0 < β) (hβT : β < T)
    (φ : TestFn) :
    (fun ω => ∫ y, φ y * (kpzRegularizedReversed P Z 0 T α 0 y ω -
      kpzRegularizedReversed P Z 0 T β 0 y ω)) =ᵐ[P]
      fun ω => (∫ y, φ y * kpzRegularizedReversed P Z 0 T α 0 y ω) -
        (∫ y, φ y * kpzRegularizedReversed P Z 0 T β 0 y ω) := by
  have hαint := checkField_heatStartLog_test_integrable ϑ P Z hZ hα hαT φ
  have hβint := checkField_heatStartLog_test_integrable ϑ P Z hZ hβ hβT φ
  filter_upwards [hαint, hβint] with ω hαω hβω
  have hαc : Integrable (fun y => φ y * kpzRegularizedReversed P Z 0 T α 0 y ω) := by
    let cα : ℝ := ∫ ω', heatStartLog Z α T α 0 ω' ∂P
    have heq : (fun y => φ y * kpzRegularizedReversed P Z 0 T α 0 y ω) =
        fun y => φ y * heatStartLog Z α T α y ω - φ y * cα := by
      funext y
      simp [cα, kpzRegularizedReversed, heatStartLog, zero_add, Real.exp_zero]
      ring
    rw [heq]
    exact hαω.sub ((φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).mul_const cα)
  have hβc : Integrable (fun y => φ y * kpzRegularizedReversed P Z 0 T β 0 y ω) := by
    let cβ : ℝ := ∫ ω', heatStartLog Z β T β 0 ω' ∂P
    have heq : (fun y => φ y * kpzRegularizedReversed P Z 0 T β 0 y ω) =
        fun y => φ y * heatStartLog Z β T β y ω - φ y * cβ := by
      funext y
      simp [cβ, kpzRegularizedReversed, heatStartLog, zero_add, Real.exp_zero]
      ring
    rw [heq]
    exact hβω.sub ((φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).mul_const cβ)
  have hfun : (fun y => φ y * (kpzRegularizedReversed P Z 0 T α 0 y ω -
      kpzRegularizedReversed P Z 0 T β 0 y ω)) =
      fun y => φ y * kpzRegularizedReversed P Z 0 T α 0 y ω -
        φ y * kpzRegularizedReversed P Z 0 T β 0 y ω := by
    funext y
    rw [mul_sub]
  calc
    (∫ y, φ y * (kpzRegularizedReversed P Z 0 T α 0 y ω -
        kpzRegularizedReversed P Z 0 T β 0 y ω)) =
        ∫ y, φ y * kpzRegularizedReversed P Z 0 T α 0 y ω -
          φ y * kpzRegularizedReversed P Z 0 T β 0 y ω := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => congrFun hfun y
    _ = (∫ y, φ y * kpzRegularizedReversed P Z 0 T α 0 y ω) -
        ∫ y, φ y * kpzRegularizedReversed P Z 0 T β 0 y ω := integral_sub hαc hβc

theorem checkField_regularized_average_centered_ae (ϑ : ℝ) {Ω : Type u}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) {T ε : ℝ} (_hT : 0 < T) (hε : 0 < ε)
    (hεT : ε ^ 2 < T) (φ : TestFn) (hφ₁ : ∫ y, φ y = 1) (x : Plane) :
    (fun ω => (∫ y, (φ.dilate ε x) y *
      kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω) -
      (heatStartLog Z (ε ^ 2) T (ε ^ 2) (x + ε • barycentre φ) ω -
        ∫ ω', heatStartLog Z (ε ^ 2) T (ε ^ 2)
          (x + ε • barycentre φ) ω' ∂P)) =ᵐ[P]
      fun ω => (∫ y, (φ.dilate ε x) y *
        heatStartLog Z (ε ^ 2) T (ε ^ 2) y ω) -
          heatStartLog Z (ε ^ 2) T (ε ^ 2) (x + ε • barycentre φ) ω := by
  let base : TestFn := φ.dilate ε x
  let b : Plane := x + ε • barycentre φ
  have hδ : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hmass : ∫ y, base y = 1 := by
    simpa only [base, hφ₁, mul_one] using
      integral_testFn_dilate_mul φ hε x (fun _ => (1 : ℝ))
  have hlogInt := checkField_heatStartLog_test_integrable ϑ P Z hZ hδ hεT base
  have hbaseInt : Integrable base :=
    base.continuous.integrable_of_hasCompactSupport base.hasCompactSupport
  have hInt0 := heatStartLog_integrable_of ϑ P Z hZ (le_of_lt hδ) hεT hδ (0 : Plane)
  have hIntb := heatStartLog_integrable_of ϑ P Z hZ (le_of_lt hδ) hεT hδ b
  have hident := heatStartLog_identDistrib_of ϑ P Z hZ hsym
    (le_of_lt hδ) hεT hδ b
  have hmean : (∫ ω', heatStartLog Z (ε ^ 2) T (ε ^ 2) b ω' ∂P) =
      ∫ ω', heatStartLog Z (ε ^ 2) T (ε ^ 2) 0 ω' ∂P := hident.integral_eq
  let c : ℝ := ∫ ω', heatStartLog Z (ε ^ 2) T (ε ^ 2) 0 ω' ∂P
  filter_upwards [hlogInt] with ω hlogω
  have hregInt : Integrable (fun y => base y *
      kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω) := by
    have heq : (fun y => base y * kpzRegularizedReversed P Z 0 T
        (ε ^ 2) 0 y ω) = fun y => base y * heatStartLog Z (ε ^ 2) T
          (ε ^ 2) y ω - base y * c := by
      funext y
      simp [c, kpzRegularizedReversed, heatStartLog, zero_add, Real.exp_zero]
      ring
    rw [heq]
    exact hlogω.sub (hbaseInt.mul_const c)
  have hregEq : (∫ y, base y * kpzRegularizedReversed P Z 0 T
      (ε ^ 2) 0 y ω) =
      (∫ y, base y * heatStartLog Z (ε ^ 2) T (ε ^ 2) y ω) -
        ∫ ω', heatStartLog Z (ε ^ 2) T (ε ^ 2) b ω' ∂P := by
    calc
      _ = (∫ y, base y * heatStartLog Z (ε ^ 2) T (ε ^ 2) y ω) -
          ∫ y, base y * c := by
        rw [show (fun y => base y * kpzRegularizedReversed P Z 0 T
            (ε ^ 2) 0 y ω) = fun y => base y * heatStartLog Z (ε ^ 2) T
              (ε ^ 2) y ω - base y * c by
              funext y
              simp [c, kpzRegularizedReversed, heatStartLog, zero_add, Real.exp_zero]
              ring]
        exact integral_sub hlogω (hbaseInt.mul_const c)
      _ = (∫ y, base y * heatStartLog Z (ε ^ 2) T (ε ^ 2) y ω) - c := by
        rw [integral_mul_const, hmass]
        ring
      _ = (∫ y, base y * heatStartLog Z (ε ^ 2) T (ε ^ 2) y ω) -
          ∫ ω', heatStartLog Z (ε ^ 2) T (ε ^ 2) b ω' ∂P := by rw [hmean]
  change (∫ y, base y * kpzRegularizedReversed P Z 0 T (ε ^ 2) 0 y ω) -
      (heatStartLog Z (ε ^ 2) T (ε ^ 2) b ω -
        ∫ ω', heatStartLog Z (ε ^ 2) T (ε ^ 2) b ω' ∂P) = _
  rw [hregEq]
  ring

end Critical2DKPZ.Extensions.ScaleLimit
