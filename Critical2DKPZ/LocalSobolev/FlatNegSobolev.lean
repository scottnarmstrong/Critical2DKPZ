/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.FlatCovariance
public import Critical2DKPZ.Analysis.Sobolev.LocalizedMoment
import Critical2DKPZ.LocalSobolev.LatticeMoment
import Critical2DKPZ.SHF.Tsai.Tech
import Critical2DKPZ.CovarianceKernel.RegularizedSpecification
import Critical2DKPZ.Assembly.RegularizedComparison
import Critical2DKPZ.SHF.Positivity.HeatBoundedIntegrability
import Critical2DKPZ.JointConvergence.LogHeatFieldMeasurability
import Mathlib.Tactic

/-! # Negative Sobolev moment bounds for regularized KPZ fields -/

@[expose] public section

noncomputable section

open MeasureTheory Set ProbabilityTheory Filter
open Critical2DKPZ.CovarianceKernel
open scoped BoundedContinuousFunction ENNReal Topology

universe u

namespace Critical2DKPZ.LocalSobolev

private theorem covarianceLogEnvelope_rpow_le_inv_sqrt (z : Plane) {p : ℝ}
    (hp : 0 < p) (hz : ‖z‖ ≤ 1) (hz0 : z ≠ 0) :
    CovarianceKernel.covarianceLogEnvelope z ^ p ≤
      (1 + 2 * p) ^ p * ‖z‖ ^ (-(1 / 2 : ℝ)) := by
  let u : ℝ := ‖z‖⁻¹
  let δ : ℝ := 1 / (2 * p)
  have hrpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hu : 1 ≤ u := by
    dsimp [u]
    exact (one_le_inv₀ hrpos).2 hz
  have hu0 : 0 ≤ u := le_trans (by norm_num) hu
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg hu
  have hprof : CovarianceKernel.covarianceLogEnvelope z =
      1 + Real.log (1 + Real.log u) := by
    change 1 + Real.log (1 + max 0 (Real.log u)) = _
    rw [max_eq_right hlogu]
  have hnested : Real.log (1 + Real.log u) ≤ Real.log u := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.log u by linarith)
    linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hinvδ : δ⁻¹ = 2 * p := by
    dsimp [δ]
    field_simp
  have hlogpow : Real.log u ≤ u ^ δ / δ := Real.log_le_rpow_div hu0 hδ
  have hupow : 1 ≤ u ^ δ := Real.one_le_rpow hu hδ.le
  have henv : CovarianceKernel.covarianceLogEnvelope z ≤
      (1 + 2 * p) * u ^ δ := by
    rw [hprof]
    calc
      1 + Real.log (1 + Real.log u) ≤ 1 + Real.log u := by linarith
      _ ≤ 1 + u ^ δ / δ := by linarith
      _ = 1 + (2 * p) * u ^ δ := by rw [div_eq_mul_inv, hinvδ]; ring
      _ ≤ (1 + 2 * p) * u ^ δ := by
        nlinarith only [hupow]
  have hpow := Real.rpow_le_rpow (le_of_lt (CovarianceKernel.covarianceLogEnvelope_pos z))
    henv hp.le
  calc
    CovarianceKernel.covarianceLogEnvelope z ^ p ≤ ((1 + 2 * p) * u ^ δ) ^ p := hpow
    _ = (1 + 2 * p) ^ p * u ^ (δ * p) := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hu0 _), ← Real.rpow_mul hu0]
    _ = (1 + 2 * p) ^ p * u ^ (1 / 2 : ℝ) := by
      rw [show δ * p = 1 / 2 by
        dsimp [δ]
        field_simp]
    _ = (1 + 2 * p) ^ p * ‖z‖ ^ (-(1 / 2 : ℝ)) := by
      have huEq : u ^ (1 / 2 : ℝ) = ‖z‖ ^ (-(1 / 2 : ℝ)) := by
        dsimp [u]
        rw [Real.inv_rpow hrpos.le, ← Real.rpow_neg hrpos.le]
      exact congrArg (fun v : ℝ => (1 + 2 * p) ^ p * v) huEq

private theorem integrableOn_covarianceLogEnvelope_rpow_ball {p R : ℝ}
    (hp : 0 < p) :
    IntegrableOn (fun z : Plane => CovarianceKernel.covarianceLogEnvelope z ^ p)
      (Metric.ball 0 R) volume := by
  let C := max ((1 + 2 * p) ^ p) (R ^ (1 / 2 : ℝ))
  have hC1 : (1 + 2 * p) ^ p ≤ C := le_max_left _ _
  have hCR : R ^ (1 / 2 : ℝ) ≤ C := le_max_right _ _
  have hmeas : AEStronglyMeasurable
      (fun z : Plane => CovarianceKernel.covarianceLogEnvelope z ^ p) volume := by
    exact ((by fun_prop [CovarianceKernel.covarianceLogEnvelope] :
      Measurable (fun z : Plane => CovarianceKernel.covarianceLogEnvelope z ^ p))
      ).aestronglyMeasurable
  have hdecay : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : Plane) R),
      ‖CovarianceKernel.covarianceLogEnvelope z ^ p‖ ≤ C * ‖z‖ ^ (-(1 / 2 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne (0 : Plane))] with z hzball hz0
    have hzNorm : ‖z‖ < R := by
      simpa [Metric.mem_ball, dist_zero_right] using hzball
    have hrpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg
        (le_of_lt (CovarianceKernel.covarianceLogEnvelope_pos z)) _)]
    by_cases hzle : ‖z‖ ≤ 1
    · exact (covarianceLogEnvelope_rpow_le_inv_sqrt z hp hzle hz0).trans
        (mul_le_mul_of_nonneg_right hC1 (Real.rpow_nonneg hrpos.le _))
    · have hone : 1 ≤ ‖z‖ := le_of_not_ge hzle
      have henv := CovarianceKernel.covarianceLogEnvelope_eq_one_of_one_le_norm z hone
      have hpow : CovarianceKernel.covarianceLogEnvelope z ^ p = 1 := by
        rw [henv, Real.one_rpow]
      rw [hpow]
      have hroot : ‖z‖ ^ (1 / 2 : ℝ) ≤ R ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (norm_nonneg _) hzNorm.le (by norm_num)
      have hrootC : ‖z‖ ^ (1 / 2 : ℝ) ≤ C := hroot.trans hCR
      have hrootPos : 0 < ‖z‖ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hrpos _
      have hratio : 1 ≤ C / ‖z‖ ^ (1 / 2 : ℝ) :=
        (one_le_div₀ hrootPos).2 hrootC
      rw [div_eq_mul_inv, ← Real.rpow_neg (norm_nonneg _) (1 / 2 : ℝ)] at hratio
      exact hratio
  exact integrableOn_ball_of_norm_le_rpow
    (by norm_num [Plane] : 1 ≤ Module.finrank ℝ Plane)
    (by norm_num [Plane] : (1 / 2 : ℝ) < Module.finrank ℝ Plane)
    hdecay hmeas

private theorem covarianceLogEnvelope_ge_one (z : Plane) :
    1 ≤ CovarianceKernel.covarianceLogEnvelope z := by
  unfold CovarianceKernel.covarianceLogEnvelope
  have hm : 0 ≤ max 0 (Real.log ‖z‖⁻¹) := le_max_left _ _
  have hl : 0 ≤ Real.log (1 + max 0 (Real.log ‖z‖⁻¹)) :=
    Real.log_nonneg (by linarith)
  linarith

private theorem lintegral_heatKernel_mul_covarianceLogEnvelope_le {p : ℝ}
    (hp : 1 < p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u : ℝ, 0 < u → ∀ x : Plane,
      (∫⁻ y : Plane, ENNReal.ofReal (heatKernel u (x - y)) *
        ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (x - y))) ≤
          ENNReal.ofReal (1 + A * u ^ (-1 / p)) := by
  let B : Set Plane := Metric.ball 0 1
  let cut : Plane → ℝ≥0∞ := B.indicator fun z =>
    ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope z)
  let M : ℝ≥0∞ := ∫⁻ z : Plane in B,
    ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope z ^ p)
  have hB : MeasurableSet B := measurableSet_ball
  have henvMeas : Measurable CovarianceKernel.covarianceLogEnvelope := by
    fun_prop [CovarianceKernel.covarianceLogEnvelope]
  have hcutMeas : Measurable cut := by
    exact (henvMeas.ennreal_ofReal).indicator hB
  have hcutPow : (fun z : Plane => cut z ^ p) = B.indicator
      (fun z => ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope z ^ p)) := by
    funext z
    by_cases hz : z ∈ B
    · have hpos := CovarianceKernel.covarianceLogEnvelope_pos z
      simp [cut, hz, ENNReal.ofReal_rpow_of_nonneg hpos.le (by linarith : 0 ≤ p)]
    · simp [cut, hz, ENNReal.zero_rpow_of_pos (by linarith : 0 < p)]
  have hIntEnv := integrableOn_covarianceLogEnvelope_rpow_ball
    (by linarith : 0 < p) (R := 1)
  have hconv : ENNReal.ofReal (∫ z : Plane in B,
      CovarianceKernel.covarianceLogEnvelope z ^ p) = M := by
    dsimp [M]
    exact ofReal_integral_eq_lintegral_ofReal hIntEnv
      (Filter.Eventually.of_forall fun z => Real.rpow_nonneg
        (le_of_lt (CovarianceKernel.covarianceLogEnvelope_pos z)) _)
  have hMtop : M < ⊤ := by
    rw [← hconv]
    exact ENNReal.ofReal_lt_top
  have hcutLp : (∫⁻ z : Plane, cut z ^ p) = M := by
    rw [hcutPow, lintegral_indicator hB]
  have hcutLower (z : Plane) :
      ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope z) ≤ 1 + cut z := by
    by_cases hz : z ∈ B
    · have hpos := CovarianceKernel.covarianceLogEnvelope_pos z
      have hcut : cut z = ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope z) := by
        simp [cut, hz]
      rw [hcut]
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) hpos.le]
      exact ENNReal.ofReal_le_ofReal (by linarith [covarianceLogEnvelope_ge_one z])
    · have hone : 1 ≤ ‖z‖ := by
        have hz' : ¬ ‖z‖ < 1 := by
          intro h
          exact hz (by simpa [B, Metric.mem_ball, dist_zero_right] using h)
        exact le_of_not_gt hz'
      rw [CovarianceKernel.covarianceLogEnvelope_eq_one_of_one_le_norm z hone]
      simp [cut, hz]
  obtain ⟨c, hc, hheat⟩ := Critical2DKPZ.SHF.Tsai.integral_heatKernel_mul_le hp
  let root : ℝ≥0∞ := M ^ (1 / p)
  have hrootTop : root < ⊤ := by
    dsimp [root]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hMtop.ne
  let D : ℝ := root.toReal
  have hrootEq : root = ENNReal.ofReal D := by
    dsimp [D]
    exact (ENNReal.ofReal_toReal hrootTop.ne).symm
  let A : ℝ := c * D
  have hAnonneg : 0 ≤ A := by
    dsimp [A, D]
    positivity
  refine ⟨A, hAnonneg, ?_⟩
  intro u hu x
  let shifted : Plane → ℝ≥0∞ := fun y => cut (x - y)
  have hshiftMeas : Measurable shifted := by
    exact hcutMeas.comp (measurable_const.sub measurable_id)
  have hmp : MeasurePreserving (fun y : Plane => x - y) volume volume :=
    volume.measurePreserving_sub_left x
  have hshiftLp : (∫⁻ y : Plane, shifted y ^ p) = M := by
    calc
      _ = ∫⁻ y : Plane, cut (x - y) ^ p := by simp [shifted]
      _ = ∫⁻ y : Plane, cut y ^ p :=
        hmp.lintegral_comp (ENNReal.continuous_rpow_const.measurable.comp hcutMeas)
      _ = M := hcutLp
  have hkernelMeas : Measurable (fun y : Plane => ENNReal.ofReal (heatKernel u (x - y))) := by
    exact ((measurable_heatKernel u).comp (measurable_const.sub measurable_id)).ennreal_ofReal
  have hmass : (∫⁻ y : Plane,
      ENNReal.ofReal (heatKernel u (x - y))) = ENNReal.ofReal 1 := by
    have hInt := hmp.integrable_comp_of_integrable (integrable_heatKernel hu)
    have hreal : ENNReal.ofReal (∫ y : Plane, heatKernel u (x - y)) =
        ∫⁻ y : Plane, ENNReal.ofReal (heatKernel u (x - y)) := by
      simpa only [Function.comp_apply] using
        (ofReal_integral_eq_lintegral_ofReal hInt
          (Filter.Eventually.of_forall fun y => heatKernel_nonneg hu.le _))
    rw [← hreal]
    have hkerEq : (fun y : Plane => heatKernel u (x - y)) =
        fun y => heatKernel u (y - x) := by
      funext y
      rw [show x - y = -(y - x) by abel, heatKernel_neg]
    rw [hkerEq, integral_heatKernel_sub hu x]
  have hsing := hheat u hu x shifted hshiftMeas
  have hfull : (∫⁻ y : Plane, ENNReal.ofReal (heatKernel u (x - y)) * shifted y) ≤
      ENNReal.ofReal (c * u ^ (-1 / p)) * root := by
    rw [hshiftLp] at hsing
    exact hsing
  have hsum : (∫⁻ y : Plane,
      ENNReal.ofReal (heatKernel u (x - y)) * ENNReal.ofReal 1 +
        ENNReal.ofReal (heatKernel u (x - y)) * shifted y) =
      ENNReal.ofReal 1 +
        ∫⁻ y : Plane, ENNReal.ofReal (heatKernel u (x - y)) * shifted y := by
    rw [lintegral_add_left (hkernelMeas.mul_const (ENNReal.ofReal 1))]
    simp only [ENNReal.ofReal_one, mul_one, hmass]
  have hbound : (∫⁻ y : Plane,
      ENNReal.ofReal (heatKernel u (x - y)) *
        ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (x - y))) ≤
      ENNReal.ofReal 1 + ENNReal.ofReal (c * u ^ (-1 / p)) * root := by
    calc
      _ ≤ ∫⁻ y : Plane,
          ENNReal.ofReal (heatKernel u (x - y)) * (ENNReal.ofReal 1 + shifted y) := by
            apply lintegral_mono
            intro y
            change ENNReal.ofReal (heatKernel u (x - y)) *
              ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (x - y)) ≤
                ENNReal.ofReal (heatKernel u (x - y)) *
                  (ENNReal.ofReal 1 + cut (x - y))
            calc
              _ = ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (x - y)) *
                  ENNReal.ofReal (heatKernel u (x - y)) := mul_comm _ _
              _ ≤ (ENNReal.ofReal 1 + cut (x - y)) *
                  ENNReal.ofReal (heatKernel u (x - y)) := by
                    simpa only [ENNReal.ofReal_one] using
                      (mul_le_mul_left (hcutLower (x - y))
                        (ENNReal.ofReal (heatKernel u (x - y))))
              _ = _ := mul_comm _ _
      _ = _ := by
        rw [show (fun y : Plane =>
            ENNReal.ofReal (heatKernel u (x - y)) * (ENNReal.ofReal 1 + shifted y)) =
            fun y => ENNReal.ofReal (heatKernel u (x - y)) * ENNReal.ofReal 1 +
              ENNReal.ofReal (heatKernel u (x - y)) * shifted y by
          funext y
          rw [mul_add]]
        rw [hsum]
      _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal (c * u ^ (-1 / p)) * root :=
        add_le_add le_rfl hfull
  rw [hrootEq, ← ENNReal.ofReal_mul (by positivity : 0 ≤ c * u ^ (-1 / p))] at hbound
  have hAeq : c * u ^ (-1 / p) * D = A * u ^ (-1 / p) := by
    dsimp [A]
    ring
  rw [hAeq, ← ENNReal.ofReal_add (by norm_num) (by positivity)] at hbound
  exact hbound

private theorem testFn_norm_data (χ : TestFn) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ x : Plane, ‖χ x‖ ≤ B) ∧
      Integrable (fun x : Plane => ‖χ x‖) volume := by
  have hK : IsCompact (tsupport χ) := χ.hasCompactSupport.isCompact
  have hImage : IsCompact ((fun x : Plane => ‖χ x‖) '' tsupport χ) :=
    hK.image χ.continuous.norm
  obtain ⟨M, hM⟩ := hImage.bddAbove
  refine ⟨max M 0, le_max_right _ _, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ tsupport χ
    · exact (hM ⟨x, hx, rfl⟩).trans (le_max_left _ _)
    · have hx0 : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hx0]
  · exact (χ.continuous.integrable_of_hasCompactSupport χ.hasCompactSupport).norm

private theorem lintegral_testFn_heatEnvelope_le (χ : TestFn) {p : ℝ}
    (hp : 1 < p) :
    ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧ (∀ y : Plane, ‖χ y‖ ≤ B) ∧
      ∀ u : ℝ, 0 < u → ∀ x : Plane,
        (∫⁻ y : Plane, ENNReal.ofReal ‖χ y‖ *
          (ENNReal.ofReal (heatKernel u (x - y)) *
            ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (x - y)))) ≤
          ENNReal.ofReal (B * (1 + A * u ^ (-1 / p))) := by
  obtain ⟨B, hB, hBbound, _⟩ := testFn_norm_data χ
  obtain ⟨A, hA, hheat⟩ := lintegral_heatKernel_mul_covarianceLogEnvelope_le hp
  refine ⟨B, A, hB, hA, hBbound, ?_⟩
  intro u hu x
  calc
    _ ≤ ∫⁻ y : Plane, ENNReal.ofReal B *
        (ENNReal.ofReal (heatKernel u (x - y)) *
          ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (x - y))) := by
          apply lintegral_mono
          intro y
          exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hBbound y)) _
    _ = ENNReal.ofReal B *
        ∫⁻ y : Plane, ENNReal.ofReal (heatKernel u (x - y)) *
          ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (x - y)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal B * ENNReal.ofReal (1 + A * u ^ (-1 / p)) := by
          calc
            _ = (∫⁻ y : Plane, ENNReal.ofReal (heatKernel u (x - y)) *
                ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (x - y))) *
                  ENNReal.ofReal B := mul_comm _ _
            _ ≤ ENNReal.ofReal (1 + A * u ^ (-1 / p)) * ENNReal.ofReal B :=
                  mul_le_mul_left (hheat u hu x) _
            _ = _ := mul_comm _ _
    _ = ENNReal.ofReal (B * (1 + A * u ^ (-1 / p))) := by
          rw [← ENNReal.ofReal_mul hB]

private theorem lintegral_testFn_pair_heatEnvelope_le (χ : TestFn) {p : ℝ}
    (hp : 1 < p) :
    ∃ B L A : ℝ, 0 ≤ B ∧ 0 ≤ L ∧ 0 ≤ A ∧
      ∀ u : ℝ, 0 < u →
        (∫⁻ q : Plane × Plane, ENNReal.ofReal ‖χ q.1‖ *
          (ENNReal.ofReal ‖χ q.2‖ *
            (ENNReal.ofReal (heatKernel (2 * u) (q.1 - q.2)) *
              ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (q.1 - q.2))))
            ∂volume.prod volume) ≤
          ENNReal.ofReal (L * B * (1 + A * (2 * u) ^ (-1 / p))) := by
  obtain ⟨_, _, _, hχInt⟩ := testFn_norm_data χ
  obtain ⟨B, A, hB, hA, hBbound, hinner⟩ := lintegral_testFn_heatEnvelope_le χ hp
  let L : ℝ := ∫ x : Plane, ‖χ x‖
  have hL : 0 ≤ L := by
    dsimp [L]
    exact integral_nonneg (fun x : Plane => norm_nonneg (χ x))
  have hLconv :
      (∫⁻ x : Plane, ENNReal.ofReal ‖χ x‖) = ENNReal.ofReal L := by
    dsimp [L]
    exact (ofReal_integral_eq_lintegral_ofReal hχInt
      (Filter.Eventually.of_forall fun x => norm_nonneg (χ x))
      ).symm
  refine ⟨B, L, A, hB, hL, hA, ?_⟩
  intro u hu
  have hχmeas : Measurable (fun x : Plane => ENNReal.ofReal ‖χ x‖) :=
    (χ.continuous.norm.measurable).ennreal_ofReal
  have hkernelMeas : Measurable (fun q : Plane × Plane =>
      ENNReal.ofReal (heatKernel (2 * u) (q.1 - q.2))) :=
    ((measurable_heatKernel (2 * u)).comp
      (measurable_fst.sub measurable_snd)).ennreal_ofReal
  have henvMeas : Measurable (fun q : Plane × Plane =>
      ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (q.1 - q.2))) := by
    fun_prop [CovarianceKernel.covarianceLogEnvelope]
  have hmeas : Measurable (fun q : Plane × Plane =>
      ENNReal.ofReal ‖χ q.1‖ *
        (ENNReal.ofReal ‖χ q.2‖ *
          (ENNReal.ofReal (heatKernel (2 * u) (q.1 - q.2)) *
            ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (q.1 - q.2))))) :=
    (hχmeas.comp measurable_fst).mul
      ((hχmeas.comp measurable_snd).mul (hkernelMeas.mul henvMeas))
  rw [lintegral_prod _ hmeas.aemeasurable]
  calc
    _ ≤ ∫⁻ x : Plane, ENNReal.ofReal ‖χ x‖ *
        ENNReal.ofReal (B * (1 + A * (2 * u) ^ (-1 / p))) := by
          apply lintegral_mono
          intro x
          change (∫⁻ y : Plane, ENNReal.ofReal ‖χ x‖ *
              (ENNReal.ofReal ‖χ y‖ *
                (ENNReal.ofReal (heatKernel (2 * u) (x - y)) *
                  ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (x - y))))) ≤
            ENNReal.ofReal ‖χ x‖ *
              ENNReal.ofReal (B * (1 + A * (2 * u) ^ (-1 / p)))
          have hpoint := hinner (2 * u) (mul_pos (by norm_num) hu) x
          calc
            _ = (∫⁻ y : Plane, ENNReal.ofReal ‖χ y‖ *
                (ENNReal.ofReal (heatKernel (2 * u) (x - y)) *
                  ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (x - y)))) *
                  ENNReal.ofReal ‖χ x‖ := by
                    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
                    rw [mul_comm (ENNReal.ofReal ‖χ x‖)]
            _ ≤ ENNReal.ofReal (B * (1 + A * (2 * u) ^ (-1 / p))) *
                ENNReal.ofReal ‖χ x‖ :=
                  mul_le_mul_left hpoint _
            _ = _ := mul_comm _ _
    _ = ENNReal.ofReal L *
        ENNReal.ofReal (B * (1 + A * (2 * u) ^ (-1 / p))) := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hLconv]
    _ = ENNReal.ofReal (L * B * (1 + A * (2 * u) ^ (-1 / p))) := by
          rw [← ENNReal.ofReal_mul hL]
          congr 1
          ring

private theorem kpzRegularized_spatial_covariance_integral_le
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Plane → ℝ)
    (Ccov : ℝ) (hCcov : 0 ≤ Ccov)
    (hcov : ∀ᵐ q : Plane × Plane ∂volume.prod volume,
      q.1 ≠ q.2 ∧
        0 ≤ ProbabilityTheory.covariance (fun ω => X ω q.1)
          (fun ω => X ω q.2) P ∧
        ProbabilityTheory.covariance (fun ω => X ω q.1)
          (fun ω => X ω q.2) P ≤
            Ccov * CovarianceKernel.covarianceLogEnvelope (q.1 - q.2))
    (χ : TestFn) {p : ℝ} (B L A : ℝ)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hpair : ∀ u : ℝ, 0 < u →
      (∫⁻ q : Plane × Plane, ENNReal.ofReal ‖χ q.1‖ *
        (ENNReal.ofReal ‖χ q.2‖ *
          (ENNReal.ofReal (heatKernel (2 * u) (q.1 - q.2)) *
            ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (q.1 - q.2))))
        ∂volume.prod volume) ≤ ENNReal.ofReal (L * B * (1 + A * (2 * u) ^ (-1 / p)))) :
    ∀ u : ℝ, 0 < u →
        (∫ q : Plane × Plane,
          (heatKernel (2 * u) (q.1 - q.2) * (χ q.1 * χ q.2) *
            ProbabilityTheory.covariance (fun ω => X ω q.1)
              (fun ω => X ω q.2) P)
          ∂volume.prod volume) ≤ (Ccov * (L * B)) * (1 + A * (2 * u) ^ (-1 / p)) := by
  have hneq : ∀ᵐ q : Plane × Plane ∂volume.prod volume, q.1 ≠ q.2 := by
    have hset : MeasurableSet {q : Plane × Plane | q.1 ≠ q.2} :=
      (isClosed_eq continuous_fst continuous_snd).measurableSet.compl
    rw [Measure.ae_prod_iff_ae_ae hset]
    filter_upwards [] with x
    filter_upwards [volume.ae_ne x] with y hy
    exact hy.symm
  intro u hu
  let f : Plane × Plane → ℝ := fun q =>
    heatKernel (2 * u) (q.1 - q.2) *
      (χ q.1 * χ q.2 * ProbabilityTheory.covariance
        (fun ω => X ω q.1)
        (fun ω => X ω q.2) P)
  let pairWeight : Plane × Plane → ℝ≥0∞ := fun q =>
    ENNReal.ofReal ‖χ q.1‖ *
      (ENNReal.ofReal ‖χ q.2‖ *
        (ENNReal.ofReal (heatKernel (2 * u) (q.1 - q.2)) *
          ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (q.1 - q.2)))
      )
  have hfieldBound (q : Plane × Plane) (hq : q.1 ≠ q.2)
      (hc : 0 ≤ ProbabilityTheory.covariance
          (fun ω => X ω q.1)
          (fun ω => X ω q.2) P ∧
        ProbabilityTheory.covariance (fun ω => X ω q.1)
          (fun ω => X ω q.2) P ≤
            Ccov * CovarianceKernel.covarianceLogEnvelope (q.1 - q.2)) :
      ‖f q‖ ≤ Ccov * (‖χ q.1‖ * (‖χ q.2‖ *
        (heatKernel (2 * u) (q.1 - q.2) *
          CovarianceKernel.covarianceLogEnvelope (q.1 - q.2)))) := by
    let k := heatKernel (2 * u) (q.1 - q.2)
    let e := CovarianceKernel.covarianceLogEnvelope (q.1 - q.2)
    let c := ProbabilityTheory.covariance
      (fun ω => X ω q.1)
      (fun ω => X ω q.2) P
    have hk : 0 ≤ k := by dsimp [k]; exact heatKernel_nonneg (by positivity) _
    have hnorm : ‖f q‖ = k * (‖χ q.1‖ * (‖χ q.2‖ * c)) := by
      change |k * (χ q.1 * χ q.2 * c)| =
        k * (|χ q.1| * (|χ q.2| * c))
      rw [abs_mul, abs_of_nonneg hk, abs_mul, abs_mul, abs_of_nonneg hc.1]
      ring
    calc
      ‖f q‖ = k * (‖χ q.1‖ * (‖χ q.2‖ * c)) := hnorm
      _ ≤ k * (‖χ q.1‖ * (‖χ q.2‖ * (Ccov * e))) := by
        apply mul_le_mul_of_nonneg_left
        · have hmul := mul_le_mul_of_nonneg_left hc.2
            (mul_nonneg (norm_nonneg (χ q.1)) (norm_nonneg (χ q.2)))
          simpa [mul_assoc] using hmul
        · exact hk
      _ = Ccov * (‖χ q.1‖ * (‖χ q.2‖ * (k * e))) := by
        dsimp [k, e]
        ring
  have hnormAE : ∀ᵐ q : Plane × Plane ∂volume.prod volume,
      ENNReal.ofReal ‖f q‖ ≤ ENNReal.ofReal Ccov * pairWeight q := by
    filter_upwards [hneq, hcov] with q hq hc
    calc
      ENNReal.ofReal ‖f q‖ ≤ ENNReal.ofReal (Ccov *
          (‖χ q.1‖ * (‖χ q.2‖ *
            (heatKernel (2 * u) (q.1 - q.2) *
              CovarianceKernel.covarianceLogEnvelope (q.1 - q.2))))) :=
        ENNReal.ofReal_le_ofReal (hfieldBound q hq ⟨hc.2.1, hc.2.2⟩)
      _ = ENNReal.ofReal Ccov * pairWeight q := by
        dsimp [pairWeight]
        rw [ENNReal.ofReal_mul hCcov, ENNReal.ofReal_mul (abs_nonneg (χ q.1)),
          ENNReal.ofReal_mul (abs_nonneg (χ q.2)),
          ENNReal.ofReal_mul (heatKernel_nonneg (by positivity) _)]
  have hpairU := hpair u hu
  have hnormIntegral :
      (∫⁻ q : Plane × Plane, ENNReal.ofReal ‖f q‖ ∂volume.prod volume) ≤
        ENNReal.ofReal (Ccov * (L * B * (1 + A * (2 * u) ^ (-1 / p)))) := by
    calc
      _ ≤ ∫⁻ q : Plane × Plane, ENNReal.ofReal Ccov * pairWeight q
            ∂volume.prod volume := lintegral_mono_ae hnormAE
      _ = ENNReal.ofReal Ccov *
          ∫⁻ q : Plane × Plane, pairWeight q ∂volume.prod volume := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal Ccov *
          ENNReal.ofReal (L * B * (1 + A * (2 * u) ^ (-1 / p))) :=
            mul_le_mul_of_nonneg_left hpairU (by positivity)
      _ = ENNReal.ofReal (Ccov * (L * B * (1 + A * (2 * u) ^ (-1 / p)))) := by
            rw [← ENNReal.ofReal_mul hCcov]
  have hrealBound :
      ‖∫ q : Plane × Plane, f q ∂volume.prod volume‖ ≤
        Ccov * (L * B * (1 + A * (2 * u) ^ (-1 / p))) := by
    calc
      _ ≤ ENNReal.toReal
          (∫⁻ q : Plane × Plane, ENNReal.ofReal ‖f q‖ ∂volume.prod volume) :=
            norm_integral_le_lintegral_norm _
      _ ≤ Ccov * (L * B * (1 + A * (2 * u) ^ (-1 / p))) := by
            calc
              _ ≤ ENNReal.toReal
                  (ENNReal.ofReal
                    (Ccov * (L * B * (1 + A * (2 * u) ^ (-1 / p))))) :=
                  ENNReal.toReal_mono ENNReal.ofReal_ne_top hnormIntegral
              _ = _ := ENNReal.toReal_ofReal (by positivity)
  have hintegral :
      (∫ q : Plane × Plane, f q ∂volume.prod volume) ≤
        Ccov * (L * B * (1 + A * (2 * u) ^ (-1 / p))) := by
    calc
      _ ≤ |∫ q : Plane × Plane, f q ∂volume.prod volume| := le_abs_self _
      _ = ‖∫ q : Plane × Plane, f q ∂volume.prod volume‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ _ := hrealBound
  simpa [f, mul_assoc, mul_left_comm, mul_comm] using hintegral

private theorem lintegral_rpow_exp_neg_finite {s : ℝ} (hs : -1 < s) :
    (∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (u ^ s * Real.exp (-u))) < ⊤ := by
  have hInt : IntegrableOn (fun u : ℝ => u ^ s * Real.exp (-u)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_rpow hs (by norm_num : (0 : ℝ) < 1))
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      fun u : ℝ => u ^ s * Real.exp (-u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hnonneg]
  exact ENNReal.ofReal_lt_top

/-- A jointly measurable field with a uniform square-moment bound has a measurable version
whose sample paths are locally integrable; a spatial null set accounts for the modification. -/
theorem measurable_locallyIntegrable_modification_of_pointwise_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω × Plane → ℝ) (hX : AEStronglyMeasurable X (P.prod volume))
    (B : ℝ) (hB : 0 ≤ B)
    (hMom : ∀ x : Plane, MemLp (fun ω => X (ω, x)) 2 P ∧
      Integrable (fun ω => X (ω, x) ^ 2) P ∧
      (∫ ω, X (ω, x) ^ 2 ∂P) ≤ B)
    (hZero : ∀ x : Plane, (∫ ω, X (ω, x) ∂P) = 0) :
    ∃ Y : Ω × Plane → ℝ, Measurable Y ∧
      Y =ᵐ[P.prod volume] X ∧
      (∀ x : Plane, MemLp (fun ω => Y (ω, x)) 2 P ∧
        Integrable (fun ω => Y (ω, x) ^ 2) P ∧
        (∫ ω, Y (ω, x) ^ 2 ∂P) ≤ B ∧
        (∫ ω, Y (ω, x) ∂P) = 0) ∧
      (∀ ω, LocallyIntegrable (fun x => Y (ω, x)) volume) ∧
      ∃ N : Set Plane, MeasurableSet N ∧ volume N = 0 ∧
        ∀ x ∉ N, (fun ω => Y (ω, x)) =ᵐ[P] fun ω => X (ω, x) := by
  classical
  obtain ⟨Y₀, hY₀meas, hY₀X, hY₀mom, N, hNmeas, hNzero, hNsection⟩ :=
    CovarianceKernel.measurable_field_modification_of_pointwise_moments
      P X hX B hB hMom hZero
  let Q : Ω × Plane → ℝ := Y₀
  have hQmeas : Measurable Q := hY₀meas
  have hSqMeas : Measurable (fun p : Ω × Plane => ENNReal.ofReal (Q p ^ 2)) := by
    exact ENNReal.measurable_ofReal.comp (hQmeas.pow_const 2)
  let ball (n : ℕ) : Set Plane := Metric.ball 0 ((n : ℝ) + 1)
  let sqMass (ω : Ω) (n : ℕ) : ℝ≥0∞ :=
    ∫⁻ x : Plane, ENNReal.ofReal (Q (ω, x) ^ 2) ∂(volume.restrict (ball n))
  have hsqMassMeas (n : ℕ) : Measurable (fun ω => sqMass ω n) := by
    exact hSqMeas.lintegral_prod_right
  have hsqMassInt (n : ℕ) :
      (∫⁻ ω, sqMass ω n ∂P) ≤ ENNReal.ofReal B * volume (ball n) := by
    calc
      _ = ∫⁻ p : Ω × Plane, ENNReal.ofReal (Q p ^ 2)
            ∂P.prod (volume.restrict (ball n)) := by
          symm
          exact lintegral_prod _ hSqMeas.aemeasurable
      _ = ∫⁻ x : Plane in ball n,
            ∫⁻ ω, ENNReal.ofReal (Q (ω, x) ^ 2) ∂P ∂volume := by
          rw [lintegral_prod_symm _ hSqMeas.aemeasurable]
      _ ≤ ∫⁻ x : Plane in ball n, ENNReal.ofReal B ∂volume := by
          apply lintegral_mono
          intro x
          have hQsqInt : Integrable (fun ω => Q (ω, x) ^ 2) P := (hY₀mom x).2.1
          have hQsqNonneg : 0 ≤ᵐ[P] fun ω => Q (ω, x) ^ 2 :=
            Filter.Eventually.of_forall fun ω => sq_nonneg _
          have hQsq := ofReal_integral_eq_lintegral_ofReal hQsqInt hQsqNonneg
          calc
            _ = ENNReal.ofReal (∫ ω, Q (ω, x) ^ 2 ∂P) := hQsq.symm
            _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (hY₀mom x).2.2.1
      _ = ENNReal.ofReal B * volume (ball n) := by
          rw [lintegral_const]
          simp
  have hsqMassFinite (n : ℕ) : ∫⁻ ω, sqMass ω n ∂P < ⊤ := by
    have hball : volume (ball n) < ⊤ := by
      dsimp [ball]
      exact measure_ball_lt_top
    exact lt_of_le_of_lt (hsqMassInt n)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hball)
  let Good : Set Ω := {ω | ∀ n : ℕ, sqMass ω n < ⊤}
  have hGoodMeas : MeasurableSet Good := by
    rw [show Good = ⋂ n : ℕ, {ω | sqMass ω n < ⊤} by
      ext ω
      simp [Good]]
    apply MeasurableSet.iInter
    intro n
    exact measurableSet_lt (hsqMassMeas n) measurable_const
  have hGood : ∀ᵐ ω ∂P, ω ∈ Good := by
    change ∀ᵐ ω ∂P, ∀ n : ℕ, sqMass ω n < ⊤
    exact ae_all_iff.2 fun n =>
      ae_lt_top (hsqMassMeas n) (ne_of_lt (hsqMassFinite n))
  let Y : Ω × Plane → ℝ := fun p => if p.1 ∈ Good then Q p else 0
  have hYmeas : Measurable Y := by
    exact Measurable.ite (hGoodMeas.preimage measurable_fst) hQmeas measurable_const
  have hYQ : Y =ᵐ[P.prod volume] Q := by
    have hGoodProd : ∀ᵐ p : Ω × Plane ∂P.prod volume, p.1 ∈ Good := by
      rw [Measure.ae_prod_iff_ae_ae (hGoodMeas.preimage measurable_fst)]
      filter_upwards [hGood] with ω hω
      exact Filter.Eventually.of_forall fun _ => hω
    filter_upwards [hGoodProd] with p hp
    simp [Y, hp]
  have hYX : Y =ᵐ[P.prod volume] X := hYQ.trans hY₀X.symm
  have hYmom (x : Plane) : MemLp (fun ω => Y (ω, x)) 2 P ∧
      Integrable (fun ω => Y (ω, x) ^ 2) P ∧
      (∫ ω, Y (ω, x) ^ 2 ∂P) ≤ B ∧
      (∫ ω, Y (ω, x) ∂P) = 0 := by
    have hsection : (fun ω => Y (ω, x)) =ᵐ[P] fun ω => Q (ω, x) := by
      filter_upwards [hGood] with ω hω
      simp [Y, hω]
    have hsectionSq : (fun ω => Y (ω, x) ^ 2) =ᵐ[P] fun ω => Q (ω, x) ^ 2 :=
      hsection.mono fun ω hω => congrArg (fun z : ℝ => z ^ 2) hω
    refine ⟨MemLp.ae_eq hsection.symm (hY₀mom x).1,
      (hY₀mom x).2.1.congr hsectionSq.symm, ?_, ?_⟩
    · rw [integral_congr_ae hsectionSq]
      exact (hY₀mom x).2.2.1
    · rw [integral_congr_ae hsection]
      exact (hY₀mom x).2.2.2
  have hYsection (x : Plane) (hx : x ∉ N) :
      (fun ω => Y (ω, x)) =ᵐ[P] fun ω => X (ω, x) := by
    have hYQ : (fun ω => Y (ω, x)) =ᵐ[P] fun ω => Q (ω, x) := by
      filter_upwards [hGood] with ω hω
      simp [Y, hω]
    exact hYQ.trans (hNsection x hx)
  have hYloc (ω : Ω) : LocallyIntegrable (fun x => Y (ω, x)) volume := by
    by_cases hω : ω ∈ Good
    · rw [locallyIntegrable_iff]
      intro K hK
      obtain ⟨R, hRpos, hR⟩ := hK.isBounded.exists_pos_norm_lt
      obtain ⟨n, hn⟩ := exists_nat_gt R
      let Bn : Set Plane := ball n
      have hsubset : K ⊆ Bn := by
        intro x hx
        have hxR := hR x hx
        change dist x 0 < (n : ℝ) + 1
        rw [dist_zero_right]
        linarith
      have hsqTop : ∫⁻ x : Plane, ENNReal.ofReal (Y (ω, x) ^ 2)
          ∂(volume.restrict Bn) < ⊤ := by
        simpa [sqMass, Bn, ball, Y, hω] using hω n
      have hYsectionMeas : AEStronglyMeasurable (fun x => Y (ω, x))
          (volume.restrict Bn) :=
        (hYmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      have hsqInt : Integrable (fun x : Plane => Y (ω, x) ^ 2)
          (volume.restrict Bn) := by
        exact (lintegral_ofReal_ne_top_iff_integrable
          ((continuous_id.pow 2).comp_aestronglyMeasurable hYsectionMeas)
          (Filter.Eventually.of_forall fun x => sq_nonneg _)).mp hsqTop.ne
      have hBnFinite : volume Bn < ⊤ := by
        dsimp [Bn, ball]
        exact measure_ball_lt_top
      have hconst : Integrable (fun _ : Plane => (1 : ℝ)) (volume.restrict Bn) := by
        exact (integrableOn_const_iff (μ := volume) (s := Bn) (C := (1 : ℝ))).2
          (Or.inr hBnFinite)
      have hmajor : Integrable (fun x : Plane => (1 : ℝ) + Y (ω, x) ^ 2)
          (volume.restrict Bn) := hconst.add hsqInt
      have hYIntBn : IntegrableOn (fun x : Plane => Y (ω, x)) Bn volume := by
        refine hmajor.mono' hYsectionMeas ?_
        filter_upwards [] with x
        rw [Real.norm_eq_abs]
        have hle : |Y (ω, x)| ≤ 1 + Y (ω, x) ^ 2 := by
          nlinarith [sq_nonneg (|Y (ω, x)| - 1 / 2), sq_abs (Y (ω, x))]
        simpa [Real.norm_of_nonneg (by positivity : 0 ≤ 1 + Y (ω, x) ^ 2)] using hle
      exact hYIntBn.mono_set hsubset
    · simpa [Y, hω] using (locallyIntegrable_zero :
        LocallyIntegrable (fun _ : Plane => (0 : ℝ)) volume)
  exact ⟨Y, hYmeas, hYX, hYmom, hYloc, ⟨N, hNmeas, hNzero, hYsection⟩⟩

/-- Joint almost everywhere measurability of a regularized field with bounded initial data. -/
theorem kpzRegularized_joint_aestronglyMeasurable_of_initial
    (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (h₀ : Plane →ᵇ ℝ) :
    AEStronglyMeasurable
      (fun p : Ω × Plane => kpzRegularized P Z t δ h₀ p.2 p.1) (P.prod volume) := by
  let T : ℝ := t - δ
  let M : Ω → Measure (Plane × Plane) := fun ω => Z 0 T ω
  let S : Ω → Measure (Plane × Plane) := fun ω => (M ω).map Prod.swap
  let g : Plane → ℝ := fun y => Real.exp (h₀ y)
  have hTpos : 0 < T := by dsimp [T]; linarith
  have hMmeas : Measurable M := hZ.1 0 T le_rfl hTpos
  have hSmeas : Measurable S :=
    (Measure.measurable_map Prod.swap measurable_swap).comp hMmeas
  have hSlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (S ω) := by
    filter_upwards [hZ.2.1 0 T le_rfl hTpos] with ω hω
    exact locallyFinite_map_homeomorph (Homeomorph.prodComm Plane Plane) (M ω) hω.1
  have hg : Measurable g := by
    exact (Real.continuous_exp.comp h₀.continuous).measurable
  have hgn : ∀ y, 0 ≤ g y := fun y => (Real.exp_pos _).le
  have hVmeas : AEMeasurable
      (fun q : Plane × Ω => Real.log
        (∫ p, heatKernel δ (p.1 - q.1) * g p.2 ∂S q.2)) (volume.prod P) :=
    Critical2DKPZ.JointConvergence.aemeasurable_log_heatPairing_joint
      P S hSmeas hSlocal δ hδ g hg hgn
  have hVswap : AEMeasurable
      (fun p : Ω × Plane => Real.log
        (∫ q, heatKernel δ (q.1 - p.2) * g q.2 ∂S p.1)) (P.prod volume) := by
    simpa only [Function.comp_def, Prod.swap] using
      hVmeas.aestronglyMeasurable.comp_measurePreserving
        (Measure.measurePreserving_swap (μ := P) (ν := volume)) |>.aemeasurable
  let c : ℝ := ∫ ω', Real.log
    (shfPairing Z 0 T (fun _ => (1 : ℝ)) (fun y => heatKernel δ y) ω') ∂P
  have hpair (x : Plane) (ω : Ω) :
      shfPairing Z 0 T (fun y => Real.exp (h₀ y))
          (fun y => heatKernel δ (y - x)) ω =
        ∫ q, heatKernel δ (q.1 - x) * g q.2 ∂S ω := by
    have hmap := integral_map (μ := M ω) measurable_swap.aemeasurable
      (((measurable_heatKernel δ).comp (measurable_fst.sub_const x)).mul
        (hg.comp measurable_snd)).aestronglyMeasurable
    simpa [shfPairing, T, M, S, g, Function.comp_def, mul_comm] using hmap.symm
  have hfield : (fun p : Ω × Plane => kpzRegularized P Z t δ h₀ p.2 p.1) =
      fun p => Real.log
        (∫ q, heatKernel δ (q.1 - p.2) * g q.2 ∂S p.1) - c := by
    funext p
    dsimp [c]
    rw [kpzRegularized, hpair]
  have hmeas : AEMeasurable
      (fun p : Ω × Plane => kpzRegularized P Z t δ h₀ p.2 p.1) (P.prod volume) := by
    rw [hfield]
    exact hVswap.sub aemeasurable_const
  exact hmeas.aestronglyMeasurable

private theorem measurable_log_heatPairing_measure (δ : ℝ) (hδ : 0 < δ) (x : Plane)
    (g : Plane → ℝ) (hg : Measurable g) (hgn : ∀ y, 0 ≤ g y) :
    Measurable (fun μ : Measure (Plane × Plane) =>
      Real.log (∫ p, heatKernel δ (p.1 - x) * g p.2 ∂μ)) := by
  let f : Plane × Plane → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (heatKernel δ (p.1 - x) * g p.2)
  have hf : Measurable f := ENNReal.measurable_ofReal.comp
    (((measurable_heatKernel δ).comp (measurable_fst.sub_const x)).mul
      (hg.comp measurable_snd))
  have hlin : Measurable (fun μ : Measure (Plane × Plane) => ∫⁻ p, f p ∂μ) :=
    Measure.measurable_lintegral hf
  have heq : (fun μ : Measure (Plane × Plane) =>
      ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂μ) =
      fun μ => (∫⁻ p, f p ∂μ).toReal := by
    funext μ
    apply integral_eq_lintegral_of_nonneg_ae
    · exact Filter.Eventually.of_forall fun p =>
        mul_nonneg (heatKernel_nonneg hδ.le _) (hgn p.2)
    · exact (((measurable_heatKernel δ).comp
        (measurable_fst.sub_const x)).mul (hg.comp measurable_snd)).aestronglyMeasurable
  have hlog : (fun μ : Measure (Plane × Plane) =>
      Real.log (∫ p, heatKernel δ (p.1 - x) * g p.2 ∂μ)) =
      fun μ => Real.log ((∫⁻ p, f p ∂μ).toReal) := by
    funext μ
    exact congrArg Real.log (congrFun heq μ)
  rw [hlog]
  exact Real.measurable_log.comp hlin.ennreal_toReal

private theorem kpzRegularized_aemeasurable_of_initial
    (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (h₀ : Plane →ᵇ ℝ) (x : Plane) :
    AEMeasurable (fun ω => kpzRegularized P Z t δ h₀ x ω) P := by
  let g : Plane → ℝ := fun y => Real.exp (h₀ y)
  let T : ℝ := t - δ
  let M : Ω → Measure (Plane × Plane) := fun ω => Z 0 T ω
  let S : Ω → Measure (Plane × Plane) := fun ω => (M ω).map Prod.swap
  have hg : Measurable g := (Real.continuous_exp.comp h₀.continuous).measurable
  have hSmeas : Measurable S :=
    (Measure.measurable_map Prod.swap measurable_swap).comp
      (hZ.1 0 T le_rfl (by dsimp [T]; linarith))
  have hnumS : Measurable (fun ω => Real.log
      (∫ p, heatKernel δ (p.1 - x) * g p.2 ∂S ω)) :=
    (measurable_log_heatPairing_measure δ hδ x g hg
      (fun y => (Real.exp_pos _).le)).comp hSmeas
  have hpair (ω : Ω) :
      shfPairing Z 0 T (fun y => Real.exp (h₀ y))
          (fun y => heatKernel δ (y - x)) ω =
        ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂S ω := by
    have hmap := integral_map (μ := M ω) measurable_swap.aemeasurable
      (((measurable_heatKernel δ).comp (measurable_fst.sub_const x)).mul
        (hg.comp measurable_snd)).aestronglyMeasurable
    simpa [shfPairing, T, M, S, g, Function.comp_def, mul_comm] using hmap.symm
  have hnum : Measurable (fun ω => Real.log
      (shfPairing Z 0 (t - δ) (fun y => Real.exp (h₀ y))
        (fun y => heatKernel δ (y - x)) ω)) := by
    have heq : (fun ω => Real.log
        (shfPairing Z 0 T (fun y => Real.exp (h₀ y))
          (fun y => heatKernel δ (y - x)) ω) ) =
        fun ω => Real.log (∫ p, heatKernel δ (p.1 - x) * g p.2 ∂S ω) := by
      funext ω
      rw [hpair]
    rw [heq]
    exact hnumS
  have hregularized : (fun ω => kpzRegularized P Z t δ h₀ x ω) =
      fun ω => Real.log (shfPairing Z 0 (t - δ) (fun y => Real.exp (h₀ y))
        (fun y => heatKernel δ (y - x)) ω) -
        ∫ ω', Real.log (shfPairing Z 0 (t - δ) (fun _ => (1 : ℝ))
          (fun y => heatKernel δ y) ω') ∂P := by
    funext ω
    rfl
  rw [hregularized]
  exact hnum.aemeasurable.sub aemeasurable_const

private theorem kpzRegularizedReversed_aemeasurable_of_initial
    (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (h₀ : Plane →ᵇ ℝ) (x : Plane) :
    AEMeasurable (fun ω => kpzRegularizedReversed P Z 0 t δ h₀ x ω) P := by
  let g : Plane → ℝ := fun y => Real.exp (h₀ y)
  have hg : Measurable g := (Real.continuous_exp.comp h₀.continuous).measurable
  have hnum : Measurable (fun ω => Real.log
      (shfPairing Z δ t (fun y => heatKernel δ (y - x))
        (fun y => Real.exp (h₀ y)) ω)) := by
    have h := (measurable_log_heatPairing_measure δ hδ x g hg
      (fun y => (Real.exp_pos _).le)).comp (hZ.1 δ t hδ.le (by linarith))
    simpa [Function.comp_def, shfPairing, g, mul_comm] using h
  have hregularized : (fun ω => kpzRegularizedReversed P Z 0 t δ h₀ x ω) =
      fun ω => Real.log (shfPairing Z δ t (fun y => heatKernel δ (y - x))
        (fun y => Real.exp (h₀ y)) ω) -
        ∫ ω', Real.log (shfPairing Z δ t (fun y => heatKernel δ y)
          (fun _ => (1 : ℝ)) ω') ∂P := by
    funext ω
    simp only [kpzRegularizedReversed, zero_add]
  rw [hregularized]
  exact hnum.aemeasurable.sub aemeasurable_const



private def kpzShiftSwappedSHF {Ω : Type u} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (δ : ℝ) : ℝ → ℝ → Ω → Measure (Plane × Plane) := fun s t ω =>
  (Z (s + δ) (t + δ) ω).map Prod.swap

private theorem shfPairing_shiftSwap_eq {Ω : Type u} [MeasurableSpace Ω]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t δ : ℝ)
    (h₀ : Plane →ᵇ ℝ) (x : Plane) (ω : Ω) :
    shfPairing (kpzShiftSwappedSHF Z δ) 0 (t - δ)
        (fun y => Real.exp (h₀ y)) (fun y => heatKernel δ (y - x)) ω =
      shfPairing Z δ t (fun y => heatKernel δ (y - x))
        (fun y => Real.exp (h₀ y)) ω := by
  have hf : AEStronglyMeasurable
      (fun p : Plane × Plane => Real.exp (h₀ p.1) * heatKernel δ (p.2 - x))
      ((Z δ t ω).map Prod.swap) := by
    exact (((Real.continuous_exp.comp h₀.continuous).comp continuous_fst).mul
      ((continuous_heatKernel δ).comp (continuous_snd.sub continuous_const))).aestronglyMeasurable
  have hmap := integral_map (μ := Z δ t ω) measurable_swap.aemeasurable hf
  simpa [shfPairing, kpzShiftSwappedSHF, Function.comp_def, mul_comm] using hmap

private theorem kpzRegularized_shiftSwap_eq_reversed {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t δ : ℝ)
    (h₀ : Plane →ᵇ ℝ) (x : Plane) :
    kpzRegularized P (kpzShiftSwappedSHF Z δ) t δ h₀ x =
      kpzRegularizedReversed P Z 0 t δ h₀ x := by
  funext ω
  rw [kpzRegularized, kpzRegularizedReversed, zero_add]
  rw [shfPairing_shiftSwap_eq Z t δ h₀ x ω]
  have hcenter :
      (∫ ω', Real.log (shfPairing (kpzShiftSwappedSHF Z δ) 0 (t - δ)
        (fun _ => (1 : ℝ)) (fun y => heatKernel δ y) ω') ∂P) =
      ∫ ω', Real.log (shfPairing Z δ t
        (fun y => heatKernel δ y) (fun _ => (1 : ℝ)) ω') ∂P := by
    apply integral_congr_ae
    filter_upwards [] with ω'
    simpa using congrArg Real.log (shfPairing_shiftSwap_eq Z t δ 0 0 ω')
  rw [hcenter]

/-- The bounded initial profile changes the centered regularized field by at most its sup norm. -/
theorem kpzRegularized_shift_bound_ae
    (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (h₀ : Plane →ᵇ ℝ) (x : Plane) :
    ∀ᵐ ω ∂P,
      |kpzRegularized P Z t δ h₀ x ω - kpzRegularized P Z t δ 0 x ω| ≤ ‖h₀‖ := by
  let Zswap := kpzShiftSwappedSHF Z δ
  let gOne : Plane →ᵇ ℝ := BoundedContinuousFunction.const Plane 1
  have hpos : ∀ᵐ ω ∂P,
      0 < shfPairing Z δ t (fun y => heatKernel δ (y - x)) (fun _ => (1 : ℝ)) ω := by
    simpa [gOne] using
      (hsym.2.2.2.2.2.2 δ t δ x (0 : Plane →ᵇ ℝ) hδ.le hδt hδ).1
  have hbaseInt := SHF.Positivity.isCriticalSHF_heat_bounded_pairing_integrable_bound
    ϑ P Z hZ (s := δ) (t := t) (δ := δ) hδ.le hδt hδ x gOne
  have hposSwap : ∀ᵐ ω ∂P,
      0 < shfPairing Zswap 0 (t - δ) (fun y => Real.exp ((0 : Plane →ᵇ ℝ) y))
        (fun y => heatKernel δ (y - x)) ω := by
    filter_upwards [hpos] with ω hω
    have hEq := shfPairing_shiftSwap_eq Z t δ (0 : Plane →ᵇ ℝ) x ω
    have hEq' : shfPairing Zswap 0 (t - δ)
        (fun y => Real.exp ((0 : Plane →ᵇ ℝ) y))
        (fun y => heatKernel δ (y - x)) ω =
      shfPairing Z δ t (fun y => heatKernel δ (y - x)) (fun _ => (1 : ℝ)) ω := by
      simpa [Real.exp_zero] using hEq
    simpa only [hEq'] using hω
  have hfinSwap : ∀ᵐ ω ∂P,
      Integrable (fun p : Plane × Plane => Real.exp ((0 : Plane →ᵇ ℝ) p.1) *
        heatKernel δ (p.2 - x)) (Zswap 0 (t - δ) ω) := by
    filter_upwards [hbaseInt.1] with ω hω
    have hf' : AEStronglyMeasurable
        (fun p : Plane × Plane => heatKernel δ (p.2 - x)) ((Z δ t ω).map Prod.swap) :=
      ((continuous_heatKernel δ).comp (continuous_snd.sub continuous_const)).aestronglyMeasurable
    have hf : AEStronglyMeasurable
        (fun p : Plane × Plane => Real.exp ((0 : Plane →ᵇ ℝ) p.1) *
          heatKernel δ (p.2 - x)) ((Z δ t ω).map Prod.swap) := by
      simpa only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero, one_mul]
        using hf'
    have hmap := (integrable_map_measure hf measurable_swap.aemeasurable).2
      (by simpa [gOne, Real.exp_zero, mul_comm, Function.comp_def] using hω)
    simpa [Zswap, kpzShiftSwappedSHF, gOne, Function.comp_def, Real.exp_zero, mul_comm]
      using hmap
  have hrevBound : ∀ᵐ ω ∂P,
      |kpzRegularizedReversed P Z 0 t δ h₀ x ω -
        kpzRegularizedReversed P Z 0 t δ 0 x ω| ≤ ‖h₀‖ := by
    filter_upwards [hposSwap, hfinSwap] with ω hωpos hωfin
    have hcmp := Assembly.kpzRegularized_comparison P Zswap t δ h₀ 0 x ω hωpos hωfin
    have heq₁ := congrFun (kpzRegularized_shiftSwap_eq_reversed P Z t δ h₀ x) ω
    have heq₀ := congrFun (kpzRegularized_shiftSwap_eq_reversed P Z t δ 0 x) ω
    rw [← heq₁, ← heq₀]
    simpa using hcmp
  let hVec : Fin 2 → Plane →ᵇ ℝ := fun i => if i.val = 0 then h₀ else 0
  let tVec : Fin 2 → ℝ := fun _ => t
  let δVec : Fin 2 → ℝ := fun _ => δ
  let xVec : Fin 2 → Plane := fun _ => x
  let F : Ω → Fin 2 → ℝ := fun ω i =>
    kpzRegularized P Z (tVec i) (δVec i) (hVec i) (xVec i) ω
  let R : Ω → Fin 2 → ℝ := fun ω i =>
    kpzRegularizedReversed P Z (t - tVec i) t (δVec i) (hVec i) (xVec i) ω
  have hparams : ∀ i : Fin 2, 0 < δVec i ∧ δVec i < tVec i ∧ tVec i ≤ t := by
    intro i
    constructor
    · simpa [δVec] using hδ
    constructor
    · simpa [tVec, δVec] using hδt
    · simp [tVec]
  have hLaw : P.map F = P.map R := by
    simpa [F, R, tVec, δVec, xVec] using
      kpzRegularized_reverse_pointLaw_of ϑ P Z hZ hsym t 2 tVec δVec hVec xVec hparams
  have hFmeas : AEMeasurable F P := by
    apply aemeasurable_pi_iff.mpr
    intro i
    fin_cases i
    · simpa [F, hVec, tVec, δVec, xVec] using
        kpzRegularized_aemeasurable_of_initial ϑ P Z hZ hδ hδt h₀ x
    · simpa [F, hVec, tVec, δVec, xVec] using
        kpzRegularized_aemeasurable_of_initial ϑ P Z hZ hδ hδt 0 x
  have hRmeas : AEMeasurable R P := by
    apply aemeasurable_pi_iff.mpr
    intro i
    fin_cases i
    · simpa [R, hVec, tVec, δVec, xVec] using
        kpzRegularizedReversed_aemeasurable_of_initial ϑ P Z hZ hδ hδt h₀ x
    · simpa [R, hVec, tVec, δVec, xVec] using
        kpzRegularizedReversed_aemeasurable_of_initial ϑ P Z hZ hδ hδt 0 x
  let E : Set (Fin 2 → ℝ) := {v | |v 0 - v 1| ≤ ‖h₀‖}
  have hE : MeasurableSet E := by
    apply (isClosed_le
      (continuous_abs.comp ((continuous_apply (0 : Fin 2)).sub (continuous_apply 1)))
      continuous_const).measurableSet
  have hRbound : ∀ᵐ ω ∂P, R ω ∈ E := by
    filter_upwards [hrevBound] with ω hω
    simpa [E, R, hVec, tVec, δVec, xVec] using hω
  have hRpush : ∀ᵐ v ∂P.map R, v ∈ E :=
    (MeasureTheory.ae_map_iff hRmeas hE).2 hRbound
  have hFpush : ∀ᵐ v ∂P.map F, v ∈ E := by
    rw [hLaw]
    exact hRpush
  have hFbound : ∀ᵐ ω ∂P, F ω ∈ E :=
    (MeasureTheory.ae_map_iff hFmeas hE).1 hFpush
  simpa [E, F, tVec, δVec, hVec, xVec] using hFbound

/-- Uniform negative Sobolev moment bound for the centered regularized field. -/
theorem kpzRegularized_flat_negSobolev_moment_le_of
    (hVD : Smoothing.PropVDBound) (ϑ : ℝ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hHeatStartLogInput : HeatStartLogAt ϑ P Z) (hsym : ShfSymmetriesAt ϑ P Z)
    {t : ℝ} (ht : 0 < t) {a : ℝ} (ha : 0 < a) (χ : TestFn) :
    ∃ C : ℝ, ∀ δ : ℝ, 0 < δ → δ < t / 2 →
      ∫⁻ ω, localNegSobolevSq a
        (Distribution.ofFun ⊤ (fun x => kpzRegularized P Z t δ 0 x ω) volume ⊤) χ ∂P ≤
          ENNReal.ofReal C := by
  let p : ℝ := max 2 (a⁻¹ + 1)
  have hp : 1 < p := by
    dsimp [p]
    linarith [le_max_left 2 (a⁻¹ + 1)]
  have hpa : 1 / p < a := by
    have hmax : a⁻¹ + 1 ≤ p := le_max_right _ _
    have hmul : 1 < a * p := by
      have hmul := mul_le_mul_of_nonneg_left hmax ha.le
      nlinarith [ha, mul_inv_cancel₀ ha.ne']
    rw [div_lt_iff₀ (lt_trans zero_lt_one hp)]
    exact hmul
  obtain ⟨Ccov, hcovAll⟩ := kpzRegularized_flat_covariance_le_of hVD ϑ P Z hZ hHeatStartLogInput hsym
    (t₀ := t / 2) (t₁ := t) (by linarith)
  let y₀ : Plane := EuclideanSpace.single 0 (1 : ℝ)
  have hxy₀ : (0 : Plane) ≠ y₀ := by
    intro h
    have hval := congrArg (fun x : Plane => x 0) h
    simp [y₀] at hval
  let δ₀ : ℝ := t / 4
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hδ₀t : δ₀ < t / 2 := by dsimp [δ₀]; linarith
  have hcov₀xy := hcovAll t ⟨by linarith, le_rfl⟩ δ₀ δ₀
    hδ₀ (by linarith) hδ₀ (by linarith) (0 : Plane) y₀ hxy₀
  have hCcov : 0 ≤ Ccov := by
    have henv := CovarianceKernel.covarianceLogEnvelope_pos ((0 : Plane) - y₀)
    have hupper : covariance (kpzRegularized P Z t δ₀ 0 0)
        (kpzRegularized P Z t δ₀ 0 y₀) P ≤
          Ccov * CovarianceKernel.covarianceLogEnvelope ((0 : Plane) - y₀) := by
      simpa [CovarianceKernel.covarianceLogEnvelope] using hcov₀xy.2.2
    by_contra hneg
    have hCneg : Ccov < 0 := lt_of_not_ge hneg
    have hprod : Ccov * CovarianceKernel.covarianceLogEnvelope
        ((0 : Plane) - y₀) < 0 := mul_neg_of_neg_of_pos hCneg henv
    linarith [hcov₀xy.2.1]
  obtain ⟨B, L, A, hB, hL, hA, hpairBase⟩ :=
    lintegral_testFn_pair_heatEnvelope_le χ hp
  let Cpair : ℝ := Ccov * (L * B)
  have hCpair : 0 ≤ Cpair := by dsimp [Cpair]; positivity
  let w0 : ℝ → ℝ := fun u => u ^ (a - 1) * Real.exp (-u)
  let w1 : ℝ → ℝ := fun u => u ^ (a - 1 - 1 / p) * Real.exp (-u)
  let K0 : ℝ≥0∞ := ∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (w0 u)
  let K1 : ℝ≥0∞ := ∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (w1 u)
  have hK0top : K0 < ⊤ := by
    dsimp [K0, w0]
    apply lintegral_rpow_exp_neg_finite
    linarith
  have hK1top : K1 < ⊤ := by
    dsimp [K1, w1]
    apply lintegral_rpow_exp_neg_finite
    linarith
  let R : ℝ≥0∞ := ENNReal.ofReal Cpair *
    (K0 + ENNReal.ofReal A * K1)
  have hRtop : R < ⊤ := by
    dsimp [R]
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    exact ENNReal.add_lt_top.mpr ⟨hK0top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK1top⟩
  let G : ℝ≥0∞ := ENNReal.ofReal ((Real.Gamma a)⁻¹)
  have hGtop : G < ⊤ := by dsimp [G]; exact ENNReal.ofReal_lt_top
  let M : ℝ≥0∞ := G * R
  have hMtop : M < ⊤ := by
    dsimp [M]
    exact ENNReal.mul_lt_top hGtop hRtop
  refine ⟨M.toReal, ?_⟩
  intro δ hδ hδt
  have hδlt : δ < t := by linarith
  obtain ⟨Bmom, hBmom, hMom⟩ :=
    CovarianceKernel.kpzRegularized_uniform_second_moment_of ϑ P Z hZ hsym
      (fun T k s u hst => shfReversal_measureLaw_of ϑ P Z hZ T k s u hst)
      (t := t) (δ := δ) hδ hδlt
  let Xraw : Ω × Plane → ℝ := fun q => kpzRegularized P Z t δ 0 q.2 q.1
  have hXraw : AEStronglyMeasurable Xraw (P.prod volume) := by
    simpa only [Xraw] using
      CovarianceKernel.kpzRegularized_joint_aestronglyMeasurable_of ϑ P Z hZ hδ hδlt
  have hmean0 : (∫ ω, kpzRegularized P Z t δ 0 0 ω ∂P) = 0 := by
    let c : ℝ := ∫ ω, swappedHeatStartLog Z t δ 0 ω ∂P
    have hlogMem : MemLp (swappedHeatStartLog Z t δ 0) 2 P :=
      CovarianceKernel.swappedHeatStartLog_memLp_two_of ϑ P Z hZ hsym
        (fun T k s u hst => shfReversal_measureLaw_of ϑ P Z hZ T k s u hst)
        hδ hδlt 0
    rw [kpzRegularized_eq_swappedHeatStartLog_sub_mean P Z 0]
    rw [integral_sub (hlogMem.integrable (by norm_num)) (integrable_const c)]
    simp [c]
  have hzeroRaw (x : Plane) :
      (∫ ω, kpzRegularized P Z t δ 0 x ω ∂P) = 0 := by
    have hident := kpzRegularized_identDistrib_translate_of ϑ P Z hZ hsym hδ hδlt x x
    have hident0 : IdentDistrib (kpzRegularized P Z t δ 0 x)
        (kpzRegularized P Z t δ 0 0) P P := by
      simpa only [sub_self] using hident
    exact hident0.integral_eq.trans hmean0
  have hMomRaw (x : Plane) : MemLp (fun ω => Xraw (ω, x)) 2 P ∧
      Integrable (fun ω => Xraw (ω, x) ^ 2) P ∧
      (∫ ω, Xraw (ω, x) ^ 2 ∂P) ≤ Bmom := by
    have hx := hMom x
    change MemLp (kpzRegularized P Z t δ 0 x) 2 P ∧
      Integrable (fun ω => kpzRegularized P Z t δ 0 x ω ^ 2) P ∧
      (∫ ω, kpzRegularized P Z t δ 0 x ω ^ 2 ∂P) = Bmom at hx
    simpa [Xraw] using ⟨hx.1, hx.2.1, le_of_eq hx.2.2⟩
  have hzeroRaw' (x : Plane) : (∫ ω, Xraw (ω, x) ∂P) = 0 := by
    simpa [Xraw] using hzeroRaw x
  obtain ⟨Y, hYmeas, hYX, hYmom, hYloc,
      ⟨N, hNmeas, hNzero, hYsection⟩⟩ :=
    measurable_locallyIntegrable_modification_of_pointwise_moments
      P Xraw hXraw Bmom hBmom hMomRaw hzeroRaw'
  let Yfield : Ω → Plane → ℝ := fun ω x => Y (ω, x)
  have hYmeasField : Measurable (fun q : Ω × Plane => Yfield q.1 q.2) := hYmeas
  have hYmomField (x : Plane) : MemLp (Yfield · x) 2 P ∧
      Integrable (fun ω => Yfield ω x ^ 2) P ∧
      (∫ ω, Yfield ω x ^ 2 ∂P) ≤ Bmom ∧
      (∫ ω, Yfield ω x ∂P) = 0 := by
    simpa [Yfield] using hYmom x
  have hYXC (x : Plane) :
      (∫⁻ ω, ENNReal.ofReal (Yfield ω x ^ 2) ∂P) ≤ ENNReal.ofReal Bmom := by
    have hconvert := ofReal_integral_eq_lintegral_ofReal (hYmomField x).2.1
      (Filter.Eventually.of_forall fun ω => sq_nonneg (Yfield ω x))
    calc
      _ = ENNReal.ofReal (∫ ω, Yfield ω x ^ 2 ∂P) := hconvert.symm
      _ ≤ ENNReal.ofReal Bmom := ENNReal.ofReal_le_ofReal (hYmomField x).2.2.1
  let hCsecond : ℝ≥0∞ := ENNReal.ofReal Bmom
  have hCsecondTop : hCsecond < ⊤ := by dsimp [hCsecond]; exact ENNReal.ofReal_lt_top
  have hYLNS := lintegral_localNegSobolevSq_ofFun_eq_covariance_of_uniform_second_moment
    P hYmeasField hYloc χ hCsecondTop hYXC (fun x => (hYmomField x).2.2.2) ha
  have hNae : ∀ᵐ x ∂volume, x ∉ N := by
    rw [ae_iff]
    simpa using hNzero
  have hNpair : ∀ᵐ q : Plane × Plane ∂volume.prod volume,
      q.1 ∉ N ∧ q.2 ∉ N := by
    have hset : MeasurableSet {q : Plane × Plane | q.1 ∉ N ∧ q.2 ∉ N} := by
      exact (hNmeas.compl.preimage measurable_fst).inter
        (hNmeas.compl.preimage measurable_snd)
    rw [Measure.ae_prod_iff_ae_ae hset]
    filter_upwards [hNae] with x hx
    filter_upwards [hNae] with y hy
    exact ⟨hx, hy⟩
  have hneq : ∀ᵐ q : Plane × Plane ∂volume.prod volume, q.1 ≠ q.2 := by
    have hset : MeasurableSet {q : Plane × Plane | q.1 ≠ q.2} :=
      (isClosed_eq continuous_fst continuous_snd).measurableSet.compl
    rw [Measure.ae_prod_iff_ae_ae hset]
    filter_upwards [] with x
    filter_upwards [volume.ae_ne x] with y hy
    exact hy.symm
  have hcovAE : ∀ᵐ q : Plane × Plane ∂volume.prod volume,
      q.1 ≠ q.2 ∧
        0 ≤ covariance (Yfield · q.1) (Yfield · q.2) P ∧
        covariance (Yfield · q.1) (Yfield · q.2) P ≤
          Ccov * CovarianceKernel.covarianceLogEnvelope (q.1 - q.2) := by
    filter_upwards [hNpair, hneq] with q hqN hqneq
    have hEq := CovarianceKernel.covariance_congr_ae P
      (hYmomField q.1).1 (hYmomField q.2).1 (hMomRaw q.1).1 (hMomRaw q.2).1
      (hYsection q.1 hqN.1) (hYsection q.2 hqN.2)
    have hraw := hcovAll t ⟨by linarith, le_rfl⟩ δ δ
      hδ hδt hδ hδt q.1 q.2 hqneq
    have hrawUpper : covariance (fun ω => Xraw (ω, q.1))
        (fun ω => Xraw (ω, q.2)) P ≤
        Ccov * CovarianceKernel.covarianceLogEnvelope (q.1 - q.2) := by
      simpa [Xraw, CovarianceKernel.covarianceLogEnvelope] using hraw.2.2
    rw [hEq]
    exact ⟨hqneq, hraw.2.1, hrawUpper⟩
  have hpairSpatial : ∀ u : ℝ, 0 < u →
      (∫ q : Plane × Plane,
        (heatKernel (2 * u) (q.1 - q.2) * (χ q.1 * χ q.2) *
          covariance (Yfield · q.1) (Yfield · q.2) P) ∂volume.prod volume) ≤
        Cpair * (1 + A * (2 * u) ^ (-1 / p)) := by
    simpa [Cpair, mul_assoc] using
      (kpzRegularized_spatial_covariance_integral_le P Yfield Ccov hCcov hcovAE χ
        B L A hB hL hA hpairBase)
  let w0 : ℝ → ℝ := fun u => u ^ (a - 1) * Real.exp (-u)
  let w1 : ℝ → ℝ := fun u => u ^ (a - 1 - 1 / p) * Real.exp (-u)
  have houter :
      (∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (w0 u) * ENNReal.ofReal
        (∫ q : Plane × Plane,
          (heatKernel (2 * u) (q.1 - q.2) * (χ q.1 * χ q.2) *
            covariance (Yfield · q.1) (Yfield · q.2) P) ∂volume.prod volume)) ≤ R := by
    calc
      _ ≤ ∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal Cpair *
          (ENNReal.ofReal (w0 u) + ENNReal.ofReal A * ENNReal.ofReal (w1 u)) := by
            apply lintegral_mono_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
            have hu' : 0 < u := hu
            have hsp := hpairSpatial u hu'
            have hw0 : 0 ≤ w0 u := by
              dsimp [w0]
              exact mul_nonneg (Real.rpow_nonneg hu'.le _) (Real.exp_pos _).le
            have hpow : (2 * u) ^ (-1 / p) ≤ u ^ (-1 / p) := by
              have hp0 : 0 < p := lt_trans one_pos hp
              have hpinv : 0 < 1 / p := one_div_pos.mpr hp0
              have hpowExp : (-1 : ℝ) / p = -(1 / p) := by ring
              exact Real.rpow_le_rpow_of_nonpos hu' (by nlinarith) (by
                rw [hpowExp]
                exact neg_nonpos.mpr hpinv.le)
            have hpower : w0 u * u ^ (-1 / p) = w1 u := by
              dsimp [w0, w1]
              calc
                u ^ (a - 1) * Real.exp (-u) * u ^ (-1 / p) =
                    (u ^ (a - 1) * u ^ (-1 / p)) * Real.exp (-u) := by ring
                _ = u ^ ((a - 1) + (-1 / p)) * Real.exp (-u) := by
                  rw [← Real.rpow_add hu']
                _ = u ^ (a - 1 - 1 / p) * Real.exp (-u) := by
                  congr 1
                  congr 1
                  ring
            have hreal : w0 u *
                (∫ q : Plane × Plane,
                  (heatKernel (2 * u) (q.1 - q.2) * (χ q.1 * χ q.2) *
                    covariance (Yfield · q.1) (Yfield · q.2) P) ∂volume.prod volume) ≤
                Cpair * (w0 u + A * w1 u) := by
              have hterm : 1 + A * (2 * u) ^ (-1 / p) ≤
                  1 + A * u ^ (-1 / p) := by gcongr
              calc
                _ ≤ w0 u * (Cpair * (1 + A * (2 * u) ^ (-1 / p))) :=
                  mul_le_mul_of_nonneg_left hsp hw0
                _ ≤ w0 u * (Cpair * (1 + A * u ^ (-1 / p))) := by
                  apply mul_le_mul_of_nonneg_left
                  · exact mul_le_mul_of_nonneg_left hterm hCpair
                  · exact hw0
                _ = Cpair * (w0 u + A * (w0 u * u ^ (-1 / p))) := by ring
                _ = Cpair * (w0 u + A * w1 u) := by rw [hpower]
            have hw1 : 0 ≤ w1 u := by
              dsimp [w1]
              exact mul_nonneg (Real.rpow_nonneg hu'.le _) (Real.exp_pos _).le
            have hAw1 : 0 ≤ A * w1 u := mul_nonneg hA hw1
            calc
              _ = ENNReal.ofReal (w0 u *
                  (∫ q : Plane × Plane,
                    (heatKernel (2 * u) (q.1 - q.2) * (χ q.1 * χ q.2) *
                      covariance (Yfield · q.1) (Yfield · q.2) P) ∂volume.prod volume)) :=
                    by rw [← ENNReal.ofReal_mul hw0]
              _ ≤ ENNReal.ofReal (Cpair * (w0 u + A * w1 u)) :=
                    ENNReal.ofReal_le_ofReal hreal
              _ = ENNReal.ofReal Cpair *
                    (ENNReal.ofReal (w0 u) + ENNReal.ofReal A * ENNReal.ofReal (w1 u)) := by
                    rw [ENNReal.ofReal_mul hCpair, ENNReal.ofReal_add hw0 hAw1,
                      ENNReal.ofReal_mul hA]
      _ = R := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_left (by fun_prop : Measurable (fun u : ℝ => ENNReal.ofReal (w0 u)))]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hMofReal : ENNReal.ofReal M.toReal = M := ENNReal.ofReal_toReal hMtop.ne
  have houter' :
      (∫⁻ u : ℝ in Ioi 0,
        ENNReal.ofReal (u ^ (a - 1) * Real.exp (-u)) * ENNReal.ofReal
          (∫ q : Plane × Plane,
            (heatKernel (2 * u) (q.1 - q.2) * (χ q.1 * χ q.2) *
              covariance (Yfield · q.1) (Yfield · q.2) P) ∂volume.prod volume)) ≤ R := by
    simpa [w0] using houter
  have hLNSRaw : ∀ᵐ ω ∂P,
      localNegSobolevSq a (Distribution.ofFun ⊤ (fun x => kpzRegularized P Z t δ 0 x ω)
        volume ⊤) χ =
      localNegSobolevSq a (Distribution.ofFun ⊤ (Yfield ω) volume ⊤) χ := by
    have hsections : ∀ᵐ ω ∂P, (Yfield ω) =ᵐ[volume] fun x => kpzRegularized P Z t δ 0 x ω := by
      filter_upwards [Measure.ae_ae_of_ae_prod hYX] with ω hω
      filter_upwards [hω] with x hx
      simpa [Yfield, Xraw] using hx
    filter_upwards [hsections] with ω hω
    have hdist : Distribution.ofFun ⊤ (Yfield ω) volume ⊤ =
        Distribution.ofFun ⊤ (fun x => kpzRegularized P Z t δ 0 x ω) volume ⊤ := by
      apply Distribution.ofFun_congr_ae
      exact hω.restrict
    rw [hdist]
  rw [lintegral_congr_ae hLNSRaw, hYLNS]
  change G *
      (∫⁻ u : ℝ in Ioi 0,
        ENNReal.ofReal (u ^ (a - 1) * Real.exp (-u)) * ENNReal.ofReal
          (∫ q : Plane × Plane,
            (heatKernel (2 * u) (q.1 - q.2) * (χ q.1 * χ q.2) *
              covariance (Yfield · q.1) (Yfield · q.2) P) ∂volume.prod volume)) ≤
      ENNReal.ofReal M.toReal
  calc
    _ ≤ G * R := mul_le_mul_of_nonneg_left houter' bot_le
    _ = M := rfl
    _ = ENNReal.ofReal M.toReal := hMofReal.symm

/-- The flat regularized field admits a jointly measurable version with locally integrable paths. -/
theorem kpzRegularized_flat_locallyIntegrable_version_of
    (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z)
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) :
    ∃ Y : Ω × Plane → ℝ, Measurable Y ∧
      Y =ᵐ[P.prod volume] (fun q => kpzRegularized P Z t δ 0 q.2 q.1) ∧
      ∀ ω, LocallyIntegrable (fun x => Y (ω, x)) volume := by
  obtain ⟨Bmom, hBmom, hMom⟩ :=
    CovarianceKernel.kpzRegularized_uniform_second_moment_of ϑ P Z hZ hsym
      (fun T k s u hst => shfReversal_measureLaw_of ϑ P Z hZ T k s u hst)
      (t := t) (δ := δ) hδ hδt
  let Xraw : Ω × Plane → ℝ := fun q => kpzRegularized P Z t δ 0 q.2 q.1
  have hXraw : AEStronglyMeasurable Xraw (P.prod volume) := by
    simpa only [Xraw] using
      CovarianceKernel.kpzRegularized_joint_aestronglyMeasurable_of ϑ P Z hZ hδ hδt
  have hmean0 : (∫ ω, kpzRegularized P Z t δ 0 0 ω ∂P) = 0 := by
    let c : ℝ := ∫ ω, swappedHeatStartLog Z t δ 0 ω ∂P
    have hlogMem : MemLp (swappedHeatStartLog Z t δ 0) 2 P :=
      CovarianceKernel.swappedHeatStartLog_memLp_two_of ϑ P Z hZ hsym
        (fun T k s u hst => shfReversal_measureLaw_of ϑ P Z hZ T k s u hst)
        hδ hδt 0
    rw [kpzRegularized_eq_swappedHeatStartLog_sub_mean P Z 0]
    rw [integral_sub (hlogMem.integrable (by norm_num)) (integrable_const c)]
    simp [c]
  have hzeroRaw (x : Plane) :
      (∫ ω, kpzRegularized P Z t δ 0 x ω ∂P) = 0 := by
    have hident := kpzRegularized_identDistrib_translate_of ϑ P Z hZ hsym hδ hδt x x
    have hident0 : IdentDistrib (kpzRegularized P Z t δ 0 x)
        (kpzRegularized P Z t δ 0 0) P P := by
      simpa only [sub_self] using hident
    exact hident0.integral_eq.trans hmean0
  have hMomRaw (x : Plane) : MemLp (fun ω => Xraw (ω, x)) 2 P ∧
      Integrable (fun ω => Xraw (ω, x) ^ 2) P ∧
      (∫ ω, Xraw (ω, x) ^ 2 ∂P) ≤ Bmom := by
    have hx := hMom x
    change MemLp (kpzRegularized P Z t δ 0 x) 2 P ∧
      Integrable (fun ω => kpzRegularized P Z t δ 0 x ω ^ 2) P ∧
      (∫ ω, kpzRegularized P Z t δ 0 x ω ^ 2 ∂P) = Bmom at hx
    simpa [Xraw] using ⟨hx.1, hx.2.1, le_of_eq hx.2.2⟩
  have hzeroRaw' (x : Plane) : (∫ ω, Xraw (ω, x) ∂P) = 0 := by
    simpa [Xraw] using hzeroRaw x
  obtain ⟨Y, hYmeas, hYX, hYmom, hYloc, _⟩ :=
    measurable_locallyIntegrable_modification_of_pointwise_moments
      P Xraw hXraw Bmom hBmom hMomRaw hzeroRaw'
  exact ⟨Y, hYmeas, hYX, hYloc⟩

end Critical2DKPZ.LocalSobolev

end
