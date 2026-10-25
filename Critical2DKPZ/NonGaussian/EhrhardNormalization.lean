/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.GaussianConvexity.EhrhardMomentBounds
public import Critical2DKPZ.EhrhardType.Characterization
public import Critical2DKPZ.EhrhardType.Moments
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-! # Normalization of positive variables with Ehrhard logarithmic law -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.NonGaussian

/-- Translating an Ehrhard law preserves its monotone convex Gaussian representation. -/
theorem isEhrhardType_map_add_const {μ : Measure ℝ} (hμ : IsEhrhardType μ) (c : ℝ) :
    IsEhrhardType (μ.map fun x => x + c) := by
  obtain ⟨h, hh, hc, rfl⟩ := EhrhardType.exists_monotone_convex_representative hμ
  have hadd : Measurable (fun x : ℝ => x + c) := by fun_prop
  rw [Measure.map_map hadd hh.measurable]
  exact EhrhardType.isEhrhardType_map_of_monotone_convex (hh.add_const c) (hc.add_const c)

/-- For a positive square-integrable variable with an Ehrhard logarithmic law, its inverse
and logarithm are integrable, and their means are bounded in terms of its first two moments. -/
theorem ehrhard_log_variable_moment_comparison {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY : MemLp Y 2 P) (hpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hMean : 0 < ∫ ω, Y ω ∂P)
    (hE : IsEhrhardType (P.map fun ω => Real.log (Y ω))) :
    Integrable (fun ω => Real.log (Y ω)) P ∧
      Integrable (fun ω => (Y ω)⁻¹) P ∧
      (∫ ω, (Y ω)⁻¹ ∂P) ≤ (∫ ω, Y ω ^ 2 ∂P) / (∫ ω, Y ω ∂P) ^ 3 ∧
      -(1 / 2 : ℝ) * Real.log (∫ ω, Y ω ^ 2 ∂P) +
        2 * Real.log (∫ ω, Y ω ∂P) ≤ ∫ ω, Real.log (Y ω) ∂P := by
  let M : ℝ := ∫ ω, Y ω ∂P
  let Q : ℝ := ∫ ω, Y ω ^ 2 ∂P
  let L : Ω → ℝ := fun ω => Real.log (Y ω)
  let U : Ω → ℝ := fun ω => L ω - Real.log M
  have hM : 0 < M := hMean
  have hYInt : Integrable Y P := hY.integrable (by norm_num)
  have hL : AEMeasurable L P := Real.measurable_log.comp_aemeasurable hY.aemeasurable
  have hU : AEMeasurable U P := hL.sub aemeasurable_const
  have hExpL (ω : Ω) (hω : 0 < Y ω) : Real.exp (L ω) = Y ω := Real.exp_log hω
  have hExpLInt : Integrable (fun z : ℝ => Real.exp z) (P.map L) := by
    apply (integrable_map_measure (by fun_prop) hL).mpr
    exact hYInt.congr (hpos.mono fun ω hω => (hExpL ω hω).symm)
  have hLInt : Integrable L P :=
    (integrable_map_measure (by fun_prop) hL).mp (EhrhardType.integrable_id_of_isEhrhardType hE hExpLInt)
  have hInvLaw := EhrhardType.integrable_exp_mul_of_isEhrhardType hE (q := -(1 : ℝ)) (by norm_num)
  have hInvEq : (fun ω => Real.exp (-(1 : ℝ) * L ω)) =ᵐ[P] fun ω => (Y ω)⁻¹ := by
    filter_upwards [hpos] with ω hω
    rw [neg_one_mul, Real.exp_neg, hExpL ω hω]
  have hInvInt : Integrable (fun ω => (Y ω)⁻¹) P :=
    ((integrable_map_measure (by fun_prop) hL).mp hInvLaw).congr hInvEq
  have hUEq : P.map U = (P.map L).map (fun z : ℝ => z + -Real.log M) := by
    have hshift : Measurable (fun z : ℝ => z + -Real.log M) := by fun_prop
    rw [AEMeasurable.map_map_of_aemeasurable hshift.aemeasurable hL]
    rfl
  have hUE : IsEhrhardType (P.map U) := by
    rw [hUEq]
    exact isEhrhardType_map_add_const hE _
  have hExpU : (fun ω => Real.exp (U ω)) =ᵐ[P] fun ω => Y ω / M := by
    filter_upwards [hpos] with ω hω
    change Real.exp (L ω - Real.log M) = Y ω / M
    rw [Real.exp_sub, hExpL ω hω, Real.exp_log hM]
  have hExpUInt : Integrable (fun z : ℝ => Real.exp z) (P.map U) :=
    (integrable_map_measure (by fun_prop) hU).mpr ((hYInt.div_const M).congr hExpU.symm)
  have hExpUMean : ∫ z, Real.exp z ∂P.map U = 1 := by
    rw [integral_map hU (by fun_prop), integral_congr_ae hExpU, integral_div]
    exact div_self hM.ne'
  have hExp2U : (fun ω => Real.exp (2 * U ω)) =ᵐ[P] fun ω => Y ω ^ 2 / M ^ 2 := by
    filter_upwards [hpos] with ω hω
    have hPoint : Real.exp (U ω) = Y ω / M := by
      change Real.exp (L ω - Real.log M) = Y ω / M
      rw [Real.exp_sub, hExpL ω hω, Real.exp_log hM]
    calc
      Real.exp (2 * U ω) = Real.exp (U ω) ^ 2 := by rw [two_mul, Real.exp_add, pow_two]
      _ = _ := by rw [hPoint, div_pow]
  have hExp2UInt : Integrable (fun z : ℝ => Real.exp (2 * z)) (P.map U) :=
    (integrable_map_measure (by fun_prop) hU).mpr ((hY.integrable_sq.div_const (M ^ 2)).congr hExp2U.symm)
  have hExp2UMean : (∫ z, Real.exp (2 * z) ∂P.map U) = Q / M ^ 2 := by
    rw [integral_map hU (by fun_prop), integral_congr_ae hExp2U, integral_div]
  have hNegU : (fun ω => Real.exp (-(1 : ℝ) * U ω)) =ᵐ[P] fun ω => M * (Y ω)⁻¹ := by
    filter_upwards [hpos] with ω hω
    change Real.exp (-(1 : ℝ) * (L ω - Real.log M)) = M * (Y ω)⁻¹
    rw [neg_one_mul, Real.exp_neg, Real.exp_sub, hExpL ω hω, Real.exp_log hM, inv_div]
    exact div_eq_mul_inv _ _
  have hNegUMean : (∫ z, Real.exp (-(1 : ℝ) * z) ∂P.map U) = M * ∫ ω, (Y ω)⁻¹ ∂P := by
    rw [integral_map hU (by fun_prop), integral_congr_ae hNegU, integral_const_mul]
  have hLogMean : (∫ z : ℝ, z ∂P.map U) = (∫ ω, L ω ∂P) - Real.log M := by
    rw [integral_map hU (by fun_prop)]
    change (∫ ω, L ω - Real.log M ∂P) = _
    rw [integral_sub hLInt (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul]
  have hNegBound := GaussianConvexity.negative_moment_le_second_moment_rpow hUE hExpUInt hExpUMean
    hExp2UInt (p := 1) (by norm_num)
  rw [hNegUMean, hExp2UMean] at hNegBound
  norm_num at hNegBound
  have hLogBound := GaussianConvexity.neg_mean_le_log_second_moment hUE hExpUInt hExpUMean hExp2UInt
  rw [hLogMean, hExp2UMean] at hLogBound
  have hQ : 0 < Q := by
    have hv := variance_nonneg Y P
    rw [variance_eq_sub hY] at hv
    change 0 ≤ Q - M ^ 2 at hv
    exact lt_of_lt_of_le (sq_pos_of_pos hM) (sub_nonneg.mp hv)
  rw [Real.log_div hQ.ne' (pow_ne_zero _ hM.ne'), Real.log_pow] at hLogBound
  refine ⟨hLInt, hInvInt, ?_, ?_⟩
  · apply (le_div_iff₀ (pow_pos hM 3)).mpr
    have h := (le_div_iff₀ (pow_pos hM 2)).mp hNegBound
    calc
      (∫ ω, (Y ω)⁻¹ ∂P) * M ^ 3 = (M * ∫ ω, (Y ω)⁻¹ ∂P) * M ^ 2 := by ring
      _ ≤ Q := h
  · change -(1 / 2 : ℝ) * Real.log Q + 2 * Real.log M ≤ ∫ ω, L ω ∂P
    linarith only [hLogBound]

end Critical2DKPZ.NonGaussian

end
