/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.GaussianConvexity.EhrhardMomentBounds
public import Critical2DKPZ.EhrhardType.Moments
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-! # The inverse-moment side of the log-mean comparison -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.NonGaussian

/-- For a positive integrable mean-one variable with an Ehrhard logarithmic law,
the inverse is integrable and `log E[Y⁻¹] ≤ -2 E[log Y]`. -/
theorem integrable_inv_and_log_integral_inv_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY : Integrable Y P) (hpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hmean : ∫ ω, Y ω ∂P = 1)
    (hE : IsEhrhardType (P.map fun ω => Real.log (Y ω))) :
    Integrable (fun ω => (Y ω)⁻¹) P ∧
      Real.log (∫ ω, (Y ω)⁻¹ ∂P) ≤ -2 * ∫ ω, Real.log (Y ω) ∂P := by
  let L : Ω → ℝ := fun ω => Real.log (Y ω)
  have hL : AEMeasurable L P := Real.measurable_log.comp_aemeasurable hY.aemeasurable
  have hExp : (fun ω => Real.exp (L ω)) =ᵐ[P] Y := by
    filter_upwards [hpos] with ω hω
    exact Real.exp_log hω
  have hInv : (fun ω => Real.exp (-(1 : ℝ) * L ω)) =ᵐ[P] fun ω => (Y ω)⁻¹ := by
    filter_upwards [hpos] with ω hω
    simp only [neg_one_mul, Real.exp_neg, L, Real.exp_log hω]
  have hExpInt : Integrable (fun r : ℝ => Real.exp r) (P.map L) :=
    (integrable_map_measure (by fun_prop) hL).2 (hY.congr hExp.symm)
  have hExpMean : ∫ r, Real.exp r ∂P.map L = 1 := by
    rw [integral_map hL (by fun_prop), integral_congr_ae hExp, hmean]
  have hInvLaw := EhrhardType.integrable_exp_mul_of_isEhrhardType hE
    (q := -(1 : ℝ)) (by norm_num)
  have hInvInt : Integrable (fun ω => (Y ω)⁻¹) P :=
    ((integrable_map_measure (by fun_prop) hL).1 hInvLaw).congr hInv
  have hVar := GaussianConvexity.variance_le_neg_two_mean hE hExpInt hExpMean
  have hNeg := GaussianConvexity.log_negative_moment_le hE hExpInt (p := 1) (by norm_num)
  have hInvMean : (∫ r, Real.exp (-(1 : ℝ) * r) ∂P.map L) = ∫ ω, (Y ω)⁻¹ ∂P := by
    rw [integral_map hL (by fun_prop)]
    exact integral_congr_ae hInv
  have hLogMean : (∫ r : ℝ, r ∂P.map L) = ∫ ω, Real.log (Y ω) ∂P :=
    integral_map hL (by fun_prop)
  rw [hInvMean, hLogMean] at hNeg
  rw [hLogMean] at hVar
  refine ⟨hInvInt, ?_⟩
  linarith only [hNeg, hVar]

end Critical2DKPZ.NonGaussian

end
