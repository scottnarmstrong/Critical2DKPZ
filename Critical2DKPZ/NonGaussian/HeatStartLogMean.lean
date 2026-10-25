/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.HeatStartInverseLower
public import Critical2DKPZ.SmallScales.HeatStartMoments
import Mathlib.Tactic

/-! # The flat heat-start logarithmic mean -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.LocalSobolev Critical2DKPZ.SmallScales
open scoped BoundedContinuousFunction Topology

universe u

namespace Critical2DKPZ.NonGaussian

/-- The flat heat-start logarithm is integrable and its mean equals `-½ log log (1/r) + O(1)`,
uniformly over centers and durations in a fixed compact subset of `(0,∞)`; see KPZ (9.13). -/
theorem heatStartLog_mean_asymp_of (hVD : Smoothing.PropVDBound) (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hHeatStartLogInput : HeatStartLogAt ϑ P Z) (_hsq : HeatStartSqAt P Z) (_hdense : DenseSHFAt ϑ P Z)
    {τ₀ τ₁ : ℝ} (hτ₀ : 0 < τ₀) :
    ∃ C r₀ : ℝ, 0 < r₀ ∧ ∀ s T r : ℝ, 0 ≤ s → τ₀ ≤ T - s → T - s ≤ τ₁ → 0 < r → r < r₀ →
      ∀ x : Plane,
        Integrable (fun ω => Real.log (shfPairing Z s T (fun y => heatKernel r (y - x)) (fun _ => 1) ω)) P ∧
        |∫ ω, Real.log (shfPairing Z s T (fun y => heatKernel r (y - x)) (fun _ => 1) ω) ∂P +
          (1 / 2) * Real.log (Real.log r⁻¹)| ≤ C  := by
  -- Heat-start convergence and the mean identity give the required moment bounds.
  obtain ⟨C₁, r₁, hr₁, hMoments⟩ := heatStartLog_moments_le_of ϑ P Z hZ hsym hHeatStartLogInput hτ₀
  obtain ⟨c, r₂, hc, hr₂, hInverse⟩ := heatStart_inv_integral_ge_of hVD ϑ P Z hZ hsym hHeatStartLogInput hτ₀
  let C : ℝ := |C₁| + |Real.log c| + 1
  let r₀ : ℝ := min r₁ (min r₂ 1)
  have hr₀ : 0 < r₀ := lt_min hr₁ (lt_min hr₂ zero_lt_one)
  refine ⟨C, r₀, hr₀, ?_⟩
  intro s T r hs hτlo hτhi hr hrr₀ x
  have hrr₁ : r ≤ r₁ := hrr₀.le.trans (min_le_left _ _)
  have hrr₂ : r < r₂ := hrr₀.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hr1 : r < 1 := hrr₀.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hLogr : 0 < Real.log r⁻¹ := by
    rw [Real.log_inv]
    exact neg_pos.mpr (Real.log_neg hr hr1)
  have hsT : s < T := by linarith only [hτlo, hτ₀]
  obtain ⟨hLmem, _hMeanNonpos, _hVar, hMeanLower⟩ :=
    hMoments s T r hs hτlo hτhi hr hrr₁ x
  obtain ⟨_hInvInt, hInvLower⟩ := hInverse s T r hs hτlo hτhi hr hrr₂ x
  have hMean := heatStart_integral_eq_one ϑ P Z hZ hs hsT hr x
  have hPackage := hsym.2.2.2.2.2.2 s T r x (0 : Plane →ᵇ ℝ) hs hsT hr
  have hPos : ∀ᵐ ω ∂P, 0 < shfPairing Z s T (fun y => heatKernel r (y - x)) (fun _ => 1) ω := by
    simpa only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] using hPackage.1
  have hE : IsEhrhardType (P.map fun ω => Real.log
      (shfPairing Z s T (fun y => heatKernel r (y - x)) (fun _ => 1) ω)) := by
    simpa only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] using hPackage.2.2
  have hLogInv := (integrable_inv_and_log_integral_inv_le P hMean.1 hPos hMean.2 hE).2
  have hLogLower : Real.log c + Real.log (Real.log r⁻¹) ≤
      Real.log (∫ ω, (shfPairing Z s T (fun y => heatKernel r (y - x)) (fun _ => 1) ω)⁻¹ ∂P) := by
    rw [← Real.log_mul hc.ne' hLogr.ne']
    exact Real.log_le_log (mul_pos hc hLogr) hInvLower
  have hInt : Integrable (fun ω => Real.log
      (shfPairing Z s T (fun y => heatKernel r (y - x)) (fun _ => 1) ω)) P :=
    hLmem.integrable (by norm_num)
  refine ⟨hInt, abs_le.mpr ⟨?_, ?_⟩⟩
  · have hC₁ : C₁ ≤ |C₁| := le_abs_self _
    have hAbsLog : 0 ≤ |Real.log c| := abs_nonneg _
    have hAbsC₁ : 0 ≤ |C₁| := abs_nonneg _
    change -2 * (∫ ω, Real.log (shfPairing Z s T (fun y => heatKernel r (y - x))
      (fun _ => 1) ω) ∂P) ≤ Real.log (Real.log r⁻¹) + C₁ at hMeanLower
    dsimp [C]
    linarith only [hMeanLower, hC₁, hAbsLog, hAbsC₁]
  · have hLogc : -|Real.log c| ≤ Real.log c := neg_abs_le _
    have hAbsLog : 0 ≤ |Real.log c| := abs_nonneg _
    have hAbsC₁ : 0 ≤ |C₁| := abs_nonneg _
    dsimp [C]
    linarith only [hLogLower, hLogInv, hLogc, hAbsLog, hAbsC₁]

end Critical2DKPZ.NonGaussian

end
