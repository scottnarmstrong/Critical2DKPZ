/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.HeatStartLogMean
public import Critical2DKPZ.NonGaussian.CompactHeatEhrhard
public import Critical2DKPZ.NonGaussian.HeatStartSemigroupMean
public import Critical2DKPZ.NonGaussian.HeatConvolutionLower
import Mathlib.Tactic

/-! # Uniform logarithmic lower means for compact terminals -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.LocalSobolev Critical2DKPZ.SmallScales Critical2DKPZ.SHF.Positivity
open scoped CompactlySupported BoundedContinuousFunction Topology

universe u

namespace Critical2DKPZ.NonGaussian

/-- The compact-terminal heat-start logarithm is integrable and its mean is at least
`-½ log log (1/r) - C`, uniformly over starting centers in a compact set for sufficiently small `r`. -/
theorem heatStartLog_mean_ge_of (hVD : Smoothing.PropVDBound) (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hHeatStartLogInput : HeatStartLogAt ϑ P Z) (hsq : HeatStartSqAt P Z) (hdense : DenseSHFAt ϑ P Z)
    {t : ℝ} (ht : 0 < t) (φ₀ : C_c(Plane, ℝ)) (hφ₀ : ∀ y, 0 ≤ φ₀ y ∧ φ₀ y ≤ 1) (hφ₀' : φ₀ ≠ 0)
    (K : Set Plane) (hK : IsCompact K) :
    ∃ C r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ x ∈ K,
      Integrable (fun ω => Real.log (shfPairing Z r t (fun y => heatKernel r (y - x)) φ₀ ω)) P ∧
      -(1 / 2) * Real.log (Real.log r⁻¹) - C ≤
        ∫ ω, Real.log (shfPairing Z r t (fun y => heatKernel r (y - x)) φ₀ ω) ∂P  := by
  have hHalf : 0 < t / 2 := by positivity
  obtain ⟨_Cflat, rflat, hrflat, _hFlat⟩ :=
    heatStartLog_mean_asymp_of hVD ϑ P Z hZ hsym hHeatStartLogInput hsq hdense (τ₀ := t / 2) (τ₁ := t) hHalf
  obtain ⟨C₂, r₂, hr₂, hSecond⟩ := hsq (τ₀ := t / 2) (τ₁ := t) hHalf
  obtain ⟨c, hc, hMeanLower⟩ := exists_pos_heat_convolution_lower ht φ₀ (fun y => (hφ₀ y).1) hφ₀' K hK
  let Cp : ℝ := |C₂| + 1
  let C : ℝ := |Real.log (1 + Cp)| + 2 * |Real.log c| + 1
  let r₀ : ℝ := min r₂ (min rflat (min (t / 2) (Real.exp (-1))))
  have hr₀ : 0 < r₀ := lt_min hr₂ (lt_min hrflat (lt_min hHalf (Real.exp_pos _)))
  refine ⟨C, r₀, hr₀, ?_⟩
  intro r hr hrr₀ x hx
  have hrr₂ : r ≤ r₂ := hrr₀.le.trans (min_le_left _ _)
  have hrHalf : r < t / 2 := hrr₀.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrExp : r < Real.exp (-1) := hrr₀.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hrt : r < t := by linarith only [hrHalf, ht]
  have hDuration : t / 2 ≤ t - r := by linarith only [hrHalf]
  have hDurationHi : t - r ≤ t := sub_le_self _ hr.le
  have hL : 1 ≤ Real.log r⁻¹ := by
    have h := (Real.log_lt_iff_lt_exp hr).mpr hrExp
    rw [Real.log_inv]
    linarith only [h]
  let V : Ω → ℝ := shfPairing Z r t (fun y => heatKernel r (y - x)) φ₀
  let A : Ω → ℝ := shfPairing Z r t (fun y => heatKernel r (y - x)) (fun _ => 1)
  have hVmem : MemLp V 2 P := memLp_heatStart_bounded ϑ P Z hZ hr.le hrt hr x φ₀.toBoundedContinuousFunction
  obtain ⟨hAmem, hASecond⟩ := hSecond r t r hr.le hDuration hDurationHi hr hrr₂ x
  have hVPackage := heatStart_cc_pairing_pos_isEhrhardType ϑ P Z hZ hr.le hrt hr x φ₀
    (fun y => (hφ₀ y).1) hφ₀'
  have hMeanEq : (∫ ω, V ω ∂P) = ∫ y, heatKernel t (y - x) * φ₀ y := by
    have h := heatStart_integral_eq_semigroup ϑ P Z hZ hr.le hrt hr x φ₀.toBoundedContinuousFunction
      (fun y => (hφ₀ y).1)
    simpa only [V, shfPairing, show r + (t - r) = t by ring,
      CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply] using h
  have hMeanC : c ≤ ∫ ω, V ω ∂P := hMeanEq.symm ▸ (hMeanLower x hx).2
  have hMeanPos : 0 < ∫ ω, V ω ∂P := hc.trans_le hMeanC
  have hPairV := isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hr.le hrt hr x φ₀.toBoundedContinuousFunction
  have hPairA := isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hr.le hrt hr x (1 : Plane →ᵇ ℝ)
  have hVA : ∀ᵐ ω ∂P, V ω ≤ A ω := by
    filter_upwards [hPairV.1, hPairA.1] with ω hVω hAω
    apply integral_mono_ae hVω hAω
    exact Filter.Eventually.of_forall fun p =>
      mul_le_mul_of_nonneg_left (hφ₀ p.2).2 (heatKernel_nonneg hr.le _)
  have hSq : (∫ ω, V ω ^ 2 ∂P) ≤ 1 + Cp * Real.log r⁻¹ := by
    calc
      _ ≤ ∫ ω, A ω ^ 2 ∂P := by
        apply integral_mono_ae hVmem.integrable_sq hAmem.integrable_sq
        filter_upwards [hVA, hVPackage.1] with ω hω hVω
        exact (sq_le_sq₀ hVω.le (hVω.le.trans hω)).mpr hω
      _ ≤ 1 + C₂ * Real.log r⁻¹ := hASecond
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right
        ((le_abs_self C₂).trans (le_add_of_nonneg_right zero_le_one)) (zero_le_one.trans hL))
  have hQpos : 0 < ∫ ω, V ω ^ 2 ∂P := by
    have hVar := variance_nonneg V P
    rw [variance_eq_sub hVmem] at hVar
    exact lt_of_lt_of_le (sq_pos_of_pos hMeanPos) (sub_nonneg.mp hVar)
  have hCp : 0 ≤ Cp := by dsimp [Cp]; positivity
  have hOneCp : 0 < 1 + Cp := by positivity
  have hSqProduct : (∫ ω, V ω ^ 2 ∂P) ≤ Real.log r⁻¹ * (1 + Cp) := by
    calc
      _ ≤ 1 + Cp * Real.log r⁻¹ := hSq
      _ ≤ Real.log r⁻¹ + Cp * Real.log r⁻¹ := add_le_add hL le_rfl
      _ = Real.log r⁻¹ * (1 + Cp) := by ring
  have hLogSq : Real.log (∫ ω, V ω ^ 2 ∂P) ≤ Real.log (Real.log r⁻¹) + Real.log (1 + Cp) := by
    have h := Real.log_le_log hQpos hSqProduct
    rwa [Real.log_mul (ne_of_gt (lt_of_lt_of_le zero_lt_one hL)) hOneCp.ne'] at h
  have hLogMean : Real.log c ≤ Real.log (∫ ω, V ω ∂P) := Real.log_le_log hc hMeanC
  have hComparison := ehrhard_log_variable_moment_comparison P hVmem hVPackage.1 hMeanPos hVPackage.2.2
  refine ⟨hComparison.1, ?_⟩
  have hAbs1 := le_abs_self (Real.log (1 + Cp))
  have hAbs2 := neg_abs_le (Real.log c)
  have hNonneg1 := abs_nonneg (Real.log (1 + Cp))
  have hNonneg2 := abs_nonneg (Real.log c)
  have hLower := hComparison.2.2.2
  dsimp [C]
  linarith only [hLogSq, hLogMean, hLower, hAbs1, hAbs2, hNonneg1, hNonneg2]

end Critical2DKPZ.NonGaussian

end
