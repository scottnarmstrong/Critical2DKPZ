/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.EhrhardNormalization
public import Critical2DKPZ.EhrhardType.WeakClosure
public import Critical2DKPZ.SHF.Positivity.ProbabilityClosure
import Mathlib.Tactic

/-! # Strict positivity and Ehrhard logarithmic laws under a positive mean bound -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Positivity
open scoped ENNReal Topology

namespace Critical2DKPZ.NonGaussian

/-- An almost-sure measurable limit of positive square-integrable variables with Ehrhard logarithmic laws
is almost surely positive and has an Ehrhard logarithmic law if their means are uniformly positive
and their second moments are uniformly bounded. -/
theorem positive_isEhrhardType_of_ae_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (hXpos : ∀ n, ∀ᵐ ω ∂P, 0 < X n ω)
    (hXE : ∀ n, IsEhrhardType (P.map fun ω => Real.log (X n ω)))
    (hY : AEMeasurable Y P) (hConv : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)))
    {m Q : ℝ} (hm : 0 < m) (hMean : ∀ n, m ≤ ∫ ω, X n ω ∂P)
    (hSecond : ∀ n, (∫ ω, X n ω ^ 2 ∂P) ≤ Q) :
    (∀ᵐ ω ∂P, 0 < Y ω) ∧ AEMeasurable (fun ω => Real.log (Y ω)) P ∧
      IsEhrhardType (P.map fun ω => Real.log (Y ω)) := by
  have hQ : 0 ≤ Q := (integral_nonneg fun ω => sq_nonneg (X 0 ω)).trans (hSecond 0)
  have hInvBound (n : ℕ) : Integrable (fun ω => (X n ω)⁻¹) P ∧
      (∫ ω, (X n ω)⁻¹ ∂P) ≤ Q / m ^ 3 := by
    have hnMean : 0 < ∫ ω, X n ω ∂P := hm.trans_le (hMean n)
    have h := ehrhard_log_variable_moment_comparison P (hX n) (hXpos n) hnMean (hXE n)
    refine ⟨h.2.1, h.2.2.1.trans ?_⟩
    calc
      (∫ ω, X n ω ^ 2 ∂P) / (∫ ω, X n ω ∂P) ^ 3 ≤ Q / (∫ ω, X n ω ∂P) ^ 3 :=
        div_le_div_of_nonneg_right (hSecond n) (pow_pos hnMean 3).le
      _ ≤ Q / m ^ 3 := div_le_div_of_nonneg_left hQ (pow_pos hm 3)
        (pow_le_pow_left₀ hm.le (hMean n) 3)
  have hLinBound (n : ℕ) : (∫⁻ ω, (ENNReal.ofReal (X n ω))⁻¹ ∂P) ≤ ENNReal.ofReal (Q / m ^ 3) := by
    have hEq : (fun ω => (ENNReal.ofReal (X n ω))⁻¹) =ᵐ[P]
        fun ω => ENNReal.ofReal ((X n ω)⁻¹) := by
      filter_upwards [hXpos n] with ω hω
      exact (ENNReal.ofReal_inv_of_pos hω).symm
    calc
      _ = ∫⁻ ω, ENNReal.ofReal ((X n ω)⁻¹) ∂P := lintegral_congr_ae hEq
      _ = ENNReal.ofReal (∫ ω, (X n ω)⁻¹ ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal (hInvBound n).1
          ((hXpos n).mono fun _ hω => inv_nonneg.mpr hω.le)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hInvBound n).2
  have hDist : TendstoInDistribution X atTop Y (fun _ => P) P :=
    tendstoInDistribution_of_ae_tendsto (fun n => (hX n).aemeasurable) hY hConv
  have hFatou := lintegral_inv_le_liminf_of_tendstoInDistribution hDist
  have hLiminf : atTop.liminf (fun n => ∫⁻ ω, (ENNReal.ofReal (X n ω))⁻¹ ∂P) ≤
      ENNReal.ofReal (Q / m ^ 3) := by
    refine liminf_le_of_le (by isBoundedDefault) (fun b hb => ?_)
    obtain ⟨n, hn⟩ := hb.exists
    exact hn.trans (hLinBound n)
  have hPos : ∀ᵐ ω ∂P, 0 < Y ω := ae_pos_of_finite_lintegral_inverse hY
    ((hFatou.trans hLiminf).trans_lt ENNReal.ofReal_lt_top)
  have hLogMeas : AEMeasurable (fun ω => Real.log (Y ω)) P :=
    Real.measurable_log.comp_aemeasurable hY
  have hLogDist := tendstoInDistribution_log_of_ne_zero hDist (hPos.mono fun _ h => h.ne')
  let ν : ℕ → ProbabilityMeasure ℝ := fun n => ⟨P.map (fun ω => Real.log (X n ω)), inferInstance⟩
  let ν' : ProbabilityMeasure ℝ := ⟨P.map (fun ω => Real.log (Y ω)), inferInstance⟩
  refine ⟨hPos, hLogMeas, ?_⟩
  exact EhrhardType.isEhrhardType_of_tendsto ν ν' hLogDist.tendsto hXE

end Critical2DKPZ.NonGaussian

end
