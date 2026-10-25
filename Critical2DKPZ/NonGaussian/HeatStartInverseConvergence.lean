/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.Inputs
public import Critical2DKPZ.NonGaussian.HeatStartInverseUniform
public import Critical2DKPZ.JointConvergence.MomentConvergence
import Mathlib.Tactic

/-! # Convergence of inverse heat-start moments -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.LocalSobolev
open scoped BoundedContinuousFunction Topology

universe u

namespace Critical2DKPZ.NonGaussian

/-- The log-law convergence and the inverse-square bound imply convergence
of inverse first moments. The limit inverse is integrable. -/
theorem heatStart_inv_integral_tendsto_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hHeatStartLogInput : HeatStartLogAt ϑ P Z)
    {s T δ : ℝ} (hs : 0 ≤ s) (hsT : s < T) (hδ : 0 < δ) (x : Plane) :
    Integrable (fun ω => (shfPairing Z s T (fun y => heatKernel δ (y - x)) (fun _ => 1) ω)⁻¹) P ∧
      Tendsto (fun N : ℕ => ∫ ω, (profileP2Fun (criticalBeta ϑ N)
        (evenCeil (N * s)) (evenCeil (N * T))
        (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x))
        (cellAverage N fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω)⁻¹ ∂disorderLaw)
        atTop (𝓝 (∫ ω, (shfPairing Z s T (fun y => heatKernel δ (y - x)) (fun _ => 1) ω)⁻¹ ∂P)) := by
  let X : ℕ → Disorder → ℝ := fun N => profileP2Fun (criticalBeta ϑ N)
    (evenCeil (N * s)) (evenCeil (N * T))
    (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x))
    (cellAverage N fun y => Real.exp ((0 : Plane →ᵇ ℝ) y))
  let Y : Ω → ℝ := shfPairing Z s T (fun y => heatKernel δ (y - x)) (fun _ => 1)
  let Xflat : ℕ → Disorder → ℝ := fun N => profileP2Fun (criticalBeta ϑ N)
    (evenCeil (N * s)) (evenCeil (N * T))
    (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x)) (fun _ => 1)
  have hK := hHeatStartLogInput T 0 1 (fun _ => s) (fun _ => δ) (fun _ => x)
    (fun _ => ⟨hs, hsT, hδ⟩)
  have hYpos : ∀ᵐ ω ∂P, 0 < Y ω := by
    simpa only [Y, BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] using hK.1 0
  have hLogDist : TendstoInDistribution (fun N ω => Real.log (X N ω)) atTop
      (fun ω => Real.log (Y ω)) (fun _ => disorderLaw) P := by
    simpa only [X, Y, BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero,
      Function.comp_def] using hK.2.1.continuous_comp (continuous_apply (0 : Fin 1))
  have hInvDist : TendstoInDistribution (fun N ω => Real.exp (-Real.log (X N ω))) atTop
      (fun ω => Real.exp (-Real.log (Y ω))) (fun _ => disorderLaw) P :=
    hLogDist.continuous_comp (g := fun z : ℝ => Real.exp (-z))
      (Real.continuous_exp.comp continuous_neg)
  have hLimitEq : (fun ω => Real.exp (-Real.log (Y ω))) =ᵐ[P] fun ω => (Y ω)⁻¹ := by
    filter_upwards [hYpos] with ω hω
    rw [Real.exp_neg, Real.exp_log hω]
  have hCellEq (N : ℕ) (hN : 1 ≤ N) (ω : Disorder) : X N ω = Xflat N ω := by
    have hab : evenCeil (N * s) ≤ evenCeil (N * T) :=
      evenCeil_mono (mul_le_mul_of_nonneg_left hsT.le (Nat.cast_nonneg _))
    have hd : Even (evenCeil (N * T) - evenCeil (N * s)) := by
      exact_mod_cast ((show Even ((evenCeil (N * T) : ℤ)) from by exact_mod_cast evenCeil_even (N * T)).sub
        (show Even ((evenCeil (N * s) : ℤ)) from by exact_mod_cast evenCeil_even (N * s)))
    dsimp [X, Xflat]
    simp only [Real.exp_zero]
    exact heatStartWalkProfile_cellAverage_one_eq _ (by omega) hab (evenCeil_even _) hd x ω
  have hFlatPos (N : ℕ) (ω : Disorder) : 0 < Xflat N ω := by
    apply OnePoint.profileP2Fun_pos_of_normalized _ _ _ _
      (Polymer.endpoints (latticePoint N x) (evenCeil (N * δ)))
    · exact fun w hw => Polymer.srwKernel_eq_zero_of_not_mem _ _ _ hw
    · exact fun w => Polymer.kernel_nonneg _ _
    · exact Polymer.sum_srwKernel_endpoints _ _
  have hSeqEq : ∀ᶠ N : ℕ in atTop, ∀ ω : Disorder,
      Real.exp (-Real.log (X N ω)) = (X N ω)⁻¹ := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    intro ω
    rw [Real.exp_neg, Real.exp_log (by rw [hCellEq N hN]; exact hFlatPos N ω)]
  obtain ⟨B, _hB, hBound⟩ := exists_heatStartWalkProfile_inv_sq_bound ϑ hs hsT hδ
  have hInt : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => |Real.exp (-Real.log (X N ω))| ^ (2 : ℝ)) disorderLaw := by
    filter_upwards [hBound, hSeqEq, eventually_ge_atTop 1] with N hN hEq hN1
    have he (ω : Disorder) : |Real.exp (-Real.log (X N ω))| ^ (2 : ℝ) = (Xflat N ω)⁻¹ ^ 2 := by
      rw [abs_of_pos (Real.exp_pos _), Real.rpow_two, hEq ω, hCellEq N hN1]
    exact (hN x).1.congr (Filter.Eventually.of_forall fun ω => (he ω).symm)
  have hUpper : ∀ᶠ N : ℕ in atTop,
      (∫ ω, |Real.exp (-Real.log (X N ω))| ^ (2 : ℝ) ∂disorderLaw) ≤ B := by
    filter_upwards [hBound, hSeqEq, eventually_ge_atTop 1] with N hN hEq hN1
    have he (ω : Disorder) : |Real.exp (-Real.log (X N ω))| ^ (2 : ℝ) = (Xflat N ω)⁻¹ ^ 2 := by
      rw [abs_of_pos (Real.exp_pos _), Real.rpow_two, hEq ω, hCellEq N hN1]
    simpa only [he] using (hN x).2
  have hLimitSq := JointConvergence.integrable_rpow_limit_of_tendstoInDistribution hInvDist
    (by norm_num : (0 : ℝ) < 2) hInt hUpper
  have hMem : MemLp (fun ω => Real.exp (-Real.log (Y ω))) 2 P := by
    apply (memLp_two_iff_integrable_sq hInvDist.aemeasurable_limit.aestronglyMeasurable).mpr
    simpa only [abs_of_pos (Real.exp_pos _), Real.rpow_two] using hLimitSq.1
  have hIntInv : Integrable (fun ω => (Y ω)⁻¹) P :=
    (hMem.integrable (by norm_num)).congr hLimitEq
  have hMean := JointConvergence.tendsto_integral_of_tendstoInDistribution hInvDist
    (by norm_num : (1 : ℝ) < 2) hUpper hInt
  rw [integral_congr_ae hLimitEq] at hMean
  refine ⟨hIntInv, hMean.congr' ?_⟩
  filter_upwards [hSeqEq] with N hN
  exact integral_congr_ae (Filter.Eventually.of_forall hN)

end Critical2DKPZ.NonGaussian

end
