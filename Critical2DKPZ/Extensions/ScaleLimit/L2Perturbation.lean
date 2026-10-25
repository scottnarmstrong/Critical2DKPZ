/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SpectralContraction
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! # Transfer of weak limits and second moments under vanishing L2 errors -/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The L2 class norm is the square root of the actual second moment. -/
theorem norm_toLp_two_eq_sqrt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : MemLp X 2 P) :
    ‖hX.toLp X‖ = Real.sqrt (∫ ω, X ω ^ 2 ∂P) := by
  have he : ‖hX.toLp X‖ ^ 2 = ∫ ω, X ω ^ 2 ∂P := by
    rw [norm_Lp_two_sq]
    apply integral_congr_ae
    filter_upwards [hX.coeFn_toLp] with ω hω
    rw [hω, Real.norm_eq_abs, sq_abs]
  rw [← he, Real.sqrt_sq (norm_nonneg _)]

/-- A vanishing second moment is sufficient for convergence to zero in probability. -/
theorem tendstoInMeasure_zero_of_integral_sq_tendsto {ι Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {l : Filter ι} {X : ι → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 P)
    (h2 : Tendsto (fun i => ∫ ω, X i ω ^ 2 ∂P) l (𝓝 0)) :
    TendstoInMeasure P X l 0 := by
  have hn : Tendsto (fun i => ‖(hX i).toLp (X i)‖) l (𝓝 0) := by
    simpa only [norm_toLp_two_eq_sqrt, Real.sqrt_zero] using h2.sqrt
  have he : Tendsto (fun i => eLpNorm (X i) 2 P) l (𝓝 0) := by
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hn
    simp only [ENNReal.ofReal_zero] at hh
    convert hh using 1
    funext i
    dsimp only [Function.comp_apply]
    rw [ofReal_norm, Lp.enorm_def, eLpNorm_congr_ae (hX i).coeFn_toLp]
  apply tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  simpa only [sub_zero] using he

/-- Second moments are stable under perturbations whose L2 errors tend to zero. -/
theorem integral_sq_tendsto_of_L2_perturbation {ι Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {l : Filter ι} {X Y : ι → Ω → ℝ} {v : ℝ}
    (hv : 0 ≤ v) (hX : ∀ i, MemLp (X i) 2 P) (hY : ∀ i, MemLp (Y i) 2 P)
    (h2 : Tendsto (fun i => ∫ ω, X i ω ^ 2 ∂P) l (𝓝 v))
    (herr : Tendsto (fun i => ∫ ω, (Y i ω - X i ω) ^ 2 ∂P) l (𝓝 0)) :
    Tendsto (fun i => ∫ ω, Y i ω ^ 2 ∂P) l (𝓝 v) := by
  let U := fun i => (hX i).toLp (X i)
  let V := fun i => (hY i).toLp (Y i)
  have hU : Tendsto (fun i => ‖U i‖) l (𝓝 (Real.sqrt v)) := by
    simpa only [U, norm_toLp_two_eq_sqrt] using h2.sqrt
  have hdiff (i : ι) : ‖V i - U i‖ = Real.sqrt (∫ ω, (Y i ω - X i ω) ^ 2 ∂P) := by
    rw [← MemLp.toLp_sub]
    exact norm_toLp_two_eq_sqrt ((hY i).sub (hX i))
  have hd : Tendsto (fun i => ‖V i - U i‖) l (𝓝 0) := by
    simpa only [hdiff, Real.sqrt_zero] using herr.sqrt
  have hnormdist : Tendsto (fun i => dist ‖U i‖ ‖V i‖) l (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) ?_ hd
    intro i
    exact (dist_norm_norm_le (U i) (V i)).trans_eq (norm_sub_rev _ _)
  have hV := (hU.congr_dist hnormdist).pow 2
  simpa only [V, norm_toLp_two_eq_sqrt, Real.sq_sqrt hv,
    Real.sq_sqrt (integral_nonneg fun ω => sq_nonneg _)] using hV

end Critical2DKPZ.Extensions.ScaleLimit
