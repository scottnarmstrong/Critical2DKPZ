/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.MeanMeasure
public import Critical2DKPZ.SHF.Positivity.BoundedPairingConvergence
public import Critical2DKPZ.Analysis.Heat.Semigroup
import Mathlib.Tactic

/-! # Exact annealed heat-start pairing formulas -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Tsai Critical2DKPZ.SHF.Positivity
open scoped BoundedContinuousFunction ENNReal Topology

namespace Critical2DKPZ.NonGaussian

/-- The expectation of a nonnegative bounded continuous heat-start pairing is its deterministic
double heat-kernel integral, whose integrand is integrable. -/
theorem integrable_and_heatStart_integral_eq (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {s t δ : ℝ} (hs : 0 ≤ s) (hst : s < t) (hδ : 0 < δ) (x : Plane)
    (g : Plane →ᵇ ℝ) (hg : ∀ y, 0 ≤ g y) :
    Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x) * g p.2 *
      heatKernel (t - s) (p.2 - p.1)) ∧
    (∫ ω, shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω ∂P) =
      ∫ p : Plane × Plane, heatKernel δ (p.1 - x) * g p.2 * heatKernel (t - s) (p.2 - p.1) := by
  let F : Plane × Plane → ℝ := fun p => heatKernel δ (p.1 - x) * g p.2
  let G : Plane × Plane → ℝ := fun p => F p * heatKernel (t - s) (p.2 - p.1)
  have hPair := isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hs hst hδ x g
  have hF : Continuous F := ((continuous_heatKernel δ).comp (continuous_fst.sub continuous_const)).mul
    (g.continuous.comp continuous_snd)
  have hG : Continuous G := hF.mul ((continuous_heatKernel (t - s)).comp (continuous_snd.sub continuous_fst))
  have hF0 (p : Plane × Plane) : 0 ≤ F p := mul_nonneg (heatKernel_nonneg hδ.le _) (hg _)
  have hG0 (p : Plane × Plane) : 0 ≤ G p := mul_nonneg (hF0 _) (heatKernel_nonneg (sub_nonneg.mpr hst.le) _)
  have hInner : ∀ᵐ ω ∂P, (∫⁻ p, ENNReal.ofReal (F p) ∂Z s t ω) =
      ENNReal.ofReal (∫ p, F p ∂Z s t ω) := by
    filter_upwards [hPair.1] with ω hω
    exact (ofReal_integral_eq_lintegral_ofReal hω (Filter.Eventually.of_forall hF0)).symm
  have hDensity : Measurable (fun p : Plane × Plane => ENNReal.ofReal (heatKernel (t - s) (p.2 - p.1))) :=
    ((measurable_heatKernel (t - s)).comp (measurable_snd.sub measurable_fst)).ennreal_ofReal
  have hLin : (∫⁻ p, ENNReal.ofReal (G p)) =
      ENNReal.ofReal (∫ ω, ∫ p, F p ∂Z s t ω ∂P) := by
    calc
      _ = ∫⁻ p, ENNReal.ofReal (F p) ∂heatBlock (t - s) := by
        unfold heatBlock
        rw [lintegral_withDensity_eq_lintegral_mul volume hDensity hF.measurable.ennreal_ofReal]
        apply lintegral_congr
        intro p
        change ENNReal.ofReal (G p) = ENNReal.ofReal (heatKernel (t - s) (p.2 - p.1)) * ENNReal.ofReal (F p)
        rw [← ENNReal.ofReal_mul (heatKernel_nonneg (sub_nonneg.mpr hst.le) _)]
        congr 1
        exact mul_comm _ _
      _ = ∫⁻ ω, ∫⁻ p, ENNReal.ofReal (F p) ∂Z s t ω ∂P := by
        rw [← isCriticalSHF_bind_eq_heatBlock ϑ P Z hZ hs hst]
        exact Measure.lintegral_bind (hZ.1 s t hs hst).aemeasurable hF.measurable.ennreal_ofReal.aemeasurable
      _ = ∫⁻ ω, ENNReal.ofReal (∫ p, F p ∂Z s t ω) ∂P := lintegral_congr_ae hInner
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hPair.2.1
        (Filter.Eventually.of_forall fun _ => integral_nonneg hF0)).symm
  have hGInt : Integrable G := by
    refine ⟨hG.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hG0), hLin]
    exact ENNReal.ofReal_lt_top
  have hEq : (∫ p, G p) = ∫ ω, ∫ p, F p ∂Z s t ω ∂P := by
    apply (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg hG0)
      (integral_nonneg fun _ => integral_nonneg hF0)).mp
    rw [ofReal_integral_eq_lintegral_ofReal hGInt (Filter.Eventually.of_forall hG0), hLin]
  exact ⟨hGInt, hEq.symm⟩

end Critical2DKPZ.NonGaussian

end
