/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.MeanMeasure
public import Critical2DKPZ.SHF.Positivity.BoundedPairingConvergence
import Mathlib.Tactic

/-! # A nonzero positive compact terminal gives a strictly positive mean -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Tsai Critical2DKPZ.SHF.Positivity
open scoped CompactlySupported ENNReal Topology

namespace Critical2DKPZ.NonGaussian

/-- The heat-start pairing against a nonzero nonnegative compactly supported continuous terminal
is integrable and has strictly positive mean. -/
theorem integrable_and_integral_heatStart_cc_pos (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {s t δ : ℝ} (hs : 0 ≤ s) (hst : s < t) (hδ : 0 < δ) (x : Plane)
    (φ : C_c(Plane, ℝ)) (hφ : ∀ y, 0 ≤ φ y) (hφ' : φ ≠ 0) :
    Integrable (shfPairing Z s t (fun y => heatKernel δ (y - x)) φ) P ∧
      0 < ∫ ω, shfPairing Z s t (fun y => heatKernel δ (y - x)) φ ω ∂P := by
  have hPair := isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hs hst hδ x φ.toBoundedContinuousFunction
  let F : Plane × Plane → ℝ := fun p => heatKernel δ (p.1 - x) * φ p.2
  have hF : Continuous F := ((continuous_heatKernel δ).comp (continuous_fst.sub continuous_const)).mul
    (φ.continuous.comp continuous_snd)
  have hF0 (p : Plane × Plane) : 0 ≤ F p := mul_nonneg (heatKernel_nonneg hδ.le _) (hφ _)
  have hInt : Integrable (fun ω => ∫ p, F p ∂Z s t ω) P := hPair.2.1
  have hLinMean : (∫⁻ p, ENNReal.ofReal (F p) ∂heatBlock (t - s)) =
      ENNReal.ofReal (∫ ω, ∫ p, F p ∂Z s t ω ∂P) := by
    rw [← isCriticalSHF_bind_eq_heatBlock ϑ P Z hZ hs hst,
      Measure.lintegral_bind (hZ.1 s t hs hst).aemeasurable hF.measurable.ennreal_ofReal.aemeasurable]
    have hInner : ∀ᵐ ω ∂P, (∫⁻ p, ENNReal.ofReal (F p) ∂Z s t ω) =
        ENNReal.ofReal (∫ p, F p ∂Z s t ω) := by
      filter_upwards [hPair.1] with ω hω
      exact (ofReal_integral_eq_lintegral_ofReal hω (Filter.Eventually.of_forall hF0)).symm
    rw [lintegral_congr_ae hInner]
    exact (ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall fun _ => integral_nonneg hF0)).symm
  let G : Plane × Plane → ℝ := fun p => heatKernel (t - s) (p.2 - p.1) * F p
  have hG : Continuous G := ((continuous_heatKernel (t - s)).comp
    (continuous_snd.sub continuous_fst)).mul hF
  have hDensity : Measurable (fun p : Plane × Plane => ENNReal.ofReal (heatKernel (t - s) (p.2 - p.1))) :=
    ((measurable_heatKernel (t - s)).comp (measurable_snd.sub measurable_fst)).ennreal_ofReal
  have hLin : (∫⁻ p, ENNReal.ofReal (F p) ∂heatBlock (t - s)) = ∫⁻ p, ENNReal.ofReal (G p) := by
    unfold heatBlock
    rw [lintegral_withDensity_eq_lintegral_mul volume hDensity hF.measurable.ennreal_ofReal]
    apply lintegral_congr
    intro p
    change ENNReal.ofReal (heatKernel (t - s) (p.2 - p.1)) * ENNReal.ofReal (F p) = ENNReal.ofReal (G p)
    exact (ENNReal.ofReal_mul (heatKernel_nonneg (sub_nonneg.mpr hst.le) _)).symm
  obtain ⟨y, hy⟩ := DFunLike.ne_iff.mp hφ'
  have hy0 : 0 < φ y := lt_of_le_of_ne (hφ y) (Ne.symm hy)
  have hGxy : 0 < G (x, y) := mul_pos (heatKernel_pos (sub_pos.mpr hst) _)
    (mul_pos (heatKernel_pos hδ _) hy0)
  have hSupp : Function.support (fun p => ENNReal.ofReal (G p)) = {p | 0 < G p} := by
    ext p
    simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le, Set.mem_ofPred_eq]
  have hLinPos : 0 < ∫⁻ p, ENNReal.ofReal (G p) := by
    apply (lintegral_pos_iff_support hG.measurable.ennreal_ofReal).mpr
    rw [hSupp]
    exact (isOpen_lt continuous_const hG).measure_pos volume ⟨(x, y), hGxy⟩
  rw [← hLin, hLinMean] at hLinPos
  exact ⟨hInt, ENNReal.ofReal_pos.mp hLinPos⟩

end Critical2DKPZ.NonGaussian

end
