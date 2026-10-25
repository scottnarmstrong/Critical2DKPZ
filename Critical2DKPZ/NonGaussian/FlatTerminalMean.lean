/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.MeanMeasure
public import Critical2DKPZ.NonGaussian.HeatBlockMarginals
public import Critical2DKPZ.Definitions.ShfPairing
import Mathlib.Tactic

/-! # First moments and integrability for compact final-endpoint tests -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported ENNReal

namespace Critical2DKPZ.NonGaussian

/-- The flat-initial SHF pairing against a nonnegative compact terminal is integrable
and has expectation equal to the terminal test’s Lebesgue integral; the inner spatial integral
is finite almost surely. -/
theorem flat_cc_pairing_integrable_mean (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (g : C_c(Plane, ℝ)) (hg : ∀ y, 0 ≤ g y) :
    (∫⁻ ω, ∫⁻ p, ENNReal.ofReal (g p.2) ∂Z s t ω ∂P) = ENNReal.ofReal (∫ y, g y) ∧
    (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane => g p.2) (Z s t ω)) ∧
    Integrable (shfPairing Z s t (fun _ => 1) g) P ∧
    (∫ ω, shfPairing Z s t (fun _ => 1) g ω ∂P) = ∫ y, g y := by
  let Q (ω : Ω) : ℝ≥0∞ := ∫⁻ p, ENNReal.ofReal (g p.2) ∂Z s t ω
  have hQ : Measurable Q :=
    (Measure.measurable_lintegral (g.continuous.measurable.comp measurable_snd).ennreal_ofReal).comp
      (hZ.1 s t hs hst)
  have hgI : Integrable (g : Plane → ℝ) :=
    g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  have hQmean : (∫⁻ ω, Q ω ∂P) = ENNReal.ofReal (∫ y, g y) := by
    calc
      _ = ∫⁻ p, ENNReal.ofReal (g p.2) ∂P.bind (Z s t) :=
        (Measure.lintegral_bind (hZ.1 s t hs hst).aemeasurable
          (g.continuous.measurable.comp measurable_snd).ennreal_ofReal.aemeasurable).symm
      _ = ∫⁻ y, ENNReal.ofReal (g y) := by
        rw [isCriticalSHF_bind_eq_heatBlock ϑ P Z hZ hs hst]
        exact lintegral_heatBlock_snd_eq (sub_pos.2 hst) _ g.continuous.measurable.ennreal_ofReal
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hgI (Eventually.of_forall hg)).symm
  have hQfin : (∫⁻ ω, Q ω ∂P) ≠ ∞ := by rw [hQmean]; exact ENNReal.ofReal_ne_top
  have hfinite := ae_lt_top' hQ.aemeasurable hQfin
  have hInner : ∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane => g p.2) (Z s t ω) := by
    filter_upwards [hfinite] with ω hω
    exact (lintegral_ofReal_ne_top_iff_integrable
      (g.continuous.measurable.comp measurable_snd).aestronglyMeasurable
      (Eventually.of_forall fun p => hg p.2)).1 hω.ne
  have hReal : (fun ω => (Q ω).toReal) =ᵐ[P] shfPairing Z s t (fun _ => 1) g := by
    filter_upwards [hInner] with ω hω
    change (∫⁻ p, ENNReal.ofReal (g p.2) ∂Z s t ω).toReal = ∫ p, 1 * g p.2 ∂Z s t ω
    rw [← ofReal_integral_eq_lintegral_ofReal hω (Eventually.of_forall fun p => hg p.2),
      ENNReal.toReal_ofReal (integral_nonneg fun p : Plane × Plane => hg p.2)]
    simp only [one_mul]
  refine ⟨hQmean, hInner, (integrable_toReal_of_lintegral_ne_top hQ.aemeasurable hQfin).congr hReal, ?_⟩
  calc
    _ = ∫ ω, (Q ω).toReal ∂P := integral_congr_ae hReal.symm
    _ = (∫⁻ ω, Q ω ∂P).toReal := integral_toReal hQ.aemeasurable hfinite
    _ = _ := by rw [hQmean, ENNReal.toReal_ofReal (integral_nonneg hg)]

end Critical2DKPZ.NonGaussian

end
