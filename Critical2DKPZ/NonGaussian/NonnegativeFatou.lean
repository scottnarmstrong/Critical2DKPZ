/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

/-! # Real integrability and upper bounds from nonnegative Fatou -/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Critical2DKPZ.NonGaussian

/-- An almost-everywhere limit of nonnegative integrable functions with uniformly bounded integrals
is integrable and obeys the same integral bound. -/
theorem integrable_and_integral_le_of_ae_tendsto_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : ℕ → Ω → ℝ) (hF : ∀ n, Integrable (F n) P)
    (hF0 : ∀ n, 0 ≤ᵐ[P] F n) (G : Ω → ℝ) (hG : AEMeasurable G P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (G ω)))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n, (∫ ω, F n ω ∂P) ≤ C) :
    (0 ≤ᵐ[P] G) ∧ Integrable G P ∧ (∫ ω, G ω ∂P) ≤ C := by
  have hG0 : 0 ≤ᵐ[P] G := by
    filter_upwards [hlim, ae_all_iff.2 hF0] with ω hω hω0
    exact ge_of_tendsto hω (Eventually.of_forall hω0)
  have hlin (n : ℕ) : (∫⁻ ω, ENNReal.ofReal (F n ω) ∂P) ≤ ENNReal.ofReal C := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hF n) (hF0 n)]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hFatou : (∫⁻ ω, ENNReal.ofReal (G ω) ∂P) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ ω, atTop.liminf (fun n => ENNReal.ofReal (F n ω)) ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with ω hω
        exact ((ENNReal.continuous_ofReal.tendsto (G ω)).comp hω).liminf_eq.symm
      _ ≤ atTop.liminf (fun n => ∫⁻ ω, ENNReal.ofReal (F n ω) ∂P) :=
        lintegral_liminf_le' (fun n => (hF n).aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal C := by
        refine liminf_le_of_le (by isBoundedDefault) (fun b hb => ?_)
        obtain ⟨n, hn⟩ := hb.exists
        exact hn.trans (hlin n)
  have hGI : Integrable G P :=
    (lintegral_ofReal_ne_top_iff_integrable hG.aestronglyMeasurable hG0).1
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hFatou)
  refine ⟨hG0, hGI, ?_⟩
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hFatou
  rw [← ofReal_integral_eq_lintegral_ofReal hGI hG0,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hG0), ENNReal.toReal_ofReal hC] at hreal
  exact hreal

end Critical2DKPZ.NonGaussian

end
