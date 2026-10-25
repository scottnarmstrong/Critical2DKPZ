/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.WeightedConvolution
import Mathlib.Tactic

/-! # Bounded convolution by compactly supported mollifiers

Continuous compactly supported mollifiers define bounded convolution operators on L²,
with operator norm at most their L¹ norm, as used in Tsai24's proof of Lemma 2.3.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Critical2DKPZ.Errata

/-- Convolution by a continuous compactly supported mollifier is bounded on L²,
and its defining Bochner integral is integrable. -/
theorem norm_l2ConvolutionAction_le_of_continuous_hasCompactSupport (w : Plane → ℝ)
    (hw : Continuous w) (hc : HasCompactSupport w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Lp ℂ 2 (volume : Measure Plane),
      Integrable (fun η : Plane => (w η : ℂ) • Analysis.Sobolev.translateL2 η f) ∧
      ‖Analysis.Sobolev.l2ConvolutionAction (fun η => (w η : ℂ)) f‖ ≤ C * ‖f‖ := by
  have hcont : Continuous (fun η => (w η : ℂ)) := Complex.continuous_ofReal.comp hw
  have hsupp : HasCompactSupport (fun η => (w η : ℂ)) := hc.comp_left (g := fun a : ℝ => (a : ℂ)) Complex.ofReal_zero
  have hint : Integrable (fun η : Plane => (w η : ℂ)) (volume : Measure Plane) :=
    hcont.integrable_of_hasCompactSupport hsupp
  refine ⟨∫ η : Plane, ‖(w η : ℂ)‖, integral_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro f
  exact Analysis.Sobolev.norm_l2ConvolutionAction_le hint hcont f

end Critical2DKPZ.Errata
