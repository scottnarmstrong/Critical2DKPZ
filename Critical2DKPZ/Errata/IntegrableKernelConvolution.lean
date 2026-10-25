/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.WeightedConvolution
import Mathlib.Analysis.Normed.Operator.Basic

/-! # Bounded planar convolution

The convolution step in Tsai24 Lemma 2.3 defines a bounded operator on planar `L²` for a continuous `L¹` kernel, with an integrable Bochner formula. -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.Analysis.Sobolev

namespace Critical2DKPZ.Errata

/-- A continuous integrable planar kernel defines a bounded linear convolution operator on L². -/
theorem exists_convolutionOperator_of_continuous_integrable
    (w : Plane → ℂ) (hw : Continuous w) (hL1 : Integrable w) :
    ∃ T : Lp ℂ 2 (volume : Measure Plane) →L[ℂ] Lp ℂ 2 (volume : Measure Plane),
      ‖T‖ ≤ ∫ η : Plane, ‖w η‖ ∧
        ∀ f : Lp ℂ 2 (volume : Measure Plane),
          Integrable (fun η : Plane => w η • translateL2 η f) ∧
          T f = l2ConvolutionAction w f := by
  let L : Lp ℂ 2 (volume : Measure Plane) →ₗ[ℂ] Lp ℂ 2 (volume : Measure Plane) :=
    { toFun := l2ConvolutionAction w
      map_add' := by
        intro f g
        change (∫ η : Plane, w η • translateL2 η (f + g)) = _
        have he (η : Plane) : translateL2 η (f + g) = translateL2 η f + translateL2 η g :=
          map_add (Lp.compMeasurePreserving _ _) f g
        simp_rw [he, smul_add]
        exact integral_add (norm_l2ConvolutionAction_le hL1 hw f).1
          (norm_l2ConvolutionAction_le hL1 hw g).1
      map_smul' := by
        intro c f
        change (∫ η : Plane, w η • translateL2 η (c • f)) = _
        have he (η : Plane) : translateL2 η (c • f) = c • translateL2 η f :=
          (Lp.compMeasurePreservingₗ ℂ _ _).map_smul c f
        simp_rw [he, smul_comm (w _) c]
        exact integral_smul c (fun η : Plane => w η • translateL2 η f) }
  have hbound (f : Lp ℂ 2 (volume : Measure Plane)) :
      ‖L f‖ ≤ (∫ η : Plane, ‖w η‖) * ‖f‖ :=
    (norm_l2ConvolutionAction_le hL1 hw f).2
  refine ⟨L.mkContinuous _ hbound,
    L.mkContinuous_norm_le (integral_nonneg (fun _ => norm_nonneg _)) hbound, ?_⟩
  intro f
  exact ⟨(norm_l2ConvolutionAction_le hL1 hw f).1, rfl⟩

end Critical2DKPZ.Errata
