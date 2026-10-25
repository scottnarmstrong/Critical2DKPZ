/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordDiagramPathL1
import Mathlib.Tactic

/-! # Integrating the complete signed two-particle diagram path -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter
open scoped CompactlySupported

/-- The full signed entrance profile equals `16π` times the integrated diagram
path. Joint integrability is supplied by `integrable_pairTwoContinuumDiagramPath`. -/
theorem pairTwo_continuum_entrance_eq_diagramPath_integral
    (θ T : ℝ) (hT : 0 < T) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) :
    let μ := ((volume : Measure ℝ).restrict (Set.Ioo 0 T)).prod
      ((volume : Measure Plane).prod ((volume : Measure Plane).prod (volume : Measure Plane)))
    let ν := (volume : Measure ℝ).prod ((volume : Measure Plane).prod (volume : Measure Plane))
    (∫ p : ℝ × (Plane × (Plane × Plane)),
      (heatKernel p.1 (p.2.2.1 - p.2.1) * heatKernel p.1 (p.2.2.2 - p.2.2.1)) *
        pairTwoContinuumFuture θ (T - p.1) φ ![p.2.1, p.2.2.2] p.2.2.1 ∂μ) =
      (16 * Real.pi) * (∫ p, pairTwoContinuumDiagramPath θ T φ p ∂μ.prod ν) := by
  dsimp only
  let μ := ((volume : Measure ℝ).restrict (Set.Ioo 0 T)).prod
    ((volume : Measure Plane).prod ((volume : Measure Plane).prod (volume : Measure Plane)))
  let ν := (volume : Measure ℝ).prod ((volume : Measure Plane).prod (volume : Measure Plane))
  have hi : Integrable (pairTwoContinuumDiagramPath θ T φ) (μ.prod ν) :=
    integrable_pairTwoContinuumDiagramPath θ T hT φ
  rw [integral_prod _ hi, ← integral_const_mul]
  have ht : ∀ᵐ p : ℝ × (Plane × (Plane × Plane)) ∂μ, p.1 ∈ Set.Ioo 0 T := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact Eventually.of_forall fun _ => hu
  apply integral_congr_ae
  filter_upwards [ht] with p hp
  have he := pairTwoContinuumFuture_eq_density_integral θ (sub_pos.mpr hp.2) φ
    ![p.2.1, p.2.2.2] p.2.2.1
  rw [he]
  simp only [pairTwoContinuumDiagramPath, integral_const_mul]
  ring

end Critical2DKPZ.SHF.Moments
