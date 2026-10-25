/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureDensityMeasurable
public import Critical2DKPZ.SHF.Moments.SinglePairWordEntranceFullL1
import Mathlib.Tactic

/-! # Joint absolute integrability of the tested two-particle diagram path -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter
open scoped CompactlySupported

/-- The tested entrance and future density before any time, center, or
terminal integrals are reordered. -/
def pairTwoContinuumDiagramPath (θ T : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (p : (ℝ × (Plane × (Plane × Plane))) × (ℝ × (Plane × Plane))) : ℝ :=
  (heatKernel p.1.1 (p.1.2.2.1 - p.1.2.1) *
    heatKernel p.1.1 (p.1.2.2.2 - p.1.2.2.1)) *
    pairTwoFutureDensity θ (T - p.1.1) φ ![p.1.2.1, p.1.2.2.2] p.1.2.2.1 p.2

/-- The complete signed diagram path is jointly measurable before any
variables are integrated out. -/
theorem measurable_pairTwoContinuumDiagramPath
    (θ T : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) :
    Measurable (pairTwoContinuumDiagramPath θ T φ) := by
  let H := fun p : ℝ × (Plane × (Plane × Plane)) =>
    heatKernel p.1 (p.2.2.1 - p.2.1) * heatKernel p.1 (p.2.2.2 - p.2.2.1)
  have hmH : Measurable H := by dsimp [H]; unfold heatKernel; fun_prop
  have ha : Measurable (fun p : (ℝ × (Plane × (Plane × Plane))) × (ℝ × (Plane × Plane)) =>
      (![p.1.2.1, p.1.2.2.2] : Fin 2 → Plane)) := by
    apply Measurable.of_eval
    intro i
    fin_cases i <;> fun_prop
  have hmap : Measurable (fun p : (ℝ × (Plane × (Plane × Plane))) × (ℝ × (Plane × Plane)) =>
      ((T - p.1.1, (![p.1.2.1, p.1.2.2.2] : Fin 2 → Plane), p.1.2.2.1), p.2)) :=
    ((measurable_const.sub measurable_fst.fst).prodMk
      (ha.prodMk measurable_fst.snd.snd.fst)).prodMk measurable_snd
  exact (hmH.comp measurable_fst).mul ((measurable_pairTwoFutureDensity θ φ).comp hmap)

/-- Joint absolute integrability of the complete signed tested diagram path.
This justifies Fubini across the entrance clock, both incoming locations,
collision center, renewal clock, and both terminal locations. -/
theorem integrable_pairTwoContinuumDiagramPath
    (θ T : ℝ) (hT : 0 < T) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) :
    let μ := ((volume : Measure ℝ).restrict (Set.Ioo 0 T)).prod
      ((volume : Measure Plane).prod ((volume : Measure Plane).prod (volume : Measure Plane)))
    let ν := (volume : Measure ℝ).prod ((volume : Measure Plane).prod (volume : Measure Plane))
    Integrable (pairTwoContinuumDiagramPath θ T φ) (μ.prod ν) := by
  dsimp only
  let μ := ((volume : Measure ℝ).restrict (Set.Ioo 0 T)).prod
    ((volume : Measure Plane).prod ((volume : Measure Plane).prod (volume : Measure Plane)))
  let ν := (volume : Measure ℝ).prod ((volume : Measure Plane).prod (volume : Measure Plane))
  let H := fun p : ℝ × (Plane × (Plane × Plane)) =>
    heatKernel p.1 (p.2.2.1 - p.2.1) * heatKernel p.1 (p.2.2.2 - p.2.2.1)
  have hm := measurable_pairTwoContinuumDiagramPath θ T φ
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · apply Eventually.of_forall
    intro p
    exact (integrable_pairTwoFutureDensity θ (T - p.1) φ ![p.2.1, p.2.2.2] p.2.2.1).const_mul (H p)
  · have hi := (integrable_pairTwo_continuum_entrance θ T hT
      (fun i => compactAbs (φ i))).div_const (16 * Real.pi)
    have ht : ∀ᵐ p : ℝ × (Plane × (Plane × Plane)) ∂μ, p.1 ∈ Set.Ioo 0 T := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.preimage measurable_fst)).mpr
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      exact Eventually.of_forall fun _ => hu
    apply hi.congr
    filter_upwards [ht] with p hp
    have hn : 0 ≤ H p :=
      mul_nonneg (heatKernel_nonneg hp.1.le _) (heatKernel_nonneg hp.1.le _)
    have he := pairTwoContinuumFuture_compactAbs_eq_density_mass θ
      (sub_pos.mpr hp.2) φ ![p.2.1, p.2.2.2] p.2.2.1
    change H p * pairTwoContinuumFuture θ (T - p.1) (fun i => compactAbs (φ i))
      ![p.2.1, p.2.2.2] p.2.2.1 / (16 * Real.pi) =
      ∫ y : ℝ × (Plane × Plane), ‖H p *
        pairTwoFutureDensity θ (T - p.1) φ ![p.2.1, p.2.2.2] p.2.2.1 y‖ ∂ν
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hn, integral_const_mul]
    rw [he]
    simp only [Real.norm_eq_abs, ν]
    have hπ : (16 * Real.pi : ℝ) ≠ 0 := by positivity
    field_simp

end Critical2DKPZ.SHF.Moments
