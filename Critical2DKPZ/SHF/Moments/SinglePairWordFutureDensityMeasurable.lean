/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureDensity
import Mathlib.Tactic

/-! # Joint measurability of the fixed-measure two-particle future density -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory
open scoped CompactlySupported

/-- The complete tested future density is jointly measurable in its horizon,
incoming locations, collision center, renewal clock, and terminal locations. -/
theorem measurable_pairTwoFutureDensity
    (θ : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) :
    Measurable (fun p : (ℝ × (Fin 2 → Plane) × Plane) × (ℝ × (Plane × Plane)) =>
      pairTwoFutureDensity θ p.1.1 φ p.1.2.1 p.1.2.2 p.2) := by
  let F := fun p : (ℝ × (Fin 2 → Plane) × Plane) × (ℝ × (Plane × Plane)) =>
    φ 0 (p.1.2.1 0, p.2.2.1) * φ 1 (p.1.2.1 1, p.2.2.2) *
      (DeltaBose.scalarDensity θ p.2.1 *
        (heatKernel (2 * (p.1.1 - p.2.1)) (p.2.2.2 - p.2.2.1) *
          heatKernel (p.1.1 / 2) ((1 / 2 : ℝ) • (p.2.2.1 + p.2.2.2) - p.1.2.2)))
  have hheat : Measurable (fun p : ℝ × Plane => heatKernel p.1 p.2) := by
    unfold heatKernel
    fun_prop
  have hφ₀ : Measurable (fun p : (ℝ × (Fin 2 → Plane) × Plane) × (ℝ × (Plane × Plane)) =>
      φ 0 (p.1.2.1 0, p.2.2.1)) :=
    (φ 0).measurable.comp (((measurable_pi_apply 0).comp measurable_fst.snd.fst).prodMk
      measurable_snd.snd.fst)
  have hφ₁ : Measurable (fun p : (ℝ × (Fin 2 → Plane) × Plane) × (ℝ × (Plane × Plane)) =>
      φ 1 (p.1.2.1 1, p.2.2.2)) :=
    (φ 1).measurable.comp (((measurable_pi_apply 1).comp measurable_fst.snd.fst).prodMk
      measurable_snd.snd.snd)
  have hρ : Measurable (fun p : (ℝ × (Fin 2 → Plane) × Plane) × (ℝ × (Plane × Plane)) =>
      DeltaBose.scalarDensity θ p.2.1) :=
    DeltaBose.measurable_scalarDensity.comp (measurable_const.prodMk measurable_snd.fst)
  have hg : Measurable (fun p : (ℝ × (Fin 2 → Plane) × Plane) × (ℝ × (Plane × Plane)) =>
      heatKernel (2 * (p.1.1 - p.2.1)) (p.2.2.2 - p.2.2.1)) := by
    have ha : Measurable (fun p : (ℝ × (Fin 2 → Plane) × Plane) × (ℝ × (Plane × Plane)) =>
        (2 * (p.1.1 - p.2.1), p.2.2.2 - p.2.2.1)) := by fun_prop
    exact hheat.comp ha
  have hc : Measurable (fun p : (ℝ × (Fin 2 → Plane) × Plane) × (ℝ × (Plane × Plane)) =>
      heatKernel (p.1.1 / 2) ((1 / 2 : ℝ) • (p.2.2.1 + p.2.2.2) - p.1.2.2)) := by
    have ha : Measurable (fun p : (ℝ × (Fin 2 → Plane) × Plane) × (ℝ × (Plane × Plane)) =>
        (p.1.1 / 2, (1 / 2 : ℝ) • (p.2.2.1 + p.2.2.2) - p.1.2.2)) := by fun_prop
    exact hheat.comp ha
  have hm : Measurable F := (hφ₀.mul hφ₁).mul (hρ.mul (hg.mul hc))
  have hs : MeasurableSet {p : (ℝ × (Fin 2 → Plane) × Plane) × (ℝ × (Plane × Plane)) |
      0 < p.2.1 ∧ p.2.1 < p.1.1} :=
    ((isOpen_lt continuous_const continuous_snd.fst).inter
      (isOpen_lt continuous_snd.fst continuous_fst.fst)).measurableSet
  have he : (fun p : (ℝ × (Fin 2 → Plane) × Plane) × (ℝ × (Plane × Plane)) =>
      pairTwoFutureDensity θ p.1.1 φ p.1.2.1 p.1.2.2 p.2) =
      {p | 0 < p.2.1 ∧ p.2.1 < p.1.1}.indicator F := by
    funext p
    by_cases hp : 0 < p.2.1 ∧ p.2.1 < p.1.1
    · simp only [pairTwoFutureDensity, Set.indicator_of_mem
        (show p.2 ∈ Set.Ioo 0 p.1.1 ×ˢ Set.univ from ⟨hp, Set.mem_univ _⟩),
        Set.indicator_of_mem (show p ∈ {p | 0 < p.2.1 ∧ p.2.1 < p.1.1} from hp)]
      rw [pairTwoFutureSpatialProfile_eq_centerGap hp.1 hp.2]
      rfl
    · have hn : p.2 ∉ Set.Ioo 0 p.1.1 ×ˢ Set.univ := fun h => hp h.1
      simp only [pairTwoFutureDensity, Set.indicator_of_notMem hn,
        Set.indicator_of_notMem (show p ∉ {p | 0 < p.2.1 ∧ p.2.1 < p.1.1} from hp)]
  rw [he]
  exact hm.indicator hs

end Critical2DKPZ.SHF.Moments
