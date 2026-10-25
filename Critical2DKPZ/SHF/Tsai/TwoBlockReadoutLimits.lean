/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.TwoBlockReadouts
public import Critical2DKPZ.SHF.Tsai.TwoIncrementLimits
public import Critical2DKPZ.SHF.Tsai.FourthMomentProbability
public import Critical2DKPZ.SHF.Tsai.CompactTensorTests

/-! # Pairing limits of smoothed two-block products

The measurable pairing map of two consecutive flow increments converges in probability to
their combined increment for every applicable mollifier family. Locally finite
modifications preserve these pairings almost surely.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- The measurable two-block pairing map converges in probability to the combined increment pairing for every applicable mollifier family. -/
theorem IsDenseSHF.tendstoInMeasure_modifiedTwoBlockReadout_tensor {θ : ℝ} {D : Set ℝ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsDenseSHF θ D P Z)
    {a b c : ℝ} (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D) (hab : a < b) (hbc : b < c)
    (E : CompactExhaustion (Plane × Plane)) (w : ℕ → Plane → ℝ) (hw : IsL2ApplicableMollifier w)
    (g g' : C_c(Plane, ℝ)) :
    TendstoInMeasure P (fun n ω => modifiedTwoBlockReadout E (w n) (compactTensorTest g g')
      (Z a b ω, Z b c ω)) atTop (fun ω => ∫ p, g p.1 * g' p.2 ∂Z a c ω) := by
  have hg : MemLp g 2 := g.continuous.memLp_of_hasCompactSupport g.hasCompactSupport
  have hg' : MemLp g' 2 := g'.continuous.memLp_of_hasCompactSupport g'.hasCompactSupport
  have h := isDenseSHF_smoothedProduct_tendsto_tensor θ D P Z hZ ha hb hc hab hbc w hw g g' hg hg'
  have hconv := tendstoInMeasure_of_integrable_fourth_moments P _ _ h.1 h.2
  apply hconv.congr_left
  intro n
  filter_upwards [(hZ.1 a ha b hb hab).2, (hZ.1 b hb c hc hbc).2] with ω hLF hLF'
  let : IsLocallyFiniteMeasure (Z a b ω) := hLF
  let : IsLocallyFiniteMeasure (Z b c ω) := hLF'
  exact (modifiedTwoBlockReadout_eq_of_locallyFinite E _ _ (w n) (compactTensorTest g g')).symm

end Critical2DKPZ.SHF.Tsai

end
