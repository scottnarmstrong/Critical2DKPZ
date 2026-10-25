/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.LocNegSobolevBorel
public import Critical2DKPZ.Analysis.Sobolev.Rellich.DistributionRepresentation
public import Critical2DKPZ.Analysis.Sobolev.Rellich.FrozenDistributionBound

/-! # Continuous test pairings on the finite local Sobolev carrier -/

@[expose] public section

noncomputable section

open Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace Critical2DKPZ.Analysis.Sobolev

/-- Pairing with a fixed test function is continuous on the finite local Sobolev carrier. -/
theorem continuous_pairing_locNegSobolevCarrier (s : ℝ) (φ : TestFn) :
    Continuous (fun T : LocNegSobolevCarrier s => T.1.toDistr φ) := by
  obtain ⟨m, hm⟩ := exists_localizer_eq_one_on_compact φ.hasCompactSupport.isCompact
  obtain ⟨B, _, hB⟩ := Rellich.exists_test_sobolev_norm_bound s φ
  let C : ℝ≥0∞ := (Rellich.sobolevNormSq 2 s (fun x => (φ x : ℝ))) ^ (1 / 2 : ℝ)
  have hC : C ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    (ne_of_lt (hB.trans_lt ENNReal.ofReal_lt_top))
  apply continuous_iff_continuousAt.mpr
  intro U
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hsq := tendsto_localNegSobolevSq_of_locNegSobolevTop
    (continuous_subtype_val.tendsto U) (localizer m)
  have hroot : Tendsto (fun T : LocNegSobolevCarrier s =>
      (localNegSobolevSq s (T.1.toDistr - U.1.toDistr) (localizer m)) ^ (1 / 2 : ℝ))
      (𝓝 U) (𝓝 0) := by
    simpa using hsq.ennrpow_const (1 / 2 : ℝ)
  have hprod : Tendsto (fun T : LocNegSobolevCarrier s => C *
      (localNegSobolevSq s (T.1.toDistr - U.1.toDistr) (localizer m)) ^ (1 / 2 : ℝ))
      (𝓝 U) (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hroot (Or.inr hC)
  have hbound (T : LocNegSobolevCarrier s) :
      ENNReal.ofReal |T.1.toDistr φ - U.1.toDistr φ| ≤ C *
        (localNegSobolevSq s (T.1.toDistr - U.1.toDistr) (localizer m)) ^ (1 / 2 : ℝ) := by
    exact Rellich.distribution_pairing_le_localNegSobolev_product s
      (T.1.toDistr - U.1.toDistr) (localizer m) φ (hm m le_rfl)
  have hz : Tendsto (fun T : LocNegSobolevCarrier s =>
      ENNReal.ofReal |T.1.toDistr φ - U.1.toDistr φ|) (𝓝 U) (𝓝 0) := by
    apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    filter_upwards [(ENNReal.tendsto_nhds_zero.mp hprod) ε hε] with T hT
    exact (hbound T).trans hT
  have hr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hz
  simpa only [Function.comp_def, ENNReal.toReal_zero,
    ENNReal.toReal_ofReal (abs_nonneg _), Real.dist_eq] using hr

/-- Every localized energy, including an energy stronger than the carrier order, is measurable. -/
theorem measurable_localEnergy_locNegSobolevCarrier (s a : ℝ) (χ : TestFn) :
    Measurable (fun T : LocNegSobolevCarrier s => localNegSobolevSq a T.1.toDistr χ) :=
  measurable_localNegSobolevSq (fun φ => (continuous_pairing_locNegSobolevCarrier s φ).measurable)
    a χ

end Critical2DKPZ.Analysis.Sobolev

end
