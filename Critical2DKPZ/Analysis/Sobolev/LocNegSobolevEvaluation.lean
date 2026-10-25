/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.LocNegSobolevFourierReadout
public import Critical2DKPZ.Analysis.Sobolev.Rellich.FrozenDistributionBound
public import Critical2DKPZ.Analysis.Sobolev.Rellich.DistributionRepresentation
public import Mathlib.Topology.Separation.Hausdorff

/-! # Continuous test evaluations on the finite local Sobolev carrier -/

@[expose] public section

noncomputable section

open Filter MeasureTheory TopologicalSpace
open scoped ENNReal FourierTransform Topology

namespace Critical2DKPZ.Analysis.Sobolev

/-- Convergence in the local Sobolev topology implies convergence of every test pairing. -/
theorem tendsto_locNegSobolevCarrier_testEvaluation {ι : Type*} {l : Filter ι} {s : ℝ}
    {S : ι → LocNegSobolevCarrier s} {T : LocNegSobolevCarrier s}
    (h : Tendsto S l (𝓝 T)) (φ : TestFn) :
    Tendsto (fun i => (S i).1.toDistr φ) l (𝓝 (T.1.toDistr φ)) := by
  obtain ⟨N, hN⟩ := Critical2DKPZ.exists_localizer_eq_one_on_compact
    φ.hasCompactSupport.isCompact
  obtain ⟨B, hB, hSob⟩ := Rellich.exists_test_sobolev_norm_bound s φ
  have hambient : Tendsto (fun i => (S i).1) l (𝓝 T.1) :=
    continuous_subtype_val.continuousAt.tendsto.comp h
  have hsq := Critical2DKPZ.tendsto_localNegSobolevSq_of_locNegSobolevTop
    hambient (localizer N)
  have hnorm : Tendsto (fun i => Critical2DKPZ.localNegSobolevENorm s
      ((S i).1.toDistr - T.1.toDistr) (localizer N)) l (𝓝 0) := by
    simpa only [← Critical2DKPZ.localNegSobolevENorm_eq_rpow,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using
      hsq.ennrpow_const (1 / 2 : ℝ)
  let C : ℝ≥0∞ :=
    (Rellich.sobolevNormSq 2 s (fun x => (φ x : ℝ))) ^ ((1 : ℝ) / 2)
  have hC : C < ⊤ := by
    apply (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).2
    exact lt_of_le_of_lt hSob (ENNReal.ofReal_lt_top)
  have hprodMap : Tendsto (fun x : ℝ≥0∞ => C * x) (𝓝 0) (𝓝 0) := by
    have hp := ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos
      (ne_of_lt hC) (by norm_num : (0 : ℝ) < 1)
    simpa using hp
  have hprod : Tendsto (fun i => C * Critical2DKPZ.localNegSobolevENorm s
      ((S i).1.toDistr - T.1.toDistr) (localizer N)) l (𝓝 0) := hprodMap.comp hnorm
  have hpair : Tendsto (fun i => ENNReal.ofReal
      (|((S i).1.toDistr - T.1.toDistr) φ|)) l (𝓝 0) := by
    apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    have hev := ENNReal.tendsto_nhds_zero.mp hprod ε hε
    filter_upwards [hev] with i hi
    have hχ : ∀ x ∈ tsupport φ, localizer N x = 1 := fun x hx => hN N le_rfl x hx
    have hbound := Rellich.distribution_pairing_le_localNegSobolev_product s
      ((S i).1.toDistr - T.1.toDistr) (localizer N) φ hχ
    have hbound' : ENNReal.ofReal
        (|((S i).1.toDistr - T.1.toDistr) φ|) ≤ C *
          Critical2DKPZ.localNegSobolevENorm s
            ((S i).1.toDistr - T.1.toDistr) (localizer N) := by
      simpa only [C, ← Critical2DKPZ.localNegSobolevENorm_eq_rpow] using hbound
    exact hbound'.trans hi
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hev := (ENNReal.tendsto_nhds_zero.mp hpair) (ENNReal.ofReal (ε / 2))
    (ENNReal.ofReal_pos.mpr hhalf)
  filter_upwards [hev] with i hi
  have hreal : |((S i).1.toDistr - T.1.toDistr) φ| ≤ ε / 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp hi
  have hdist : dist ((S i).1.toDistr φ) (T.1.toDistr φ) =
      |((S i).1.toDistr - T.1.toDistr) φ| := by
    rw [Real.dist_eq]
    simp only [sub_apply]
  rw [hdist]
  linarith

/-- Evaluation at a fixed test function is continuous on the finite local Sobolev carrier. -/
theorem continuous_locNegSobolevCarrier_testEvaluation (s : ℝ) (φ : TestFn) :
    Continuous (fun T : LocNegSobolevCarrier s => T.1.toDistr φ) := by
  apply continuous_iff_continuousAt.mpr
  intro T
  exact tendsto_locNegSobolevCarrier_testEvaluation tendsto_id φ

/-- The full family of test evaluations separates points of the carrier. -/
def locNegSobolevCarrierTestReadout (s : ℝ) (T : LocNegSobolevCarrier s) :
    TestFn → ℝ := fun φ => T.1.toDistr φ

/-- Evaluation of a local negative Sobolev distribution on a test function is continuous. -/
theorem continuous_locNegSobolevCarrierTestReadout (s : ℝ) :
    Continuous (locNegSobolevCarrierTestReadout s) := by
  apply continuous_pi
  intro φ
  exact continuous_locNegSobolevCarrier_testEvaluation s φ

/-- Test-function evaluations determine a local negative Sobolev distribution uniquely. -/
theorem injective_locNegSobolevCarrierTestReadout (s : ℝ) :
    Function.Injective (locNegSobolevCarrierTestReadout s) := by
  intro T U h
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro φ
  exact congrFun h φ

private structure LocNegSobolevCarrierReadoutSource (s : ℝ) where
  toCarrier : LocNegSobolevCarrier s

private def locNegSobolevCarrierReadoutSourceMap (s : ℝ)
    (T : LocNegSobolevCarrierReadoutSource s) : TestFn → ℝ :=
  locNegSobolevCarrierTestReadout s T.toCarrier


/-- Test-function evaluations generate the Borel sigma algebra on the finite-energy local Sobolev space. -/
theorem measurableSpace_locNegSobolevCarrier_eq_comap_testReadout (s : ℝ)
    [Fact (0 ≤ s)] :
    (inferInstance : MeasurableSpace (LocNegSobolevCarrier s)) =
      MeasurableSpace.comap (locNegSobolevCarrierTestReadout s)
        (MeasurableSpace.pi : MeasurableSpace (TestFn → ℝ)) := by
  let Ω := LocNegSobolevCarrierReadoutSource s
  let m : MeasurableSpace Ω :=
    MeasurableSpace.comap (locNegSobolevCarrierReadoutSourceMap s)
      (MeasurableSpace.pi : MeasurableSpace (TestFn → ℝ))
  have hcoord : ∀ φ : TestFn,
      @Measurable Ω ℝ m inferInstance
        (fun T => T.toCarrier.1.toDistr φ) := by
    intro φ
    have hF : @Measurable Ω (TestFn → ℝ) m
        (MeasurableSpace.pi : MeasurableSpace (TestFn → ℝ))
        (locNegSobolevCarrierReadoutSourceMap s) :=
      measurable_iff_comap_le.mpr le_rfl
    exact (measurable_pi_iff.mp hF) φ
  have hval : @Measurable Ω (LocNegSobolevCarrier s) m inferInstance
      (fun T => T.toCarrier) := by
    exact measurable_locNegSobolevCarrier_of_testwise
      (fun T : Ω => T.toCarrier.1.toDistr)
      (fun φ => hcoord φ)
      (fun T => T.toCarrier.2)
  have hvalLe : MeasurableSpace.comap (fun T : Ω => T.toCarrier)
      (inferInstance : MeasurableSpace (LocNegSobolevCarrier s)) ≤ m :=
    hval.comap_le
  have hBorelLe : (inferInstance : MeasurableSpace (LocNegSobolevCarrier s)) ≤
      MeasurableSpace.comap (locNegSobolevCarrierTestReadout s)
        (MeasurableSpace.pi : MeasurableSpace (TestFn → ℝ)) := by
    intro U hU
    have hpreVal : MeasurableSet[
        MeasurableSpace.comap (fun T : Ω => T.toCarrier)
          (inferInstance : MeasurableSpace (LocNegSobolevCarrier s))]
        ((fun T : Ω => T.toCarrier) ⁻¹' U) :=
      MeasurableSpace.measurableSet_comap.mpr ⟨U, hU, rfl⟩
    have hpre : MeasurableSet[m] ((fun T : Ω => T.toCarrier) ⁻¹' U) :=
      hvalLe _ hpreVal
    obtain ⟨B, hB, hEq⟩ := MeasurableSpace.measurableSet_comap.mp hpre
    apply MeasurableSpace.measurableSet_comap.mpr
    refine ⟨B, hB, ?_⟩
    ext T
    let x : Ω := ⟨T⟩
    have hx := congrArg (fun S : Set Ω => x ∈ S) hEq
    simpa [x, locNegSobolevCarrierReadoutSourceMap,
      locNegSobolevCarrierTestReadout] using hx
  have hreadoutMeas : @Measurable (LocNegSobolevCarrier s) (TestFn → ℝ)
      (inferInstance : MeasurableSpace (LocNegSobolevCarrier s))
      (MeasurableSpace.pi : MeasurableSpace (TestFn → ℝ))
      (locNegSobolevCarrierTestReadout s) := by
    apply measurable_pi_iff.mpr
    intro φ
    exact (continuous_locNegSobolevCarrier_testEvaluation s φ).measurable
  exact le_antisymm hBorelLe hreadoutMeas.comap_le

instance instT2SpaceLocNegSobolevCarrier (s : ℝ) : T2Space (LocNegSobolevCarrier s) :=
  T2Space.of_injective_continuous
    (injective_locNegSobolevCarrierTestReadout s)
    (continuous_locNegSobolevCarrierTestReadout s)

end Critical2DKPZ.Analysis.Sobolev

end
