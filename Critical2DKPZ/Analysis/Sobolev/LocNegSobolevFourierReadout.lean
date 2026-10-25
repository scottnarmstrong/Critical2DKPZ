/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.LocNegSobolevBorel
public import Critical2DKPZ.Analysis.Sobolev.LocalizerEnergy
public import Critical2DKPZ.Analysis.Sobolev.WeightedConvolutionRepresentation
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.Maps.Basic

/-! A finite-energy distribution maps to its localized weighted Fourier transforms in a countable product of separable L² spaces, and this map induces the local negative Sobolev topology. -/

@[expose] public section

set_option linter.style.haveILetI false

noncomputable section

open Filter MeasureTheory TopologicalSpace
open scoped ENNReal FourierTransform Topology

namespace Critical2DKPZ.Analysis.Sobolev

private instance instLpProbabilityExponentOneLe : Fact (1 ≤ (2 : ℝ≥0∞)) :=
  ⟨by norm_num⟩

private instance instLpProbabilityExponentNeTop : Fact ((2 : ℝ≥0∞) ≠ ∞) :=
  ⟨by simp⟩

private theorem isSeparable_negSobolevFourierMeasure (a : ℝ) :
    IsSeparable (Critical2DKPZ.negSobolevFourierMeasure a) := by
  letI : MeasurableSpace.CountablyGenerated Critical2DKPZ.Plane := inferInstance
  have hsfinite : SFinite (Critical2DKPZ.negSobolevFourierMeasure a) := by
    change SFinite (volume.withDensity _)
    infer_instance
  letI : SFinite (Critical2DKPZ.negSobolevFourierMeasure a) := hsfinite
  infer_instance

private theorem secondCountable_lp_negSobolevFourierMeasure (a : ℝ) :
    SecondCountableTopology
      (Lp ℂ 2 (Critical2DKPZ.negSobolevFourierMeasure a)) := by
  letI : IsSeparable (Critical2DKPZ.negSobolevFourierMeasure a) :=
    isSeparable_negSobolevFourierMeasure a
  infer_instance

/-- The countable localizer Fourier readout of a finite-energy distribution. -/
def locNegSobolevFourierReadout (s : ℝ) (T : LocNegSobolevCarrier s) :
    ℕ → Lp ℂ 2 (Critical2DKPZ.negSobolevFourierMeasure s) := fun n =>
  let f : Plane → ℂ := fun ξ =>
    Critical2DKPZ.localizedFourier T.1.toDistr (localizer n) ξ
  let hf : MemLp f 2 (Critical2DKPZ.negSobolevFourierMeasure s) := by
    change Critical2DKPZ.localNegSobolevENorm s T.1.toDistr (localizer n) < ⊤
    exact (Critical2DKPZ.localNegSobolevENorm_lt_top_iff s T.1.toDistr
      (localizer n)).2 (T.2 (localizer n))
  hf.toLp f

/-- The L² distance between two localized Fourier coordinates equals their localized negative Sobolev seminorm. -/
theorem edist_locNegSobolevFourierReadout (s : ℝ) (T U : LocNegSobolevCarrier s)
    (n : ℕ) :
    edist (locNegSobolevFourierReadout s T n) (locNegSobolevFourierReadout s U n) =
      Critical2DKPZ.localNegSobolevENorm s (T.1.toDistr - U.1.toDistr) (localizer n) := by
  let fT : Plane → ℂ := fun ξ =>
    Critical2DKPZ.localizedFourier T.1.toDistr (localizer n) ξ
  let fU : Plane → ℂ := fun ξ =>
    Critical2DKPZ.localizedFourier U.1.toDistr (localizer n) ξ
  have hT : MemLp fT 2 (Critical2DKPZ.negSobolevFourierMeasure s) := by
    change Critical2DKPZ.localNegSobolevENorm s T.1.toDistr (localizer n) < ⊤
    exact (Critical2DKPZ.localNegSobolevENorm_lt_top_iff s T.1.toDistr
      (localizer n)).2 (T.2 (localizer n))
  have hU : MemLp fU 2 (Critical2DKPZ.negSobolevFourierMeasure s) := by
    change Critical2DKPZ.localNegSobolevENorm s U.1.toDistr (localizer n) < ⊤
    exact (Critical2DKPZ.localNegSobolevENorm_lt_top_iff s U.1.toDistr
      (localizer n)).2 (U.2 (localizer n))
  rw [show locNegSobolevFourierReadout s T n = hT.toLp fT by rfl,
    show locNegSobolevFourierReadout s U n = hU.toLp fU by rfl,
    MeasureTheory.Lp.edist_toLp_toLp]
  change eLpNorm (fT - fU) 2 (Critical2DKPZ.negSobolevFourierMeasure s) = _
  have hdiff : fT - fU = fun ξ =>
      Critical2DKPZ.localizedFourier (T.1.toDistr - U.1.toDistr) (localizer n) ξ := by
    funext ξ
    dsimp [fT, fU, Critical2DKPZ.localizedFourier]
    simp only [sub_apply, Complex.ofReal_sub]
    ring
  rw [hdiff]
  rfl

/-- A family of finite-energy distributions converges in the local Sobolev topology if and only if every localized Fourier coordinate converges in L². -/
theorem tendsto_locNegSobolevFourierReadout_iff {ι : Type*} {l : Filter ι} {s : ℝ}
    (hs : 0 ≤ s)
    {S : ι → LocNegSobolevCarrier s} {T : LocNegSobolevCarrier s} :
    Tendsto (fun i => locNegSobolevFourierReadout s (S i)) l
      (𝓝 (locNegSobolevFourierReadout s T)) ↔ Tendsto S l (𝓝 T) := by
  constructor
  · intro h
    rw [tendsto_subtype_rng]
    apply Critical2DKPZ.tendsto_locNegSobolevTop_of_localNegSobolevSq
    intro φ
    obtain ⟨N, hN⟩ := exists_testFnMul_localizer_eq φ
    have hcoord := (tendsto_pi_nhds.mp h) N
    rw [tendsto_iff_edist_tendsto_0] at hcoord
    have hnorm : Tendsto (fun i => Critical2DKPZ.localNegSobolevENorm s
        ((S i).1.toDistr - T.1.toDistr) (localizer N)) l (𝓝 0) := by
      simpa only [edist_locNegSobolevFourierReadout] using hcoord
    have hsqLocal : Tendsto (fun i => Critical2DKPZ.localNegSobolevSq s
        ((S i).1.toDistr - T.1.toDistr) (localizer N)) l (𝓝 0) := by
      simpa only [Critical2DKPZ.localNegSobolevENorm_sq, ENNReal.rpow_two,
        ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] using
        hnorm.ennrpow_const (2 : ℝ)
    let A : ι → Distr := fun i => (S i).1.toDistr - T.1.toDistr
    have hmemA : ∀ i, Critical2DKPZ.MemLocalNegSobolev s (A i) := by
      intro i
      change Critical2DKPZ.MemLocalNegSobolev s ((S i).1.toDistr - T.1.toDistr)
      have hsum := (S i).2.add T.2.neg
      convert hsum using 1; abel
    let K : ℝ≥0∞ := ENNReal.ofReal
      ((∫ η : Plane, ‖(𝓕 (testFnSchwartz φ)) η‖ *
        Real.sqrt (2 ^ s * (1 + (2 * Real.pi * ‖η‖) ^ 2) ^ s)) ^ 2)
    have hmul0 : Tendsto (fun x : ℝ≥0∞ => K * x) (𝓝 0) (𝓝 0) := by
      have hpow := ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos
        (show K ≠ ∞ by simp [K]) (by norm_num : (0 : ℝ) < 1)
      simpa using hpow
    have hprod : Tendsto (fun i => K * Critical2DKPZ.localNegSobolevSq s
        (A i) (localizer N)) l (𝓝 0) := hmul0.comp hsqLocal
    apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    have hev := (ENNReal.tendsto_nhds_zero.mp hprod) ε hε
    filter_upwards [hev] with i hi
    have hfinite : Critical2DKPZ.localNegSobolevSq s (A i) (localizer N) < ⊤ :=
      hmemA i (localizer N)
    have hmult := Critical2DKPZ.Analysis.Sobolev.localNegSobolevSq_testFnMul_le
      hs (A i) (localizer N) φ hfinite
    have hmul : testFnMul φ (localizer N) = φ := by
      rw [testFnMul_comm]
      exact hN N le_rfl
    have hbound : Critical2DKPZ.localNegSobolevSq s (A i) φ ≤
        K * Critical2DKPZ.localNegSobolevSq s (A i) (localizer N) := by
      simpa [K, hmul] using hmult.2
    exact hbound.trans hi
  · intro h
    rw [tendsto_pi_nhds]
    intro n
    rw [tendsto_iff_edist_tendsto_0]
    have hambient : Tendsto (fun i => (S i).1) l (𝓝 T.1) :=
      continuous_subtype_val.continuousAt.tendsto.comp h
    have hsq := Critical2DKPZ.tendsto_localNegSobolevSq_of_locNegSobolevTop
      hambient (localizer n)
    have hnorm : Tendsto (fun i => Critical2DKPZ.localNegSobolevENorm s
        ((S i).1.toDistr - T.1.toDistr) (localizer n)) l (𝓝 0) := by
      simpa only [← Critical2DKPZ.localNegSobolevENorm_eq_rpow,
        ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using
        hsq.ennrpow_const (1 / 2 : ℝ)
    simpa only [edist_locNegSobolevFourierReadout] using hnorm

/-- The local Sobolev carrier topology is the topology induced by the countable Fourier readout. -/
theorem isInducing_locNegSobolevFourierReadout (s : ℝ) (hs : 0 ≤ s) :
    Topology.IsInducing (locNegSobolevFourierReadout s) := by
  apply Topology.isInducing_iff_nhds.mpr
  intro T
  apply le_antisymm
  · have hcont : Tendsto (locNegSobolevFourierReadout s) (𝓝 T)
        (𝓝 (locNegSobolevFourierReadout s T)) :=
      (tendsto_locNegSobolevFourierReadout_iff hs).2 tendsto_id
    exact hcont.le_comap
  · let l := Filter.comap (locNegSobolevFourierReadout s)
      (𝓝 (locNegSobolevFourierReadout s T))
    have hread : Tendsto (locNegSobolevFourierReadout s) l
        (𝓝 (locNegSobolevFourierReadout s T)) := tendsto_comap
    have hid : Tendsto id l (𝓝 T) :=
      (tendsto_locNegSobolevFourierReadout_iff hs).1 hread
    change l ≤ 𝓝 T
    exact hid

/-- At every nonnegative Sobolev order, the space of finite-energy distributions is second countable. -/
theorem secondCountable_locNegSobolevCarrier (s : ℝ) (hs : 0 ≤ s) :
    SecondCountableTopology (LocNegSobolevCarrier s) := by
  letI : ∀ n : ℕ, SecondCountableTopology
      (Lp ℂ 2 (Critical2DKPZ.negSobolevFourierMeasure s)) := fun _ =>
    secondCountable_lp_negSobolevFourierMeasure s
  haveI : SecondCountableTopology
      (ℕ → Lp ℂ 2 (Critical2DKPZ.negSobolevFourierMeasure s)) := inferInstance
  exact (isInducing_locNegSobolevFourierReadout s hs).secondCountableTopology

instance instSecondCountableLocNegSobolevCarrier (s : ℝ) [Fact (0 ≤ s)] :
    SecondCountableTopology (LocNegSobolevCarrier s) :=
  secondCountable_locNegSobolevCarrier s Fact.out

end Critical2DKPZ.Analysis.Sobolev

end
