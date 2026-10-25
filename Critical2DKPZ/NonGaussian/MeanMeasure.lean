/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.CompactMean
public import Critical2DKPZ.SHF.Tsai.MixedBlockJointMoments
public import Critical2DKPZ.RandomMeasure.GeneralTests
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Mathlib.Tactic

/-! # The exact annealed measure of a critical SHF block -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported ENNReal Topology

namespace Critical2DKPZ.NonGaussian

private theorem integral_heatBlock_eq (τ : ℝ) (hτ : 0 ≤ τ) (f : Plane × Plane → ℝ) :
    (∫ p, f p ∂heatBlock τ) = ∫ p, f p * heatKernel τ (p.2 - p.1) := by
  unfold heatBlock
  have hden : Measurable (fun p : Plane × Plane => ENNReal.ofReal (heatKernel τ (p.2 - p.1))) := by
    exact ((measurable_heatKernel τ).comp (measurable_snd.sub measurable_fst)).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hden
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    change (ENNReal.ofReal (heatKernel τ (p.2 - p.1))).toReal • f p = f p * heatKernel τ (p.2 - p.1)
    rw [ENNReal.toReal_ofReal (heatKernel_nonneg hτ _), smul_eq_mul, mul_comm]

/-- The expected measure of a positive-time critical SHF increment equals
the heat block of the same duration. -/
theorem isCriticalSHF_bind_eq_heatBlock (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    P.bind (Z s t) = heatBlock (t - s) := by
  let μ : Measure (Plane × Plane) := P.bind (Z s t)
  let K : CompactExhaustion (Plane × Plane) := RandomMeasure.vagueCompactExhaustion (Plane × Plane)
  have hμtest (f : C_c(Plane × Plane, ℝ)) (hf : ∀ p, 0 ≤ f p) :
      (∫⁻ p, ENNReal.ofReal (f p) ∂μ) = ENNReal.ofReal (∫ p, f p ∂heatBlock (t - s)) := by
    have hfirst := integrable_and_integral_compactPairing_eq ϑ P Z hZ hs hst f hf
    have hInner : ∀ᵐ ω ∂P,
        (∫⁻ p, ENNReal.ofReal (f p) ∂Z s t ω) = ENNReal.ofReal (∫ p, f p ∂Z s t ω) := by
      filter_upwards [hZ.2.1 s t hs hst] with ω hω
      let : IsLocallyFiniteMeasure (Z s t ω) := hω.1
      exact (ofReal_integral_eq_lintegral_ofReal
        (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)
        (Filter.Eventually.of_forall hf)).symm
    calc
      _ = ∫⁻ ω, ∫⁻ p, ENNReal.ofReal (f p) ∂Z s t ω ∂P :=
        Measure.lintegral_bind (hZ.1 s t hs hst).aemeasurable f.continuous.measurable.ennreal_ofReal.aemeasurable
      _ = ∫⁻ ω, ENNReal.ofReal (∫ p, f p ∂Z s t ω) ∂P := lintegral_congr_ae hInner
      _ = ENNReal.ofReal (∫ ω, ∫ p, f p ∂Z s t ω ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hfirst.1
          (Filter.Eventually.of_forall fun _ => integral_nonneg hf)).symm
      _ = _ := by rw [hfirst.2, integral_heatBlock_eq (t - s) (sub_nonneg.mpr hst.le)]
  have hμlf : IsLocallyFiniteMeasure μ := by
    constructor
    intro p
    obtain ⟨n, hSub⟩ := K.exists_superset_of_isCompact (isCompact_closedBall p 1)
    let f : C_c(Plane × Plane, ℝ) := RandomMeasure.vagueMassTest K n
    have hf := RandomMeasure.vagueMassTest_spec K n
    have hKn : MeasurableSet (K n) := (K.isCompact n).measurableSet
    have hMass : μ (K n) ≤ ∫⁻ q, ENNReal.ofReal (f q) ∂μ := by
      rw [← lintegral_indicator_one hKn]
      apply lintegral_mono
      intro q
      by_cases hq : q ∈ K n
      · rw [Set.indicator_of_mem hq]
        change (1 : ℝ≥0∞) ≤ ENNReal.ofReal (f q)
        have hfq : f q = 1 := hf.2.2.1 q hq
        rw [hfq]
        norm_num
      · simp only [Set.indicator_of_notMem hq, zero_le]
    have hFinite : (∫⁻ q, ENNReal.ofReal (f q) ∂μ) < ⊤ := by
      rw [hμtest f hf.1]
      exact ENNReal.ofReal_lt_top
    exact ⟨Metric.closedBall p 1, Metric.closedBall_mem_nhds p (by norm_num),
      (measure_mono hSub).trans_lt (hMass.trans_lt hFinite)⟩
  let : IsLocallyFiniteMeasure μ := hμlf
  let : IsLocallyFiniteMeasure (heatBlock (t - s)) := locallyFinite_heatBlock (t - s)
  let : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  let : (heatBlock (t - s)).Regular :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure (heatBlock (t - s))
  apply Measure.ext_of_integral_eq_on_compactlySupported_nnreal
  intro f
  have hNonneg (p : Plane × Plane) : 0 ≤ f.toReal p := by
    rw [CompactlySupportedContinuousMap.toReal_apply]
    exact (f p).coe_nonneg
  have h := hμtest f.toReal hNonneg
  have hInt : Integrable (fun p => f.toReal p) μ :=
    f.toReal.continuous.integrable_of_hasCompactSupport f.toReal.hasCompactSupport
  rw [← ofReal_integral_eq_lintegral_ofReal hInt (Filter.Eventually.of_forall hNonneg)] at h
  simpa only [CompactlySupportedContinuousMap.toReal_apply] using
    (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg hNonneg) (integral_nonneg hNonneg)).mp h

end Critical2DKPZ.NonGaussian

end
