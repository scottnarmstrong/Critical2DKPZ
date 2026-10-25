/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.FlatEndpointHeatCollapse
public import Critical2DKPZ.NonGaussian.FlatEndpointMeasureConstruction
public import Critical2DKPZ.Differentiation.RandomHeat
import Critical2DKPZ.Analysis.Heat.Semigroup
import Mathlib.Tactic

/-! # Singularity of flat SHF endpoint measures -/

@[expose] public noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.Differentiation
open Critical2DKPZ.LocalSobolev Critical2DKPZ.SmallScales
open scoped ENNReal Topology

universe u

namespace Critical2DKPZ.NonGaussian

private theorem flatTerminalHeat_lintegral_eq (u : ℝ) (x : Plane)
    (μ : Measure (Plane × Plane)) :
    heatSmoothedDensity (μ.map Prod.snd) u x =
      ∫⁻ p, ENNReal.ofReal (heatKernel u (p.2 - x)) ∂μ := by
  change (∫⁻ y : Plane, (fun y => ENNReal.ofReal (heatKernel u (x - y))) y
      ∂Measure.map Prod.snd μ) = _
  rw [lintegral_map (f := fun y : Plane => ENNReal.ofReal (heatKernel u (x - y)))
    (g := Prod.snd)
    (ENNReal.measurable_ofReal.comp
      ((measurable_heatKernel u).comp (measurable_const.sub measurable_id))) measurable_snd]
  apply lintegral_congr
  intro p
  congr 1
  rw [show x - p.2 = -(p.2 - x) by abel, heatKernel_neg]

private theorem heatDensity_integral_eq_one {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (ν : RandomPlanarMeasure Ω)
    (hmean : ∀ A : Set Plane, MeasurableSet A →
      (∫⁻ ω, ν.measure ω A ∂P) = (volume : Measure Plane) A)
    {u : ℝ} (hu : 0 < u) (x : Plane) :
    (∫⁻ ω, heatSmoothedDensity (ν.measure ω) u x ∂P) = 1 := by
  let Q : Ω → Measure Plane := fun ω => ν.measure ω
  have hQ : AEMeasurable Q P := ν.measurable.aemeasurable
  have hbind : P.bind Q = (volume : Measure Plane) := by
    ext A hA
    rw [Measure.bind_apply hA hQ]
    exact hmean A hA
  let f : Plane → ℝ≥0∞ := fun y => ENNReal.ofReal (heatKernel u (x - y))
  have hf : Measurable f := by
    exact ENNReal.measurable_ofReal.comp
      ((measurable_heatKernel u).comp (measurable_const.sub measurable_id))
  have hfpos : ∀ y, 0 ≤ heatKernel u (x - y) := fun y => heatKernel_nonneg hu.le _
  have hInt : Integrable (fun y : Plane => heatKernel u (x - y)) (volume : Measure Plane) := by
    have hbase : Integrable (fun y : Plane => heatKernel u (y - x)) (volume : Measure Plane) :=
      (integrable_heatKernel hu).comp_sub_right x
    apply hbase.congr
    filter_upwards [] with y
    rw [show x - y = -(y - x) by abel, heatKernel_neg]
  have hkernel : (∫⁻ y, f y ∂(volume : Measure Plane)) = 1 := by
    have hreal : (∫ y, heatKernel u (x - y) ∂(volume : Measure Plane)) = 1 := by
      calc
        (∫ y, heatKernel u (x - y) ∂(volume : Measure Plane)) =
            ∫ y, heatKernel u (y - x) ∂(volume : Measure Plane) := by
              apply integral_congr_ae
              filter_upwards [] with y
              rw [show x - y = -(y - x) by abel, heatKernel_neg]
        _ = 1 := integral_heatKernel_sub hu x
    rw [← ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall fun y => hfpos y), hreal]
    norm_num
  calc
    (∫⁻ ω, heatSmoothedDensity (ν.measure ω) u x ∂P) =
        ∫⁻ ω, ∫⁻ y, f y ∂Q ω ∂P := rfl
    _ = ∫⁻ y, f y ∂P.bind Q := (Measure.lintegral_bind hQ hf.aemeasurable).symm
    _ = ∫⁻ y, f y ∂(volume : Measure Plane) := by rw [hbind]
    _ = 1 := hkernel

private theorem flatEndpoint_heatDensity_eq_pairing {Ω : Type u}
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    {s t u : ℝ} (hu : 0 < u) (x : Plane) (ω : Ω)
    (hfinite : heatSmoothedDensity ((Z s t ω).map Prod.snd) u x < ∞) :
    heatSmoothedDensity ((Z s t ω).map Prod.snd) u x =
      ENNReal.ofReal (shfPairing Z s t (fun _ => 1)
        (fun y => heatKernel u (y - x)) ω) := by
  let I : ℝ≥0∞ := ∫⁻ p, ENNReal.ofReal (heatKernel u (p.2 - x)) ∂Z s t ω
  have hMarginal := flatTerminalHeat_lintegral_eq u x (Z s t ω)
  have hIfinite : I < ∞ := by
    have h := hfinite
    rw [hMarginal] at h
    exact h
  have hX : shfPairing Z s t (fun _ => 1)
      (fun y => heatKernel u (y - x)) ω = I.toReal := by
    unfold shfPairing
    simp only [one_mul]
    dsimp [I]
    apply integral_eq_lintegral_of_nonneg_ae
    · exact Filter.Eventually.of_forall fun p => heatKernel_nonneg hu.le _
    · exact ((measurable_heatKernel u).comp (measurable_snd.sub_const x)).aestronglyMeasurable
  calc
    heatSmoothedDensity ((Z s t ω).map Prod.snd) u x = I := hMarginal
    _ = ENNReal.ofReal (shfPairing Z s t (fun _ => 1)
        (fun y => heatKernel u (y - x)) ω) := by
      rw [hX]
      exact (ENNReal.ofReal_toReal hIfinite.ne).symm

/-- At each fixed spatial point, heat regularizations of the Radon-valued flat endpoint measure
tend to zero in probability as the heat scale vanishes. -/
private theorem flatEndpoint_randomMeasure_heat_tendstoInMeasure_of
    (hVD : Smoothing.PropVDBound) (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hHeatStartLogInput : HeatStartLogAt ϑ P Z)
    (hsq : HeatStartSqAt P Z) (hdense : DenseSHFAt ϑ P Z)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (ν : RandomPlanarMeasure Ω) (hν : ∀ᵐ ω ∂P,
      ν.measure ω = (Z s t ω).map Prod.snd)
    (hmean : ∀ A : Set Plane, MeasurableSet A →
      (∫⁻ ω, ν.measure ω A ∂P) = (volume : Measure Plane) A) :
    ∀ x : Plane, TendstoInMeasure P
      (fun u ω => heatProbabilityValue (heatSmoothedDensity (ν.measure ω) u x))
      (𝓝[>] (0 : ℝ)) (fun _ => 0) := by
  have hcollapse := shf_heatDensity_tendstoInMeasure_of hVD ϑ P Z hZ hsym hHeatStartLogInput hsq hdense hs hst
  intro x ε hε
  by_cases hεtop : ε = ∞
  · simp [hεtop]
  have hεne : ε ≠ 0 := ne_of_gt hε
  let ε' : NNReal := ε.toNNReal
  have hε' : (ε' : ℝ≥0∞) = ε := ENNReal.coe_toNNReal hεtop
  have hε'pos : 0 < ε' := ENNReal.toNNReal_pos hεne hεtop
  let ε₀ : NNReal := min ε' (1 / 2)
  have hε₀ : 0 < ε₀ := lt_min hε'pos (by norm_num)
  have hε₀one : ε₀ < 1 := by
    dsimp [ε₀]
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hXtail := (tendstoInMeasure_iff_norm.mp (hcollapse x))
    (ε₀ : ℝ) (by exact_mod_cast hε₀)
  have hTailBound : ∀ᶠ u in 𝓝[>] (0 : ℝ),
      P {ω | ε ≤ edist (heatProbabilityValue (heatSmoothedDensity (ν.measure ω) u x)) 0} ≤
        P {ω | (ε₀ : ℝ) ≤ ‖shfPairing Z s t (fun _ => 1)
          (fun y => heatKernel u (y - x)) ω - 0‖} := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hfinite : ∀ᵐ ω ∂P, heatSmoothedDensity (ν.measure ω) u x < ∞ := by
      have hmass := heatDensity_integral_eq_one P ν hmean hu x
      have hnotTop : (∫⁻ ω, heatSmoothedDensity (ν.measure ω) u x ∂P) ≠ ∞ := by
        rw [hmass]
        simp
      exact ae_lt_top (measurable_heatSmoothedDensity ν u x) hnotTop
    have hpairEq : ∀ᵐ ω ∂P,
        heatSmoothedDensity (ν.measure ω) u x =
          ENNReal.ofReal (shfPairing Z s t (fun _ => 1)
            (fun y => heatKernel u (y - x)) ω) := by
      filter_upwards [hν, hfinite] with ω hω hωfinite
      have hωfinite' : heatSmoothedDensity ((Z s t ω).map Prod.snd) u x < ∞ := by
        rw [← hω]
        exact hωfinite
      rw [hω]
      exact flatEndpoint_heatDensity_eq_pairing Z hu x ω hωfinite'
    have hpairNonneg (ω : Ω) :
        0 ≤ shfPairing Z s t (fun _ => 1)
          (fun y => heatKernel u (y - x)) ω := by
      unfold shfPairing
      simp only [one_mul]
      exact integral_nonneg fun p => heatKernel_nonneg hu.le _
    have hsubset : ∀ᵐ ω ∂P,
        ε ≤ edist (heatProbabilityValue (heatSmoothedDensity (ν.measure ω) u x)) 0 →
        (ε₀ : ℝ) ≤ ‖shfPairing Z s t (fun _ => 1)
          (fun y => heatKernel u (y - x)) ω - 0‖ := by
      filter_upwards [hpairEq] with ω hEq
      intro hbig
      have hbig' : ε' ≤ heatProbabilityValue
          (heatSmoothedDensity (ν.measure ω) u x) := by
        have hco : (ε' : ℝ≥0∞) ≤
            (heatProbabilityValue (heatSmoothedDensity (ν.measure ω) u x) : ℝ≥0∞) := by
          rw [← hε'] at hbig
          simpa only [edist_nndist, NNReal.nndist_zero_eq_val'] using hbig
        exact (ENNReal.coe_le_coe).mp hco
      have hsmall : ε₀ ≤ heatProbabilityValue
          (heatSmoothedDensity (ν.measure ω) u x) := by
        exact (min_le_left _ _).trans hbig'
      by_contra hnot
      have hXlt : shfPairing Z s t (fun _ => 1)
          (fun y => heatKernel u (y - x)) ω < ε₀ := by
        have habs := lt_of_not_ge hnot
        simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg (hpairNonneg ω)] using habs
      have hoflt : ENNReal.ofReal (shfPairing Z s t (fun _ => 1)
          (fun y => heatKernel u (y - x)) ω) < (ε₀ : ℝ≥0∞) :=
        (ENNReal.ofReal_lt_coe_iff (hpairNonneg ω)).2 hXlt
      have hcaplt := (heatProbabilityValue_lt_iff hε₀one).2 (by simpa [hEq] using hoflt)
      rw [← hEq] at hcaplt
      exact (not_lt_of_ge hsmall) hcaplt
    exact measure_mono_ae hsubset
  exact ENNReal.tendsto_nhds_zero.mpr fun η hη => by
    filter_upwards [hTailBound, hXtail.eventually (Iio_mem_nhds hη)] with u hle hsmall
    exact le_of_lt (lt_of_le_of_lt hle hsmall)

/-- Every deterministic finite measure is almost surely mutually singular with the flat
terminal SHF marginal; see KPZ Lemma 9.7. -/
theorem shf_flatEndpoint_mutuallySingular_of (hVD : Smoothing.PropVDBound) (ϑ : ℝ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hHeatStartLogInput : HeatStartLogAt ϑ P Z)
    (hsq : HeatStartSqAt P Z) (hdense : DenseSHFAt ϑ P Z)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (μ : Measure Plane) [IsFiniteMeasure μ] :
    ∀ᵐ ω ∂P, μ ⟂ₘ (Z s t ω).map Prod.snd := by
  obtain ⟨ν, hν, hmean⟩ := exists_flatEndpoint_randomPlanarMeasure_of ϑ P Z hZ hdense hs hst
  have hheat := flatEndpoint_randomMeasure_heat_tendstoInMeasure_of hVD ϑ P Z hZ
    hsym hHeatStartLogInput hsq hdense hs hst ν hν hmean
  have hsing := ae_randomMeasure_mutuallySingular_finiteMeasure_of_mean_and_heat_tendstoInMeasure
    P ν μ hmean hheat
  filter_upwards [hsing, hν] with ω hsingω hνeq
  simpa [hνeq] using hsingω

end Critical2DKPZ.NonGaussian

end
