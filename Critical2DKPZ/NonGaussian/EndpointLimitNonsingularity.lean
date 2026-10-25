/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.RetainedEndpointMeanBounds
public import Critical2DKPZ.NonGaussian.LaterComparisonCountableSeparation
public import Critical2DKPZ.NonGaussian.EndpointLimitMean
public import Critical2DKPZ.NonGaussian.FlatTerminalMean
import Critical2DKPZ.NonGaussian.FlatEndpointMeasureConstruction
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Kernel.MeasurableIntegral
import Critical2DKPZ.Spectral.BochnerSchwartzRiesz
import Mathlib.Tactic

/-! # Endpoint limits and the later flat endpoint measure are not mutually singular with positive probability -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.LocalSobolev Critical2DKPZ.SmallScales
open Critical2DKPZ.Spectral
open scoped CompactlySupported ENNReal Topology
open CompactlySupportedContinuousMap

namespace Critical2DKPZ.NonGaussian

universe u

private def endpointJointPairing {Ω : Type u} [MeasurableSpace Ω]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (r t : ℝ)
    (hZrt : Measurable (Z r t)) (hr : 0 < r)
    (g : C_c(Plane, ℝ)) (q : Plane × Ω) : ℝ :=
  ∫ y, g y ∂endpointMeasureKernel (Z r t) hZrt r hr q

private theorem measurable_endpointJointPairing {Ω : Type u} [MeasurableSpace Ω]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (r t : ℝ)
    (hZrt : Measurable (Z r t)) (hr : 0 < r) (g : C_c(Plane, ℝ)) :
    Measurable (endpointJointPairing Z r t hZrt hr g) := by
  exact (g.continuous.stronglyMeasurable.integral_kernel
    (κ := endpointMeasureKernel (Z r t) hZrt r hr)).measurable

private theorem endpointJointPairing_eq_ae {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (ϑ : ℝ) (hZ : IsCriticalSHF ϑ P Z) {r t : ℝ} (hr : 0 < r) (hrt : r < t)
    (g : C_c(Plane, ℝ)) (x : Plane) :
    (fun ω => endpointJointPairing Z r t (hZ.1 r t hr.le hrt) hr g (x, ω)) =ᵐ[P]
      fun ω => endpointPairing Z r t x g ω := by
  filter_upwards [hZ.2.1 r t hr.le hrt] with ω hω
  rw [endpointJointPairing, endpointMeasureKernel_apply_of_isLocallyFinite
    (Z r t) (hZ.1 r t hr.le hrt) r hr x ω hω.1,
    endpointPairing_eq_integral_endpointTerminalMeasure Z hr t x g
      g.continuous.stronglyMeasurable ω]

private def modifiedHeatJointPairing {Ω : Type u} [MeasurableSpace Ω]
    (M : Ω → Measure (Plane × Plane)) (δ : ℝ) (g : Plane → ℝ)
    (q : Plane × Ω) : ℝ :=
  ∫ p, heatKernel δ (p.1 - q.1) * g p.2 ∂M q.2

private theorem measurable_modifiedHeatJointPairing {Ω : Type u} [MeasurableSpace Ω]
    (M : Ω → Measure (Plane × Plane)) (hM : Measurable M)
    (hMLF : ∀ ω, IsLocallyFiniteMeasure (M ω)) (δ : ℝ) (g : Plane → ℝ)
    (hg : Continuous g) : Measurable (modifiedHeatJointPairing M δ g) := by
  let κ : Kernel (Plane × Ω) (Plane × Plane) := ⟨fun q => M q.2, hM.comp measurable_snd⟩
  have hκ : IsSFiniteKernel κ := SHF.Tsai.isSFiniteKernel_of_locallyFinite κ
    (fun q => hMLF q.2)
  have hdiff : Measurable (fun q : (Plane × Ω) × (Plane × Plane) => q.2.1 - q.1.1) :=
    (measurable_fst.comp measurable_snd).sub (measurable_fst.comp measurable_fst)
  have hterm : Measurable (fun q : (Plane × Ω) × (Plane × Plane) => g q.2.2) :=
    hg.measurable.comp (measurable_snd.comp measurable_snd)
  have hF : Measurable (fun q : (Plane × Ω) × (Plane × Plane) =>
      heatKernel δ (q.2.1 - q.1.1) * g q.2.2) :=
    ((measurable_heatKernel δ).comp hdiff).mul hterm
  have hInt : StronglyMeasurable (fun q : Plane × Ω =>
      ∫ p, heatKernel δ (p.1 - q.1) * g p.2 ∂M q.2) :=
    @StronglyMeasurable.integral_kernel_prod_right' (Plane × Ω) (Plane × Plane)
      _ _ κ ℝ inferInstance hκ inferInstance _ hF.stronglyMeasurable
  exact hInt.measurable

private def endpointAverage {Ω : Type u} [MeasurableSpace Ω]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (r t : ℝ)
    (hZrt : Measurable (Z r t)) (hr : 0 < r) (ψ : TestFn)
    (g : C_c(Plane, ℝ)) (ω : Ω) : ℝ :=
  ∫ x, ψ x * endpointJointPairing Z r t hZrt hr g (x, ω)

private theorem measurable_endpointAverage {Ω : Type u} [MeasurableSpace Ω]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (r t : ℝ)
    (hZrt : Measurable (Z r t)) (hr : 0 < r) (ψ : TestFn)
    (g : C_c(Plane, ℝ)) : Measurable (endpointAverage Z r t hZrt hr ψ g) := by
  let κ : Kernel Ω Plane := Kernel.const Ω volume
  have hF : Measurable (fun q : Ω × Plane =>
      ψ q.2 * endpointJointPairing Z r t hZrt hr g (q.2, q.1)) := by
    exact (ψ.continuous.measurable.comp measurable_snd).mul
      ((measurable_endpointJointPairing Z r t hZrt hr g).comp
        (measurable_snd.prodMk measurable_fst))
  have hInt := hF.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)
  have hMeas : Measurable (fun ω =>
      ∫ x, ψ x * endpointJointPairing Z r t hZrt hr g (x, ω) ∂volume) := by
    simpa only [κ, Kernel.const_apply] using hInt.measurable
  exact hMeas

private theorem endpointAverage_eq_ae {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (ϑ : ℝ) (hZ : IsCriticalSHF ϑ P Z) {r t : ℝ} (hr : 0 < r) (hrt : r < t)
    (ψ : TestFn) (g : C_c(Plane, ℝ)) :
    endpointAverage Z r t (hZ.1 r t hr.le hrt) hr ψ g =ᵐ[P]
      fun ω => ∫ x, ψ x * endpointPairing Z r t x g ω := by
  filter_upwards [hZ.2.1 r t hr.le hrt] with ω hω
  change (∫ x, ψ x * endpointJointPairing Z r t
      (hZ.1 r t hr.le hrt) hr g (x, ω)) =
    ∫ x, ψ x * endpointPairing Z r t x g ω
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change ψ x * (∫ y, g y ∂endpointMeasureKernel (Z r t)
      (hZ.1 r t hr.le hrt) r hr (x, ω)) =
        ψ x * endpointPairing Z r t x g ω
    rw [endpointMeasureKernel_apply_of_isLocallyFinite (Z r t)
      (hZ.1 r t hr.le hrt) r hr x ω hω.1,
      endpointPairing_eq_integral_endpointTerminalMeasure Z hr t x g
        g.continuous.stronglyMeasurable ω]

private theorem modifiedHeatJointPairing_eq_ae {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (ϑ : ℝ)
    (hZ : IsCriticalSHF ϑ P Z) {r t δ : ℝ} (hr : 0 ≤ r) (hrt : r < t)
    (x : Plane) (g : Plane → ℝ) :
    (fun ω => modifiedHeatJointPairing
      (RandomMeasure.locallyFiniteMeasureModification
        (RandomMeasure.vagueCompactExhaustion (Plane × Plane)) (Z r t)) δ g (x, ω)) =ᵐ[P]
      fun ω => ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂Z r t ω := by
  let E : CompactExhaustion (Plane × Plane) :=
    RandomMeasure.vagueCompactExhaustion (Plane × Plane)
  filter_upwards [hZ.2.1 r t hr hrt] with ω hω
  have hmod := RandomMeasure.locallyFiniteMeasureModification_apply_of_isLocallyFinite
    E (Z r t) ω hω.1
  change (∫ p, heatKernel δ (p.1 - x) * g p.2 ∂
    RandomMeasure.locallyFiniteMeasureModification E (Z r t) ω) = _
  rw [hmod]

private def modifiedHeatMass {Ω : Type u} [MeasurableSpace Ω]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (r t δ : ℝ)
    (q : Plane × Ω) : ℝ :=
  modifiedHeatJointPairing
    (RandomMeasure.locallyFiniteMeasureModification
      (RandomMeasure.vagueCompactExhaustion (Plane × Plane)) (Z r t))
    δ (fun _ => 1) q

private def modifiedEndpointRatio {Ω : Type u} [MeasurableSpace Ω]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (r s t δ : ℝ)
    (q : Plane × Ω) : ℝ :=
  modifiedHeatMass Z r t δ q / modifiedHeatMass Z r s δ q

private theorem measurable_modifiedEndpointRatio {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (ϑ : ℝ)
    (hZ : IsCriticalSHF ϑ P Z) {r s t δ : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hst : s < t) :
    Measurable (modifiedEndpointRatio Z r s t δ) := by
  let E : CompactExhaustion (Plane × Plane) :=
    RandomMeasure.vagueCompactExhaustion (Plane × Plane)
  let Mt := RandomMeasure.locallyFiniteMeasureModification E (Z r t)
  let Ms := RandomMeasure.locallyFiniteMeasureModification E (Z r s)
  have hMt : Measurable Mt :=
    RandomMeasure.measurable_locallyFiniteMeasureModification E (Z r t)
      (hZ.1 r t hr (hrs.trans hst))
  have hMs : Measurable Ms :=
    RandomMeasure.measurable_locallyFiniteMeasureModification E (Z r s) (hZ.1 r s hr hrs)
  have hMtl : ∀ ω, IsLocallyFiniteMeasure (Mt ω) :=
    fun ω => RandomMeasure.locallyFinite_locallyFiniteMeasureModification E (Z r t) ω
  have hMsl : ∀ ω, IsLocallyFiniteMeasure (Ms ω) :=
    fun ω => RandomMeasure.locallyFinite_locallyFiniteMeasureModification E (Z r s) ω
  have hNum := measurable_modifiedHeatJointPairing Mt hMt hMtl δ (fun _ => 1)
    continuous_const
  have hDen := measurable_modifiedHeatJointPairing Ms hMs hMsl δ (fun _ => 1)
    continuous_const
  change Measurable (fun q : Plane × Ω =>
    modifiedHeatJointPairing Mt δ (fun _ => 1) q /
      modifiedHeatJointPairing Ms δ (fun _ => 1) q)
  exact hNum.div hDen

private theorem modifiedEndpointRatio_eq_ae {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (ϑ : ℝ)
    (hZ : IsCriticalSHF ϑ P Z) {r s t δ : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hst : s < t)
    (x : Plane) :
    (fun ω => modifiedEndpointRatio Z r s t δ (x, ω)) =ᵐ[P]
      fun ω => shfPairing Z r t (fun y => heatKernel δ (y - x)) (fun _ => 1) ω /
        shfPairing Z r s (fun y => heatKernel δ (y - x)) (fun _ => 1) ω := by
  have hNum := modifiedHeatJointPairing_eq_ae P Z ϑ hZ hr (hrs.trans hst)
    (δ := δ) x (fun _ => 1)
  have hDen := modifiedHeatJointPairing_eq_ae P Z ϑ hZ hr hrs (δ := δ) x (fun _ => 1)
  filter_upwards [hNum, hDen] with ω hn hd
  change modifiedHeatJointPairing
    (RandomMeasure.locallyFiniteMeasureModification
      (RandomMeasure.vagueCompactExhaustion (Plane × Plane)) (Z r t))
    δ (fun _ => 1) (x, ω) /
    modifiedHeatJointPairing
      (RandomMeasure.locallyFiniteMeasureModification
        (RandomMeasure.vagueCompactExhaustion (Plane × Plane)) (Z r s))
      δ (fun _ => 1) (x, ω) = _
  rw [hn, hd]
  simp [shfPairing]

private def retainedEndpointKernelFunction {Ω : Type u} [MeasurableSpace Ω]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (r s t δ : ℝ)
    (hZrt : Measurable (Z r t)) (hr : 0 < r) (a : ℝ) (g : C_c(Plane, ℝ))
    (q : Plane × Ω) : ℝ :=
  Set.indicator {q | a ≤ modifiedEndpointRatio Z r s t δ q}
    (fun q => endpointJointPairing Z r t hZrt hr g q) q

private theorem measurable_retainedEndpointKernelFunction {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (ϑ : ℝ)
    (hZ : IsCriticalSHF ϑ P Z) {r s t δ : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hst : s < t)
    (hZrt : Measurable (Z r t)) (hpos : 0 < r) (a : ℝ) (g : C_c(Plane, ℝ)) :
    Measurable (retainedEndpointKernelFunction Z r s t δ hZrt hpos a g) := by
  have hRatio := measurable_modifiedEndpointRatio P Z ϑ hZ
    (r := r) (s := s) (t := t) (δ := δ) hr hrs hst
  have hEndpoint := measurable_endpointJointPairing Z r t hZrt hpos g
  have hEvent : MeasurableSet {q : Plane × Ω | a ≤ modifiedEndpointRatio Z r s t δ q} :=
    measurableSet_le measurable_const hRatio
  change Measurable
    ({q : Plane × Ω | a ≤ modifiedEndpointRatio Z r s t δ q}.indicator
      (fun q => endpointJointPairing Z r t hZrt hpos g q))
  exact hEndpoint.indicator hEvent


private def rawEndpointRatioAt {Ω : Type u} [MeasurableSpace Ω]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (r s t δ : ℝ)
    (x : Plane) (ω : Ω) : ℝ :=
  shfPairing Z r t (fun y => heatKernel δ (y - x)) (fun _ => 1) ω /
    shfPairing Z r s (fun y => heatKernel δ (y - x)) (fun _ => 1) ω


private theorem retainedEndpointKernelFunction_eq_ae {Ω : Type u}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (ϑ : ℝ)
    (hZ : IsCriticalSHF ϑ P Z) {r s t δ : ℝ}
    (hr : 0 ≤ r) (hrs : r < s) (hst : s < t) (hpos : 0 < r)
    (x : Plane) (a : ℝ) (g : C_c(Plane, ℝ)) :
    (fun ω => retainedEndpointKernelFunction Z r s t δ
      (hZ.1 r t hr (hrs.trans hst)) hpos a g (x, ω)) =ᵐ[P]
      fun ω => Set.indicator {ω | a ≤ rawEndpointRatioAt Z r s t δ x ω}
        (fun ω => endpointPairing Z r t x g ω) ω := by
  have hRatio := modifiedEndpointRatio_eq_ae P Z ϑ hZ hr hrs hst x (δ := δ)
  have hPair := endpointJointPairing_eq_ae P Z ϑ hZ hpos (hrs.trans hst) g x
  filter_upwards [hRatio, hPair] with ω hRatio hPair
  change (if a ≤ modifiedEndpointRatio Z r s t δ (x, ω) then
      endpointJointPairing Z r t (hZ.1 r t hr (hrs.trans hst)) hpos g (x, ω) else 0) =
    (if a ≤ shfPairing Z r t (fun y => heatKernel δ (y - x)) (fun _ => 1) ω /
        shfPairing Z r s (fun y => heatKernel δ (y - x)) (fun _ => 1) ω then
      endpointPairing Z r t x g ω else 0)
  rw [hRatio, hPair]

private theorem endpointJointPairing_bounds {Ω : Type u} [MeasurableSpace Ω]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (r t : ℝ)
    (hZrt : Measurable (Z r t)) (hr : 0 < r) (g : C_c(Plane, ℝ))
    (hg : ∀ y, 0 ≤ g y ∧ g y ≤ 1) (q : Plane × Ω) :
    0 ≤ endpointJointPairing Z r t hZrt hr g q ∧
      endpointJointPairing Z r t hZrt hr g q ≤ 1 := by
  let ν := endpointMeasureKernel (Z r t) hZrt r hr q
  have hgInt : Integrable (fun y => g y) ν :=
    g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  have hνmass : ν.real Set.univ ≤ 1 := by
    apply ENNReal.toReal_le_of_le_ofReal (by norm_num)
    simpa only [ENNReal.ofReal_one] using
      endpointMeasureKernel_mass_le_one (Z r t) hZrt r hr q
  constructor
  · change 0 ≤ ∫ y, g y ∂ν
    exact integral_nonneg fun y => (hg y).1
  · change (∫ y, g y ∂ν) ≤ 1
    calc
      _ ≤ ∫ _y : Plane, (1 : ℝ) ∂ν :=
        integral_mono hgInt (integrable_const 1) (fun y => (hg y).2)
      _ = ν.real Set.univ := by simp [Measure.real_def]
      _ ≤ 1 := hνmass

private theorem retainedEndpointKernelFunction_bounds {Ω : Type u} [MeasurableSpace Ω]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) {r s t δ : ℝ}
    (hZrt : Measurable (Z r t)) (hr : 0 < r) (a : ℝ) (g : C_c(Plane, ℝ))
    (hg : ∀ y, 0 ≤ g y ∧ g y ≤ 1) (q : Plane × Ω) :
    0 ≤ retainedEndpointKernelFunction Z r s t δ hZrt hr a g q ∧
      retainedEndpointKernelFunction Z r s t δ hZrt hr a g q ≤ 1 := by
  have hX := endpointJointPairing_bounds Z r t hZrt hr g hg q
  by_cases hEvent : a ≤ modifiedEndpointRatio Z r s t δ q
  · simp [retainedEndpointKernelFunction, hEvent, hX]
  · simp [retainedEndpointKernelFunction, hEvent]

private def spatialAverage {Ω : Type u} [MeasurableSpace Ω]
    (ψ : TestFn) (F : Plane × Ω → ℝ) (ω : Ω) : ℝ :=
  ∫ x, ψ x * F (x, ω)


private theorem integrable_spatialAverage {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x)
    (F : Plane × Ω → ℝ) (hF : Measurable F)
    (hFbound : ∀ q, 0 ≤ F q ∧ F q ≤ 1) :
    Integrable (spatialAverage ψ F) P := by
  let J : Plane × Ω → ℝ := fun q => ψ q.1 * F q
  have hJmeas : Measurable J :=
    (ψ.continuous.measurable.comp measurable_fst).mul hF
  have hψInt : Integrable (fun x => ψ x) :=
    ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  have hDom : Integrable (fun q : Plane × Ω => ψ q.1) (volume.prod P) :=
    hψInt.comp_fst P
  have hJbound (q : Plane × Ω) : ‖J q‖ ≤ ψ q.1 := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ q.1)]
    apply mul_le_of_le_one_right (hψ q.1)
    apply abs_le.mpr
    constructor
    · linarith [(hFbound q).1]
    · exact (hFbound q).2
  have hJint : Integrable J (volume.prod P) :=
    hDom.mono' hJmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hJbound)
  change Integrable (fun ω => ∫ x, ψ x * F (x, ω) ∂volume) P
  exact hJint.integral_prod_right

private theorem setIntegral_spatialAverage {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x)
    (F : Plane × Ω → ℝ) (hF : Measurable F)
    (hFbound : ∀ q, 0 ≤ F q ∧ F q ≤ 1) (A : Set Ω) (hA : MeasurableSet A) :
    (∫ ω in A, spatialAverage ψ F ω ∂P) =
      ∫ x, ψ x * (∫ ω in A, F (x, ω) ∂P) := by
  let J : Plane × Ω → ℝ := fun q => ψ q.1 * F q
  have hJmeas : Measurable J :=
    (ψ.continuous.measurable.comp measurable_fst).mul hF
  have hψInt : Integrable (fun x => ψ x) :=
    ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  have hDom : Integrable (fun q : Plane × Ω => ψ q.1) (volume.prod P) :=
    hψInt.comp_fst P
  have hJbound (q : Plane × Ω) : ‖J q‖ ≤ ψ q.1 := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ q.1)]
    apply mul_le_of_le_one_right (hψ q.1)
    apply abs_le.mpr
    constructor
    · linarith [(hFbound q).1]
    · exact (hFbound q).2
  have hJint : Integrable J (volume.prod P) :=
    hDom.mono' hJmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hJbound)
  have hJintA : IntegrableOn J (Set.univ ×ˢ A) (volume.prod P) := hJint.integrableOn
  have hJswapIntA : IntegrableOn (fun q : Ω × Plane => J q.swap)
      (A ×ˢ Set.univ) (P.prod volume) := hJint.swap.integrableOn
  calc
    _ = ∫ ω in A, ∫ x in Set.univ, J (x, ω) ∂volume ∂P := by
      apply setIntegral_congr_ae hA
      exact Eventually.of_forall fun ω hω => by
        simp [spatialAverage, J]
    _ = ∫ q in A ×ˢ Set.univ, J q.swap ∂P.prod volume :=
      (setIntegral_prod (fun q : Ω × Plane => J q.swap) hJswapIntA).symm
    _ = ∫ q in Set.univ ×ˢ A, J q ∂volume.prod P :=
      setIntegral_prod_swap Set.univ A J
    _ = ∫ x in Set.univ, ∫ ω in A, J (x, ω) ∂P ∂volume :=
      setIntegral_prod J hJintA
    _ = ∫ x, ψ x * (∫ ω in A, F (x, ω) ∂P) := by
      rw [setIntegral_univ]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change (∫ ω in A, ψ x * F (x, ω) ∂P) = _
        simpa only [J] using
          (integral_const_mul (μ := P.restrict A) (ψ x) (fun ω => F (x, ω)))

private theorem condExp_spatialRetainedEndpoint_le {Ω : Type u}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (ϑ : ℝ)
    (hZ : IsCriticalSHF ϑ P Z) (hsym : ShfSymmetriesAt ϑ P Z)
    (hdense : DenseSHFAt ϑ P Z) {t r a : ℝ} (ht : 0 < t)
    (hr : 0 < r) (hrt : r < t / 3) (ha : 0 < a)
    (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x) (hψ₁ : ∫ x, ψ x = 1)
    (g : C_c(Plane, ℝ)) (hg : ∀ x, 0 ≤ g x) (hg₁ : ∀ x, g x ≤ 1) :
    P[spatialAverage ψ
      (fun q => retainedEndpointKernelFunction Z r (t / 3) t r
        (hZ.1 r t hr.le (hrt.trans (by linarith [ht]))) hr a g q) |
      MeasurableSpace.comap (Z r (t / 3)) inferInstance ⊔
        MeasurableSpace.comap (Z (2 * t / 3) t) inferInstance] ≤ᵐ[P]
      fun ω => ((2 * Real.pi * (t / 3))⁻¹ / a) *
        shfPairing Z (2 * t / 3) t (fun _ => 1) g ω := by
  let ambient : MeasurableSpace Ω := inferInstance
  let m : MeasurableSpace Ω := MeasurableSpace.comap (Z r (t / 3)) inferInstance ⊔
    MeasurableSpace.comap (Z (2 * t / 3) t) inferInstance
  let : MeasurableSpace Ω := ambient
  have hmambient : m ≤ ambient := by
    dsimp [m]
    refine sup_le ?_ ?_
    · exact (hZ.1 r (t / 3) hr.le hrt).comap_le
    · have hmid : t / 3 < 2 * t / 3 := by linarith
      have hlast : 2 * t / 3 < t := by linarith
      exact (hZ.1 (2 * t / 3) t (by linarith) hlast).comap_le
  have hmid : t / 3 < 2 * t / 3 := by linarith
  have hlast : 2 * t / 3 < t := by linarith
  have hrtT : r < t := hrt.trans hmid |>.trans hlast
  let F : Plane × Ω → ℝ := fun q => retainedEndpointKernelFunction Z r (t / 3) t r
    (hZ.1 r t hr.le hrtT) hr a g q
  have hF : Measurable F := by
    exact measurable_retainedEndpointKernelFunction P Z ϑ hZ
      (r := r) (s := t / 3) (t := t) (δ := r) hr.le hrt (by linarith [ht])
      (hZ.1 r t hr.le hrtT) hr a g
  have hFbounds (q : Plane × Ω) : 0 ≤ F q ∧ F q ≤ 1 := by
    exact retainedEndpointKernelFunction_bounds Z (hZ.1 r t hr.le hrtT) hr a g
      (fun x => ⟨hg x, hg₁ x⟩) q
  have hSInt : Integrable (spatialAverage ψ F) P :=
    integrable_spatialAverage P ψ hψ F hF hFbounds
  let V : Ω → ℝ := shfPairing Z (2 * t / 3) t (fun _ => 1) g
  have hVdata := flat_cc_pairing_integrable_mean ϑ P Z hZ (by positivity) hlast g hg
  have hVInt : Integrable V P := by simpa only [V] using hVdata.2.2.1
  let η : Kernel (Measure (Plane × Plane)) (Plane × Plane) := ⟨id, measurable_id⟩
  have hPairMeas : Measurable (fun μ : Measure (Plane × Plane) => ∫ p, g p.2 ∂μ) :=
    ((g.continuous.measurable.comp measurable_snd).stronglyMeasurable.integral_kernel
      (κ := η)).measurable
  have hZlast : Measurable[m] (Z (2 * t / 3) t) := Measurable.of_comap_le le_sup_right
  have hVm : StronglyMeasurable[m] V := by
    change StronglyMeasurable[m]
      (fun ω => ∫ p, (1 : ℝ) * g p.2 ∂Z (2 * t / 3) t ω)
    simpa only [one_mul, Function.comp_def] using
      (hPairMeas.comp hZlast).stronglyMeasurable
  let c : ℝ := (2 * Real.pi * (t / 3))⁻¹ / a
  let G : Ω → ℝ := fun ω => c * V ω
  have hGInt : Integrable G P := hVInt.const_mul c
  have hGsm : StronglyMeasurable[m] G := hVm.const_mul c
  have hFxInt (x : Plane) : Integrable (fun ω => F (x, ω)) P := by
    have hmeas : Measurable (fun ω => F (x, ω)) :=
      hF.comp (measurable_const.prodMk measurable_id)
    apply (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [(hFbounds (x, ω)).1], (hFbounds (x, ω)).2⟩
  have hFxCond (x : Plane) :
      P[fun ω => F (x, ω) | m] ≤ᵐ[P] G := by
    let W : Ω → ℝ := fun ω => Set.indicator
      {ω | a ≤ rawEndpointRatioAt Z r (t / 3) t r x ω}
      (fun ω => endpointPairing Z r t x g ω) ω
    have hEq := retainedEndpointKernelFunction_eq_ae P Z ϑ hZ
      (r := r) (s := t / 3) (t := t) (δ := r)
      hr.le hrt (by linarith [ht]) hr x a g
    have hFxW : (fun ω => F (x, ω)) =ᵐ[P] W := by
      simpa only [F, W] using hEq
    have hWInt : Integrable W P := (hFxInt x).congr hFxW
    have hScalar := condExp_retained_endpoint_pairing_le_of ϑ P Z hZ hsym hdense
      (r := r) (t := t) (a := a) hr hrt ha x g hg hg₁
    have hCEEq := condExp_congr_ae (m := m) hFxW
    dsimp [W, G, c] at hScalar ⊢
    filter_upwards [hCEEq, hScalar] with ω hCE hBound
    rw [hCE]
    exact hBound
  have hsetPointwise (A : Set Ω) (hA : MeasurableSet[m] A)
      (hAambient : MeasurableSet A) (x : Plane) :
      (∫ ω in A, F (x, ω) ∂P) ≤ ∫ ω in A, G ω ∂P := by
    have hEq := setIntegral_condExp (m := m) hmambient (hFxInt x) hA
    have hRestr : P[fun ω => F (x, ω) | m] ≤ᵐ[P.restrict A] G :=
      (ae_restrict_iff' hAambient).2
        ((hFxCond x).mono fun ω hω _ => hω)
    have hMono := integral_mono_ae integrable_condExp.integrableOn hGInt.integrableOn hRestr
    calc
      _ = ∫ ω in A, P[fun ω => F (x, ω) | m] ω ∂P := hEq.symm
      _ ≤ ∫ ω in A, G ω ∂P := hMono
  have hCEsm : StronglyMeasurable[m] (P[spatialAverage ψ F | m]) :=
    stronglyMeasurable_condExp
  have hCEIntTrim : Integrable (P[spatialAverage ψ F | m]) (P.trim hmambient) :=
    integrable_condExp.trim hmambient hCEsm
  have hGIntTrim : Integrable G (P.trim hmambient) := hGInt.trim hmambient hGsm
  have hTrimBound : P[spatialAverage ψ F | m] ≤ᵐ[P.trim hmambient] G := by
    apply ae_le_of_forall_setIntegral_le hCEIntTrim hGIntTrim
    intro A hA hAfin
    have hAambient : MeasurableSet A := hmambient A hA
    have hFubini := setIntegral_spatialAverage P ψ hψ F hF hFbounds A hAambient
    let H : Plane → ℝ := fun x => ∫ ω in A, F (x, ω) ∂P
    have hHmeas : Measurable H := by
      let κ : Kernel Plane Ω := Kernel.const Plane (P.restrict A)
      have hFsm : StronglyMeasurable F := hF.stronglyMeasurable
      have hInt := hFsm.integral_kernel_prod_right' (κ := κ)
      change Measurable (fun x => ∫ ω, F (x, ω) ∂P.restrict A)
      exact hInt.measurable
    have hψInt : Integrable (fun x => ψ x) :=
      ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
    have hHbounds (x : Plane) : 0 ≤ H x ∧ H x ≤ 1 := by
      have hFxNonneg : 0 ≤ᵐ[P.restrict A] fun ω => F (x, ω) :=
        Filter.Eventually.of_forall fun ω => (hFbounds (x, ω)).1
      have hFxle : (fun ω => F (x, ω)) ≤ᵐ[P.restrict A] fun _ => (1 : ℝ) :=
        Filter.Eventually.of_forall fun ω => (hFbounds (x, ω)).2
      have hFxIntA : Integrable (fun ω => F (x, ω)) (P.restrict A) :=
        (hFxInt x).integrableOn
      constructor
      · exact integral_nonneg_of_ae hFxNonneg
      · have hMono := integral_mono_ae hFxIntA (integrable_const (1 : ℝ)) hFxle
        change (∫ ω, F (x, ω) ∂P.restrict A) ≤ 1
        calc
          _ ≤ ∫ _ω : Ω, (1 : ℝ) ∂P.restrict A := hMono
          _ = (P A).toReal := by
            simp [Measure.real_def]
          _ ≤ 1 := by
            calc
              (P A).toReal ≤ (P Set.univ).toReal :=
                ENNReal.toReal_mono (measure_ne_top P Set.univ)
                  (measure_mono (Set.subset_univ A))
              _ = 1 := by simp
    have hLmeas : Measurable (fun x => ψ x * H x) := ψ.continuous.measurable.mul hHmeas
    have hLint : Integrable (fun x => ψ x * H x) := by
      apply hψInt.mono' hLmeas.aestronglyMeasurable
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ x)]
      exact mul_le_of_le_one_right (hψ x) (abs_le.mpr ⟨by linarith [(hHbounds x).1],
        (hHbounds x).2⟩)
    let d : ℝ := ∫ ω in A, G ω ∂P
    have hRInt : Integrable (fun x => ψ x * d) := hψInt.mul_const d
    have hpoint (x : Plane) : ψ x * H x ≤ ψ x * d :=
      mul_le_mul_of_nonneg_left (hsetPointwise A hA hAambient x) (hψ x)
    have hmono := integral_mono hLint hRInt hpoint
    have hSetBound :
        (∫ ω in A, P[spatialAverage ψ F | m] ω ∂P) ≤ ∫ ω in A, G ω ∂P := by
      calc
        (∫ ω in A, P[spatialAverage ψ F | m] ω ∂P) =
            ∫ ω in A, spatialAverage ψ F ω ∂P :=
          setIntegral_condExp (m := m) hmambient hSInt hA
        _ = ∫ x, ψ x * H x := by
          exact hFubini
        _ ≤ ∫ x, ψ x * d := hmono
        _ = d := by rw [integral_mul_const, hψ₁, one_mul]
        _ = ∫ ω in A, G ω ∂P := rfl
    have hCEtrim :
        (∫ ω in A, P[spatialAverage ψ F | m] ω ∂(P.trim hmambient)) =
          ∫ ω in A, P[spatialAverage ψ F | m] ω ∂P := by
      rw [restrict_trim hmambient P hA]
      exact (integral_trim hmambient hCEsm).symm
    have hGtrim :
        (∫ ω in A, G ω ∂(P.trim hmambient)) = ∫ ω in A, G ω ∂P := by
      rw [restrict_trim hmambient P hA]
      exact (integral_trim hmambient hGsm).symm
    calc
      _ = ∫ ω in A, P[spatialAverage ψ F | m] ω ∂P := hCEtrim
      _ ≤ ∫ ω in A, G ω ∂P := hSetBound
      _ = ∫ ω in A, G ω ∂(P.trim hmambient) := hGtrim.symm
  exact ae_le_of_ae_le_trim (hm := hmambient) hTrimBound

private theorem exists_nonzero_compact_test_bounded_by_one (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x)
    (hψ₁ : ∫ x, ψ x = 1) :
    ∃ φ : C_c(Plane, ℝ), (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
      φ ≠ 0 ∧ IsCompact (tsupport ψ) := by
  obtain ⟨M, hM⟩ := ψ.continuous.bounded_above_of_compact_support ψ.hasCompactSupport
  let C : ℝ := max M 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hψne : testFnToCcc ψ ≠ 0 := by
    intro hzero
    have hzeroFun : (testFnToCcc ψ : Plane → ℝ) = 0 :=
      congrArg (fun f : C_c(Plane, ℝ) => (f : Plane → ℝ)) hzero
    have hzero' : ψ = 0 := by
      ext x
      have hx := congrFun hzeroFun x
      change ψ x = (0 : ℝ) at hx
      exact hx
    rw [hzero'] at hψ₁
    simp at hψ₁
  have hCinv : C⁻¹ ≠ 0 := inv_ne_zero hC.ne'
  have hψM (x : Plane) : ψ x ≤ M := by
    have hm := hM x
    rw [Real.norm_eq_abs, abs_of_nonneg (hψ x)] at hm
    exact hm
  have hval (x : Plane) : ψ x ≤ C := by
    dsimp [C]
    exact (hψM x).trans (le_max_left M 1)
  let φ : C_c(Plane, ℝ) := C⁻¹ • testFnToCcc ψ
  have hφapply (x : Plane) : φ x = C⁻¹ * ψ x := by simp [φ]
  have hbounds : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1 := by
    intro x
    rw [hφapply]
    constructor
    · exact mul_nonneg (inv_nonneg.mpr hC.le) (hψ x)
    · calc
        C⁻¹ * ψ x ≤ C⁻¹ * C := mul_le_mul_of_nonneg_left (hval x) (inv_nonneg.mpr hC.le)
        _ = 1 := inv_mul_cancel₀ hC.ne'
  have hφintegral : ∫ x, φ x = C⁻¹ := by
    calc
      _ = ∫ x, C⁻¹ * ψ x := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hφapply
      _ = C⁻¹ * ∫ x, ψ x := integral_const_mul C⁻¹ (fun x => ψ x)
      _ = C⁻¹ := by rw [hψ₁, mul_one]
  have hne : φ ≠ 0 := by
    intro hz
    have hzint : ∫ x, φ x = 0 := by simp [hz]
    rw [hφintegral] at hzint
    exact hCinv hzint
  exact ⟨φ, hbounds, hne, ψ.hasCompactSupport.isCompact⟩

private theorem spatial_retained_endpoint_mean_lower_of (hVD : Smoothing.PropVDBound)
    (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hHeatStartLogInput : HeatStartLogAt ϑ P Z)
    (hsq : HeatStartSqAt P Z) (hdense : DenseSHFAt ϑ P Z)
    {t : ℝ} (ht : 0 < t) (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x)
    (hψ₁ : ∫ x, ψ x = 1) :
    ∃ φ : C_c(Plane, ℝ), (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧ φ ≠ 0 ∧
      ∃ a c r₀ : ℝ, 0 < a ∧ a < 1 ∧ 0 < c ∧ 0 < r₀ ∧
      ∀ (r : ℝ) (hr : 0 < r) (hrr₀ : r < r₀) (hrt : r < t / 3),
        let F : Plane × Ω → ℝ := fun q => retainedEndpointKernelFunction Z r (t / 3) t r
          (hZ.1 r t hr.le (by linarith [hrt, ht])) hr a φ q
        Integrable (spatialAverage ψ F) P ∧
          c ≤ ∫ ω, spatialAverage ψ F ω ∂P := by
  obtain ⟨φ, hφ, hφne, hK⟩ := exists_nonzero_compact_test_bounded_by_one ψ hψ hψ₁
  obtain ⟨a, c, r₀, ha, ha1, hc, hr₀, hMass⟩ :=
    retained_endpoint_pairing_mean_lower_of hVD ϑ P Z hZ hsym hHeatStartLogInput hsq hdense ht
      (tsupport ψ) hK φ hφ hφne
  refine ⟨φ, hφ, hφne, a, c, r₀, ha, ha1, hc, hr₀, ?_⟩
  intro r hr hrr₀ hrt
  have hrtT : r < t := hrt.trans (by linarith [ht])
  let F : Plane × Ω → ℝ := fun q => retainedEndpointKernelFunction Z r (t / 3) t r
    (hZ.1 r t hr.le hrtT) hr a φ q
  have hF : Measurable F := by
    exact measurable_retainedEndpointKernelFunction P Z ϑ hZ
      (r := r) (s := t / 3) (t := t) (δ := r) hr.le hrt (by linarith [ht])
      (hZ.1 r t hr.le hrtT) hr a φ
  have hFbounds (q : Plane × Ω) : 0 ≤ F q ∧ F q ≤ 1 := by
    exact retainedEndpointKernelFunction_bounds Z (hZ.1 r t hr.le hrtT) hr a φ
      (fun x => ⟨(hφ x).1, (hφ x).2⟩) q
  have hSInt : Integrable (spatialAverage ψ F) P :=
    integrable_spatialAverage P ψ hψ F hF hFbounds
  have hFxInt (x : Plane) : Integrable (fun ω => F (x, ω)) P := by
    have hmeas : Measurable (fun ω => F (x, ω)) :=
      hF.comp (measurable_const.prodMk measurable_id)
    apply (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [(hFbounds (x, ω)).1], (hFbounds (x, ω)).2⟩
  let H : Plane → ℝ := fun x => ∫ ω, F (x, ω) ∂P
  have hHmeas : Measurable H := by
    let κ : Kernel Plane Ω := Kernel.const Plane P
    have hFsm : StronglyMeasurable F := hF.stronglyMeasurable
    have hInt := hFsm.integral_kernel_prod_right' (κ := κ)
    change Measurable (fun x => ∫ ω, F (x, ω) ∂P)
    exact hInt.measurable
  have hψInt : Integrable (fun x => ψ x) :=
    ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  have hHbounds (x : Plane) : 0 ≤ H x ∧ H x ≤ 1 := by
    have hFxNonneg : 0 ≤ᵐ[P] fun ω => F (x, ω) :=
      Filter.Eventually.of_forall fun ω => (hFbounds (x, ω)).1
    have hFxle : (fun ω => F (x, ω)) ≤ᵐ[P] fun _ => (1 : ℝ) :=
      Filter.Eventually.of_forall fun ω => (hFbounds (x, ω)).2
    constructor
    · exact integral_nonneg_of_ae hFxNonneg
    · calc
        H x ≤ ∫ _ω : Ω, (1 : ℝ) ∂P := integral_mono_ae (hFxInt x)
          (integrable_const (1 : ℝ)) hFxle
        _ = 1 := by simp
  have hHInt : Integrable (fun x => ψ x * H x) := by
    have hmeas : Measurable (fun x => ψ x * H x) := ψ.continuous.measurable.mul hHmeas
    apply hψInt.mono' hmeas.aestronglyMeasurable
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ x),
      abs_of_nonneg (hHbounds x).1] using
        (mul_le_of_le_one_right (hψ x) (abs_le.mpr ⟨by linarith [(hHbounds x).1],
          (hHbounds x).2⟩))
  have hψcInt : Integrable (fun x => ψ x * c) := hψInt.mul_const c
  have hψzero (x : Plane) (hx : x ∉ tsupport ψ) : ψ x = 0 := by
    by_contra hxne
    exact hx (subset_tsupport ψ (Function.mem_support.mpr hxne))
  have hpoint (x : Plane) : ψ x * c ≤ ψ x * H x := by
    by_cases hx : x ∈ tsupport ψ
    · have hEq := retainedEndpointKernelFunction_eq_ae P Z ϑ hZ
        (r := r) (s := t / 3) (t := t) (δ := r) hr.le hrt
        (by linarith [ht]) hr x a φ
      let W : Ω → ℝ := fun ω => Set.indicator
        {ω | a ≤ rawEndpointRatioAt Z r (t / 3) t r x ω}
        (fun ω => endpointPairing Z r t x φ ω) ω
      have hFW : (fun ω => F (x, ω)) =ᵐ[P] W := by
        simpa only [F, W] using hEq
      have hWInt : Integrable W P := (hFxInt x).congr hFW
      have hIntEq : (∫ ω, F (x, ω) ∂P) = ∫ ω, W ω ∂P :=
        integral_congr_ae hFW
      have hMassX := hMass r hr hrr₀ x hx
      have hMassW : c ≤ ∫ ω, W ω ∂P := by
        simpa only [W, rawEndpointRatioAt] using hMassX.2
      change ψ x * c ≤ ψ x * (∫ ω, F (x, ω) ∂P)
      rw [hIntEq]
      exact mul_le_mul_of_nonneg_left hMassW (hψ x)
    · rw [hψzero x hx]
      simp
  have hmono := integral_mono hψcInt hHInt hpoint
  have hFubini := setIntegral_spatialAverage P ψ hψ F hF hFbounds
    Set.univ MeasurableSet.univ
  have hFubini' : (∫ ω, spatialAverage ψ F ω ∂P) = ∫ x, ψ x * H x := by
    simpa only [setIntegral_univ] using hFubini
  have hconstant : (∫ x, ψ x * c) = c := by
    rw [integral_mul_const, hψ₁, one_mul]
  refine ⟨hSInt, ?_⟩
  rw [hFubini']
  calc
    c = ∫ x, ψ x * c := hconstant.symm
    _ ≤ ∫ x, ψ x * H x := hmono

private theorem flatPairing_eq_randomPlanarMeasure_of_ae {Ω : Type u}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) {s t : ℝ}
    (ν : Differentiation.RandomPlanarMeasure Ω)
    (hν : ∀ᵐ ω ∂P, ν.measure ω = (Z s t ω).map Prod.snd)
    (g : C_c(Plane, ℝ)) :
    shfPairing Z s t (fun _ => 1) g =ᵐ[P] fun ω => ∫ y, g y ∂ν.measure ω := by
  have hmap (ω : Ω) :
      (∫ y, g y ∂(Z s t ω).map Prod.snd) = shfPairing Z s t (fun _ => 1) g ω := by
    change (∫ y, (g : Plane → ℝ) y ∂Measure.map Prod.snd (Z s t ω)) =
      ∫ p, (fun _ : Plane => (1 : ℝ)) p.1 * g p.2 ∂Z s t ω
    calc
      _ = ∫ p, (g : Plane → ℝ) p.2 ∂Z s t ω :=
        integral_map measurable_snd.aemeasurable
          g.continuous.stronglyMeasurable.aestronglyMeasurable
      _ = _ := by simp
  filter_upwards [hν] with ω hω
  calc
    shfPairing Z s t (fun _ => 1) g ω =
        ∫ y, g y ∂(Z s t ω).map Prod.snd := (hmap ω).symm
    _ = ∫ y, g y ∂ν.measure ω := by rw [← hω]

private theorem measurable_flatPairing {Ω : Type u} [MeasurableSpace Ω]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) {s t : ℝ}
    (hZst : Measurable (Z s t)) (g : C_c(Plane, ℝ)) :
    Measurable (fun ω => shfPairing Z s t (fun _ => 1) g ω) := by
  let η : Kernel (Measure (Plane × Plane)) (Plane × Plane) := ⟨id, measurable_id⟩
  have hPairMeas : Measurable (fun μ : Measure (Plane × Plane) => ∫ p, g p.2 ∂μ) :=
    ((g.continuous.measurable.comp measurable_snd).stronglyMeasurable.integral_kernel
      (κ := η)).measurable
  change Measurable (fun ω => ∫ p, (1 : ℝ) * g p.2 ∂Z s t ω)
  simpa only [one_mul, Function.comp_def] using hPairMeas.comp hZst

private theorem endpointAverage_integrable_bounds {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (ϑ : ℝ)
    (hZ : IsCriticalSHF ϑ P Z) {r t : ℝ} (hr : 0 < r) (hrt : r < t)
    (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x) (hψ₁ : ∫ x, ψ x = 1)
    (g : C_c(Plane, ℝ)) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    Integrable (endpointAverage Z r t (hZ.1 r t hr.le hrt) hr ψ g) P ∧
      ∀ ω, 0 ≤ endpointAverage Z r t (hZ.1 r t hr.le hrt) hr ψ g ω ∧
        endpointAverage Z r t (hZ.1 r t hr.le hrt) hr ψ g ω ≤ 1 := by
  let hZrt := hZ.1 r t hr.le hrt
  have hFmeas : Measurable (endpointJointPairing Z r t hZrt hr g) :=
    measurable_endpointJointPairing Z r t hZrt hr g
  have hFb (q : Plane × Ω) :
      0 ≤ endpointJointPairing Z r t hZrt hr g q ∧
        endpointJointPairing Z r t hZrt hr g q ≤ 1 :=
    endpointJointPairing_bounds Z r t hZrt hr g hg q
  have hψInt : Integrable (fun x => ψ x) :=
    ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  have hIntegrandInt (ω : Ω) :
      Integrable (fun x => ψ x * endpointJointPairing Z r t hZrt hr g (x, ω)) := by
    have hm : Measurable (fun x => endpointJointPairing Z r t hZrt hr g (x, ω)) :=
      hFmeas.comp (measurable_id.prodMk measurable_const)
    apply hψInt.mono' (ψ.continuous.measurable.mul hm).aestronglyMeasurable
    filter_upwards [] with x
    change |ψ x * endpointJointPairing Z r t hZrt hr g (x, ω)| ≤ ψ x
    rw [abs_mul, abs_of_nonneg (hψ x)]
    exact mul_le_of_le_one_right (hψ x)
      (abs_le.mpr ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans (hFb (x, ω)).1,
        (hFb (x, ω)).2⟩)
  have hBound (ω : Ω) :
      0 ≤ endpointAverage Z r t hZrt hr ψ g ω ∧
        endpointAverage Z r t hZrt hr ψ g ω ≤ 1 := by
    constructor
    · exact integral_nonneg fun x => mul_nonneg (hψ x) (hFb (x, ω)).1
    · change (∫ x, ψ x * endpointJointPairing Z r t hZrt hr g (x, ω)) ≤ 1
      calc
        _ ≤ ∫ x, ψ x := integral_mono (hIntegrandInt ω) hψInt fun x =>
          mul_le_of_le_one_right (hψ x) (hFb (x, ω)).2
        _ = 1 := hψ₁
  have hMeas : Measurable (endpointAverage Z r t hZrt hr ψ g) :=
    measurable_endpointAverage Z r t hZrt hr ψ g
  have hInt : Integrable (endpointAverage Z r t hZrt hr ψ g) P := by
    apply (integrable_const (1 : ℝ)).mono' hMeas.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans (hBound ω).1,
      (hBound ω).2⟩
  refine ⟨hInt, ?_⟩
  intro ω
  simpa only [hZrt] using hBound ω

private theorem spatialAverage_mono {Ω : Type u} [MeasurableSpace Ω]
    (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x)
    (F G : Plane × Ω → ℝ) (hF : Measurable F) (hG : Measurable G)
    (hFb : ∀ q, 0 ≤ F q ∧ F q ≤ 1) (hGb : ∀ q, 0 ≤ G q ∧ G q ≤ 1)
    (hFG : ∀ q, F q ≤ G q) :
    ∀ ω, spatialAverage ψ F ω ≤ spatialAverage ψ G ω := by
  have hψInt : Integrable (fun x => ψ x) :=
    ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  have hI (H : Plane × Ω → ℝ) (hH : Measurable H)
      (hHb : ∀ q, 0 ≤ H q ∧ H q ≤ 1) (ω : Ω) :
      Integrable (fun x => ψ x * H (x, ω)) := by
    have hHm : Measurable (fun x => H (x, ω)) :=
      hH.comp (measurable_id.prodMk measurable_const)
    apply hψInt.mono' (ψ.continuous.measurable.mul hHm).aestronglyMeasurable
    filter_upwards [] with x
    change |ψ x * H (x, ω)| ≤ ψ x
    rw [abs_mul, abs_of_nonneg (hψ x)]
    exact mul_le_of_le_one_right (hψ x)
      (abs_le.mpr ⟨by linarith [(hHb (x, ω)).1], (hHb (x, ω)).2⟩)
  intro ω
  unfold spatialAverage
  exact integral_mono (hI F hF hFb ω) (hI G hG hGb ω)
    (fun x => mul_le_mul_of_nonneg_left (hFG (x, ω)) (hψ x))

private theorem endpointJointPairing_add {Ω : Type u} [MeasurableSpace Ω]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (r t : ℝ)
    (hZrt : Measurable (Z r t)) (hr : 0 < r)
    (g₁ g₂ : C_c(Plane, ℝ))
    (hg₁ : ∀ x, 0 ≤ g₁ x ∧ g₁ x ≤ 1)
    (hg₂ : ∀ x, 0 ≤ g₂ x ∧ g₂ x ≤ 1) (q : Plane × Ω) :
    endpointJointPairing Z r t hZrt hr (g₁ + g₂) q =
      endpointJointPairing Z r t hZrt hr g₁ q +
        endpointJointPairing Z r t hZrt hr g₂ q := by
  let κ := endpointMeasureKernel (Z r t) hZrt r hr
  have hMassTop : κ q Set.univ < ∞ :=
    (endpointMeasureKernel_mass_le_one (Z r t) hZrt r hr q).trans_lt ENNReal.one_lt_top
  have hInt (g : C_c(Plane, ℝ)) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
      Integrable (fun x => g x) (κ q) := by
    refine ⟨g.continuous.stronglyMeasurable.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    calc
      (∫⁻ x, ENNReal.ofReal ‖g x‖ ∂κ q) ≤ ∫⁻ _x : Plane, (1 : ℝ≥0∞) ∂κ q := by
        apply lintegral_mono_ae
        filter_upwards [] with x
        rw [Real.norm_eq_abs, abs_of_nonneg (hg x).1]
        exact ENNReal.ofReal_le_one.mpr (hg x).2
      _ = κ q Set.univ := by simp
      _ < ∞ := hMassTop
  unfold endpointJointPairing
  exact integral_add (hInt g₁ hg₁) (hInt g₂ hg₂)

private theorem retainedEndpointKernelFunction_add {Ω : Type u} [MeasurableSpace Ω]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (r s t δ : ℝ)
    (hZrt : Measurable (Z r t)) (hr : 0 < r) (a : ℝ)
    (g₁ g₂ : C_c(Plane, ℝ))
    (hg₁ : ∀ x, 0 ≤ g₁ x ∧ g₁ x ≤ 1)
    (hg₂ : ∀ x, 0 ≤ g₂ x ∧ g₂ x ≤ 1) (q : Plane × Ω) :
    retainedEndpointKernelFunction Z r s t δ hZrt hr a (g₁ + g₂) q =
      retainedEndpointKernelFunction Z r s t δ hZrt hr a g₁ q +
        retainedEndpointKernelFunction Z r s t δ hZrt hr a g₂ q := by
  unfold retainedEndpointKernelFunction
  by_cases h : a ≤ modifiedEndpointRatio Z r s t δ q
  · simp [h, endpointJointPairing_add Z r t hZrt hr g₁ g₂ hg₁ hg₂ q]
  · simp [h]

private theorem spatialAverage_retained_add {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (ϑ : ℝ)
    (hZ : IsCriticalSHF ϑ P Z) {r t a : ℝ} (hr : 0 < r) (ht : 0 < t)
    (hrt : r < t / 3)
    (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x)
    (g₁ g₂ : C_c(Plane, ℝ))
    (hg₁ : ∀ x, 0 ≤ g₁ x ∧ g₁ x ≤ 1)
    (hg₂ : ∀ x, 0 ≤ g₂ x ∧ g₂ x ≤ 1) :
    let F₁ : Plane × Ω → ℝ := fun q => retainedEndpointKernelFunction Z r (t / 3) t r
      (hZ.1 r t hr.le (hrt.trans (by linarith [ht]))) hr a g₁ q
    let F₂ : Plane × Ω → ℝ := fun q => retainedEndpointKernelFunction Z r (t / 3) t r
      (hZ.1 r t hr.le (hrt.trans (by linarith [ht]))) hr a g₂ q
    let F : Plane × Ω → ℝ := fun q => retainedEndpointKernelFunction Z r (t / 3) t r
      (hZ.1 r t hr.le (hrt.trans (by linarith [ht]))) hr a (g₁ + g₂) q
    ∀ ω, spatialAverage ψ F ω = spatialAverage ψ F₁ ω + spatialAverage ψ F₂ ω := by
  dsimp only
  intro ω
  have hrtT : r < t := hrt.trans (by linarith [ht])
  have hZrt := hZ.1 r t hr.le hrtT
  let F₁ : Plane × Ω → ℝ := fun q => retainedEndpointKernelFunction Z r (t / 3) t r hZrt hr a g₁ q
  let F₂ : Plane × Ω → ℝ := fun q => retainedEndpointKernelFunction Z r (t / 3) t r hZrt hr a g₂ q
  let F : Plane × Ω → ℝ := fun q => retainedEndpointKernelFunction Z r (t / 3) t r hZrt hr a (g₁ + g₂) q
  have hF₁ : Measurable F₁ := measurable_retainedEndpointKernelFunction P Z ϑ hZ
    (r := r) (s := t / 3) (t := t) (δ := r) hr.le hrt (by linarith [ht]) hZrt hr a g₁
  have hF₂ : Measurable F₂ := measurable_retainedEndpointKernelFunction P Z ϑ hZ
    (r := r) (s := t / 3) (t := t) (δ := r) hr.le hrt (by linarith [ht]) hZrt hr a g₂
  have hF₁b (q : Plane × Ω) : 0 ≤ F₁ q ∧ F₁ q ≤ 1 :=
    retainedEndpointKernelFunction_bounds Z hZrt hr a g₁ hg₁ q
  have hF₂b (q : Plane × Ω) : 0 ≤ F₂ q ∧ F₂ q ≤ 1 :=
    retainedEndpointKernelFunction_bounds Z hZrt hr a g₂ hg₂ q
  have hψInt : Integrable (fun x => ψ x) :=
    ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  have hIx (G : Plane × Ω → ℝ) (hG : Measurable G)
      (hGb : ∀ q, 0 ≤ G q ∧ G q ≤ 1) :
      ∀ ω, Integrable (fun x => ψ x * G (x, ω)) := by
    intro ω
    have hm : Measurable (fun x => G (x, ω)) := hG.comp (measurable_id.prodMk measurable_const)
    apply hψInt.mono' (ψ.continuous.measurable.mul hm).aestronglyMeasurable
    filter_upwards [] with x
    change |ψ x * G (x, ω)| ≤ ψ x
    rw [abs_mul, abs_of_nonneg (hψ x)]
    exact mul_le_of_le_one_right (hψ x)
      (abs_le.mpr ⟨by linarith [(hGb (x, ω)).1], (hGb (x, ω)).2⟩)
  have hI₁ := hIx F₁ hF₁ hF₁b ω
  have hI₂ := hIx F₂ hF₂ hF₂b ω
  unfold spatialAverage
  change (∫ x, ψ x * retainedEndpointKernelFunction Z r (t / 3) t r
      hZrt hr a (g₁ + g₂) (x, ω)) =
    (∫ x, ψ x * retainedEndpointKernelFunction Z r (t / 3) t r hZrt hr a g₁ (x, ω)) +
      ∫ x, ψ x * retainedEndpointKernelFunction Z r (t / 3) t r hZrt hr a g₂ (x, ω)
  rw [← integral_add hI₁ hI₂]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change ψ x * retainedEndpointKernelFunction Z r (t / 3) t r hZrt hr a
        (g₁ + g₂) (x, ω) =
      ψ x * retainedEndpointKernelFunction Z r (t / 3) t r hZrt hr a g₁ (x, ω) +
        ψ x * retainedEndpointKernelFunction Z r (t / 3) t r hZrt hr a g₂ (x, ω)
    rw [retainedEndpointKernelFunction_add Z r (t / 3) t r hZrt hr a
      g₁ g₂ hg₁ hg₂ (x, ω)]
    ring

private def runningMinimum {Ω : Type u} (q : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0, ω => q 0 ω
  | n + 1, ω => min (runningMinimum q n ω) (q (n + 1) ω)

private theorem runningMinimum_nonneg {Ω : Type u} (q : ℕ → Ω → ℝ)
    (hq : ∀ j ω, 0 ≤ q j ω) (n : ℕ) (ω : Ω) :
    0 ≤ runningMinimum q n ω := by
  induction n with
  | zero => exact hq 0 ω
  | succ n ih => exact (le_min ih (hq (n + 1) ω))

private theorem runningMinimum_le {Ω : Type u} (q : ℕ → Ω → ℝ)
    (n j : ℕ) (ω : Ω) (hjn : j ≤ n) :
    runningMinimum q n ω ≤ q j ω := by
  induction n with
  | zero =>
      have : j = 0 := Nat.eq_zero_of_le_zero hjn
      subst j
      rfl
  | succ n ih =>
      by_cases h : j = n + 1
      · subst j
        exact min_le_right _ _
      · have hjn' : j ≤ n := by omega
        exact (min_le_left _ _).trans (ih hjn')

private theorem runningMinimum_mem {Ω : Type u} (q : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) :
    ∃ j, j ≤ n ∧ runningMinimum q n ω = q j ω := by
  induction n with
  | zero => exact ⟨0, Nat.le_refl _, rfl⟩
  | succ n ih =>
      by_cases h : runningMinimum q n ω ≤ q (n + 1) ω
      · obtain ⟨j, hj, hq⟩ := ih
        refine ⟨j, by omega, ?_⟩
        have hh : q j ω ≤ q (n + 1) ω := by simpa only [← hq] using h
        simp [runningMinimum, min_eq_left hh, hq]
      · refine ⟨n + 1, Nat.le_refl _, ?_⟩
        simp [runningMinimum, min_eq_right (le_of_not_ge h)]

private theorem runningMinimum_measurable {Ω : Type u} [MeasurableSpace Ω]
    (q : ℕ → Ω → ℝ) (hq : ∀ j, Measurable (q j)) :
    ∀ n, Measurable (runningMinimum q n) := by
  intro n
  induction n with
  | zero => simpa [runningMinimum] using hq 0
  | succ n ih => simpa [runningMinimum] using ih.min (hq (n + 1))

private theorem runningMinimum_tendsto_zero_of_arbitrarily_small_values {Ω : Type u}
    (q : ℕ → Ω → ℝ) (hq : ∀ j ω, 0 ≤ q j ω)
    (ω : Ω) (hsep : ∀ ε, 0 < ε → ∃ j, q j ω < ε) :
    Tendsto (fun n => runningMinimum q n ω) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := hsep ε hε
  filter_upwards [eventually_ge_atTop j] with n hn
  have hmin := runningMinimum_le q n j ω hn
  simpa [Real.dist_eq, abs_of_nonneg (runningMinimum_nonneg q hq n ω)] using hmin.trans_lt hj

private theorem conditional_endpoint_pairing_error_tendsto_zero {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (ϑ : ℝ)
    (hZ : IsCriticalSHF ϑ P Z) {t : ℝ} (ht : 0 < t)
    (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x) (hψ₁ : ∫ x, ψ x = 1)
    (μ : Measure Plane) [IsFiniteMeasure μ] (r : ℕ → ℝ)
    (hr : ∀ n, 0 < r n) (hrt : ∀ n, r n < t / 3)
    (hμ : ∀ g : C_c(Plane, ℝ),
      Tendsto (fun n => ∫ ω,
        |(∫ x, ψ x * endpointPairing Z (r n) t x g ω) - ∫ y, g y ∂μ| ∂P)
        atTop (𝓝 0))
    (g : C_c(Plane, ℝ)) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    Tendsto (fun n => ∫ ω,
      |P[endpointAverage Z (r n) t (hZ.1 (r n) t (hr n).le
        ((hrt n).trans (by linarith [ht]))) (hr n) ψ g | MeasurableSpace.comap
          (Z (r n) (t / 3)) inferInstance ⊔
          MeasurableSpace.comap (Z (2 * t / 3) t) inferInstance] ω -
        ∫ y, g y ∂μ| ∂P) atTop (𝓝 0) := by
  let m : ℕ → MeasurableSpace Ω := fun n =>
    MeasurableSpace.comap (Z (r n) (t / 3)) inferInstance ⊔
      MeasurableSpace.comap (Z (2 * t / 3) t) inferInstance
  let U : ℕ → Ω → ℝ := fun n => endpointAverage Z (r n) t
    (hZ.1 (r n) t (hr n).le ((hrt n).trans (by linarith [ht]))) (hr n) ψ g
  let D : ℕ → Ω → ℝ := fun n => P[U n | m n]
  let M : ℝ := ∫ y, g y ∂μ
  have hm (n : ℕ) : m n ≤ (inferInstance : MeasurableSpace Ω) := by
    dsimp [m]
    refine sup_le ?_ ?_
    · exact (hZ.1 (r n) (t / 3) (hr n).le (hrt n)).comap_le
    · have hmid : t / 3 < 2 * t / 3 := by linarith
      have hlast : 2 * t / 3 < t := by linarith
      exact (hZ.1 (2 * t / 3) t (by linarith [ht]) hlast).comap_le
  have hUint (n : ℕ) : Integrable (U n) P := by
    exact (endpointAverage_integrable_bounds P Z ϑ hZ
      (r := r n) (t := t) (hr n) ((hrt n).trans (by linarith [ht]))
      ψ hψ hψ₁ g hg).1
  have hUae (n : ℕ) : U n =ᵐ[P]
      fun ω => ∫ x, ψ x * endpointPairing Z (r n) t x g ω := by
    exact endpointAverage_eq_ae P Z ϑ hZ (hr n) ((hrt n).trans (by linarith [ht])) ψ g
  have hrawLimit : Tendsto (fun n => ∫ ω,
      |(∫ x, ψ x * endpointPairing Z (r n) t x g ω) - M| ∂P) atTop (𝓝 0) := by
    simpa only [M] using hμ g
  have hbound (n : ℕ) : ∫ ω, |D n ω - M| ∂P ≤
      ∫ ω, |(∫ x, ψ x * endpointPairing Z (r n) t x g ω) - M| ∂P := by
    have hsub := condExp_sub (hUint n) (integrable_const M) (m n)
    have hconst := condExp_const (μ := P) (hm n) M
    have hCE : (fun ω => D n ω - M) =ᵐ[P] P[fun ω => U n ω - M | m n] := by
      filter_upwards [hsub] with ω hsubω
      calc
        D n ω - M = P[U n | m n] ω - P[fun _ => M | m n] ω := by
          simp [D, hconst]
        _ = P[fun ω => U n ω - M | m n] ω := hsubω.symm
    have hCEabs : (fun ω => |D n ω - M|) =ᵐ[P]
        fun ω => |P[fun ω => U n ω - M | m n] ω| := by
      filter_upwards [hCE] with ω hω
      rw [hω]
    have hRawAbs : (fun ω => |U n ω - M|) =ᵐ[P]
        fun ω => |(∫ x, ψ x * endpointPairing Z (r n) t x g ω) - M| := by
      filter_upwards [hUae n] with ω hω
      rw [hω]
    have hcontract := integral_abs_condExp_le (μ := P) (m := m n)
      (fun ω => U n ω - M)
    calc
      _ = ∫ ω, |P[fun ω => U n ω - M | m n] ω| ∂P :=
        integral_congr_ae hCEabs
      _ ≤ ∫ ω, |U n ω - M| ∂P := hcontract
      _ = ∫ ω, |(∫ x, ψ x * endpointPairing Z (r n) t x g ω) - M| ∂P :=
        integral_congr_ae hRawAbs
  have hnonneg (n : ℕ) : 0 ≤ ∫ ω, |D n ω - M| ∂P :=
    integral_nonneg fun ω => abs_nonneg _
  simpa only [D, U, m, M] using
    squeeze_zero' (Filter.Eventually.of_forall hnonneg)
      (Filter.Eventually.of_forall hbound) hrawLimit

/-- A deterministic finite endpoint limit of the averaged pairings is not mutually singular
with the later flat endpoint measure with positive probability; see KPZ Lemma 9.6. -/
theorem endpoint_limit_not_singular_of (hVD : Smoothing.PropVDBound) (ϑ : ℝ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hHeatStartLogInput : HeatStartLogAt ϑ P Z)
    (hsq : HeatStartSqAt P Z) (hdense : DenseSHFAt ϑ P Z)
    {t : ℝ} (ht : 0 < t) (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x)
    (hψ₁ : ∫ x, ψ x = 1) (μ : Measure Plane) [IsFiniteMeasure μ]
    (r : ℕ → ℝ) (hr : Tendsto r atTop (nhdsWithin 0 (Set.Ioi 0)))
    (hμ : ∀ φ : C_c(Plane, ℝ),
      Tendsto (fun n => ∫ ω,
        |(∫ x, ψ x * endpointPairing Z (r n) t x φ ω) - ∫ y, φ y ∂μ| ∂P)
        atTop (𝓝 0)) :
    0 < P {ω | ¬ μ ⟂ₘ (Z (2 * t / 3) t ω).map Prod.snd} := by
  obtain ⟨φ, hφ, hφne, a, c, r₀, ha, ha1, hc, hr₀, hretained⟩ :=
    spatial_retained_endpoint_mean_lower_of hVD ϑ P Z hZ hsym hHeatStartLogInput hsq hdense ht ψ hψ hψ₁
  have hflatStart : 0 ≤ 2 * t / 3 := by positivity
  have hflatEnd : 2 * t / 3 < t := by linarith
  obtain ⟨ν, hν, _hmean⟩ := exists_flatEndpoint_randomPlanarMeasure_of ϑ P Z hZ hdense
    (s := 2 * t / 3) (t := t) hflatStart hflatEnd
  have hrzero : Tendsto r atTop (𝓝 0) := hr.mono_right nhdsWithin_le_nhds
  have hrpos : ∀ᶠ n in atTop, 0 < r n := hr.eventually eventually_mem_nhdsWithin
  have hrsmall : ∀ᶠ n in atTop, r n < min r₀ (t / 3) :=
    hrzero.eventually_lt_const (lt_min hr₀ (by positivity))
  have hgood : ∀ᶠ n in atTop, 0 < r n ∧ r n < r₀ ∧ r n < t / 3 := by
    filter_upwards [hrpos, hrsmall] with n hpos hsmall
    exact ⟨hpos, lt_of_lt_of_le hsmall (min_le_left _ _),
      lt_of_lt_of_le hsmall (min_le_right _ _)⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hgood
  let ρ : ℕ → ℝ := fun n => r (n + N)
  have hρgood (n : ℕ) : 0 < ρ n ∧ ρ n < r₀ ∧ ρ n < t / 3 := by
    exact hN (n + N) (by omega)
  have hμρ (g : C_c(Plane, ℝ)) :
      Tendsto (fun n => ∫ ω,
        |(∫ x, ψ x * endpointPairing Z (ρ n) t x g ω) - ∫ y, g y ∂μ| ∂P)
        atTop (𝓝 0) := by
    simpa [ρ, Function.comp_def] using (hμ g).comp (tendsto_add_atTop_nat N)
  by_contra hnot
  have hbad0 : P {ω | ¬ μ ⟂ₘ (Z (2 * t / 3) t ω).map Prod.snd} = 0 :=
    le_antisymm (not_lt.mp hnot) bot_le
  have hsing : ∀ᵐ ω ∂P, μ ⟂ₘ (Z (2 * t / 3) t ω).map Prod.snd :=
    ae_iff.mpr hbad0
  have hνsing : ∀ᵐ ω ∂P, μ ⟂ₘ ν.measure ω := by
    filter_upwards [hsing, hν] with ω hω hω'
    rw [hω']
    exact hω
  let B : ℝ := (2 * Real.pi * (t / 3))⁻¹ / a
  have hB : 0 < B := by dsimp [B]; positivity
  let χ : ℕ → C_c(Plane, ℝ) := countableBoundedVagueTest
  let G : ℕ → C_c(Plane, ℝ) := fun j => φ * χ j
  let F : ℕ → C_c(Plane, ℝ) := fun j => φ - G j
  let V : ℕ → Ω → ℝ := fun j ω =>
    shfPairing Z (2 * t / 3) t (fun _ => 1) (G j) ω
  let M : ℕ → ℝ := fun j => ∫ y, F j y ∂μ
  let Q : ℕ → Ω → ℝ := fun j ω => B * V j ω + M j
  have hχbounds (j : ℕ) (x : Plane) : 0 ≤ χ j x ∧ χ j x ≤ 1 := by
    dsimp [χ, countableBoundedVagueTest]
    exact boundedDenseVagueTest_bounds (RandomMeasure.vagueCompactExhaustion Plane)
      (Nat.unpair j).1 (Nat.unpair j).2 x
  have hGapply (j : ℕ) (x : Plane) : G j x = φ x * χ j x := by simp [G]
  have hFapply (j : ℕ) (x : Plane) : F j x = φ x * (1 - χ j x) := by
    change φ x - φ x * χ j x = φ x * (1 - χ j x)
    ring
  have hGbounds (j : ℕ) (x : Plane) : 0 ≤ G j x ∧ G j x ≤ 1 := by
    rw [hGapply]
    constructor
    · exact mul_nonneg (hφ x).1 (hχbounds j x).1
    · calc
        φ x * χ j x ≤ 1 * χ j x :=
          mul_le_mul_of_nonneg_right (hφ x).2 (hχbounds j x).1
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left (hχbounds j x).2 (by norm_num)
        _ = 1 := by ring
  have hFbounds (j : ℕ) (x : Plane) : 0 ≤ F j x ∧ F j x ≤ 1 := by
    rw [hFapply]
    have hχ' : 0 ≤ 1 - χ j x := by linarith [(hχbounds j x).2]
    constructor
    · exact mul_nonneg (hφ x).1 hχ'
    · calc
        φ x * (1 - χ j x) ≤ 1 * (1 - χ j x) :=
          mul_le_mul_of_nonneg_right (hφ x).2 hχ'
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left (by linarith [(hχbounds j x).1]) (by norm_num)
        _ = 1 := by ring
  have hsum (j : ℕ) : G j + F j = φ := by
    ext x
    change G j x + F j x = φ x
    rw [hGapply, hFapply]
    ring
  have hVmeas (j : ℕ) : Measurable (V j) := by
    dsimp [V]
    exact measurable_flatPairing Z (hZ.1 (2 * t / 3) t hflatStart hflatEnd) (G j)
  have hVint (j : ℕ) : Integrable (V j) P := by
    dsimp [V]
    exact (flat_cc_pairing_integrable_mean ϑ P Z hZ hflatStart hflatEnd (G j)
      (fun x => (hGbounds j x).1)).2.2.1
  have hVnonneg (j : ℕ) (ω : Ω) : 0 ≤ V j ω := by
    dsimp [V, shfPairing]
    simpa only [one_mul] using
      (integral_nonneg fun p => (hGbounds j p.2).1 :
        0 ≤ ∫ p : Plane × Plane, (G j) p.2 ∂Z (2 * t / 3) t ω)
  have hMnonneg (j : ℕ) : 0 ≤ M j := by
    dsimp [M]
    exact integral_nonneg fun x => (hFbounds j x).1
  have hQmeas (j : ℕ) : Measurable (Q j) := by
    dsimp [Q]
    exact measurable_const.mul (hVmeas j) |>.add measurable_const
  have hQnonneg (j : ℕ) (ω : Ω) : 0 ≤ Q j ω := by
    dsimp [Q]
    exact add_nonneg (mul_nonneg hB.le (hVnonneg j ω)) (hMnonneg j)
  have hQzeroInt : Integrable (Q 0) P := by
    dsimp [Q]
    exact ((hVint 0).const_mul B).add (integrable_const (M 0))
  have hVpair (j : ℕ) : V j =ᵐ[P] fun ω => ∫ y, G j y ∂ν.measure ω := by
    dsimp [V]
    exact flatPairing_eq_randomPlanarMeasure_of_ae P Z ν hν (G j)
  have hpairAll : ∀ᵐ ω ∂P, ∀ j : ℕ, V j ω = ∫ y, G j y ∂ν.measure ω :=
    ae_all_iff.mpr hVpair
  have hQseparates (ω : Ω) (hω : μ ⟂ₘ ν.measure ω)
      (hpair : ∀ j : ℕ, V j ω = ∫ y, G j y ∂ν.measure ω)
      (ε : ℝ) (hε : 0 < ε) : ∃ j, Q j ω < ε := by
    let ε₀ : ℝ := ε / (2 * (B + 1))
    have hε₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
    obtain ⟨j, hνsmall, hμsmall⟩ :=
      @exists_countableBoundedVagueTest_singular_separation μ (ν.measure ω)
        inferInstance (ν.value ω).2 hω φ hφ ε₀ hε₀
    have hVsmall : V j ω < ε₀ := by
      rw [hpair j]
      simpa [G, χ, countableBoundedVagueTest] using hνsmall
    have hMsmall : M j < ε₀ := by
      have hEq : M j = ∫ y, φ y * (1 - χ j y) ∂μ := by
        dsimp [M]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (hFapply j)
      rw [hEq]
      simpa [χ, countableBoundedVagueTest] using hμsmall
    refine ⟨j, ?_⟩
    calc
      Q j ω = B * V j ω + M j := rfl
      _ < B * ε₀ + ε₀ := add_lt_add (mul_lt_mul_of_pos_left hVsmall hB) hMsmall
      _ = ε / 2 := by dsimp [ε₀]; field_simp
      _ < ε := by linarith
  have hQprefixMeas (J : ℕ) : Measurable (runningMinimum Q J) :=
    runningMinimum_measurable Q hQmeas J
  have hQprefixInt (J : ℕ) : Integrable (runningMinimum Q J) P := by
    apply hQzeroInt.mono' (hQprefixMeas J).aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (runningMinimum_nonneg Q hQnonneg J ω)]
    exact runningMinimum_le Q J 0 ω (Nat.zero_le _)
  have hQprefixLimit : ∀ᵐ ω ∂P,
      Tendsto (fun J => runningMinimum Q J ω) atTop (𝓝 0) := by
    filter_upwards [hνsing, hpairAll] with ω hω hpair
    exact runningMinimum_tendsto_zero_of_arbitrarily_small_values Q hQnonneg ω
      (fun ε hε => hQseparates ω hω hpair ε hε)
  have hprefixIntegralLimit :
      Tendsto (fun J => ∫ ω, runningMinimum Q J ω ∂P) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (Q 0)
      (fun J => (hQprefixMeas J).aestronglyMeasurable) hQzeroInt
      (fun J => Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (runningMinimum_nonneg Q hQnonneg J ω)]
        exact runningMinimum_le Q J 0 ω (Nat.zero_le _))
      hQprefixLimit
    simpa using h
  let m : ℕ → MeasurableSpace Ω := fun n =>
    MeasurableSpace.comap (Z (ρ n) (t / 3)) inferInstance ⊔
      MeasurableSpace.comap (Z (2 * t / 3) t) inferInstance
  have hρt (n : ℕ) : ρ n < t := by
    exact (hρgood n).2.2.trans (by linarith [ht])
  have hZrt (n : ℕ) : Measurable (Z (ρ n) t) :=
    hZ.1 (ρ n) t (hρgood n).1.le (hρt n)
  let U : ℕ → ℕ → Ω → ℝ := fun j n => endpointAverage Z (ρ n) t (hZrt n)
    (hρgood n).1 ψ (F j)
  let D : ℕ → ℕ → Ω → ℝ := fun j n => P[U j n | m n]
  let Ret : ℕ → C_c(Plane, ℝ) → Ω → ℝ := fun n g =>
    spatialAverage ψ (fun q => retainedEndpointKernelFunction Z (ρ n) (t / 3) t (ρ n)
      (hZrt n) (hρgood n).1 a g q)
  let Eta : ℕ → Ω → ℝ := fun n => P[Ret n φ | m n]
  have hm (n : ℕ) : m n ≤ (inferInstance : MeasurableSpace Ω) := by
    dsimp [m]
    refine sup_le ?_ ?_
    · exact (hZ.1 (ρ n) (t / 3) (hρgood n).1.le (hρgood n).2.2).comap_le
    · exact (hZ.1 (2 * t / 3) t hflatStart hflatEnd).comap_le
  have hRetMeas (n : ℕ) (g : C_c(Plane, ℝ)) :
      Measurable (fun q => retainedEndpointKernelFunction Z (ρ n) (t / 3) t (ρ n)
        (hZrt n) (hρgood n).1 a g q) := by
    exact measurable_retainedEndpointKernelFunction P Z ϑ hZ
      (r := ρ n) (s := t / 3) (t := t) (δ := ρ n)
      (hρgood n).1.le (hρgood n).2.2 (by linarith [ht]) (hZrt n)
      (hρgood n).1 a g
  have hRetBounds (n : ℕ) (g : C_c(Plane, ℝ))
      (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (q : Plane × Ω) :
      0 ≤ retainedEndpointKernelFunction Z (ρ n) (t / 3) t (ρ n)
        (hZrt n) (hρgood n).1 a g q ∧
      retainedEndpointKernelFunction Z (ρ n) (t / 3) t (ρ n)
        (hZrt n) (hρgood n).1 a g q ≤ 1 :=
    retainedEndpointKernelFunction_bounds Z (hZrt n) (hρgood n).1 a g hg q
  have hRetInt (n : ℕ) (g : C_c(Plane, ℝ))
      (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) : Integrable (Ret n g) P := by
    exact integrable_spatialAverage P ψ hψ
      (fun q => retainedEndpointKernelFunction Z (ρ n) (t / 3) t (ρ n)
        (hZrt n) (hρgood n).1 a g q)
      (hRetMeas n g) (hRetBounds n g hg)
  have hRetSplit (n j : ℕ) :
      Ret n φ =ᵐ[P] fun ω => Ret n (G j) ω + Ret n (F j) ω := by
    filter_upwards [] with ω
    have h := spatialAverage_retained_add P Z ϑ hZ
      (r := ρ n) (t := t) (a := a) (hρgood n).1 ht (hρgood n).2.2
      ψ hψ (G j) (F j) (hGbounds j) (hFbounds j) ω
    simpa only [Ret, hsum j] using h
  have hUintegrable (j n : ℕ) : Integrable (U j n) P := by
    exact (endpointAverage_integrable_bounds P Z ϑ hZ
      (r := ρ n) (t := t) (hρgood n).1 ((hρgood n).2.2.trans (by linarith [ht]))
      ψ hψ hψ₁ (F j) (hFbounds j)).1
  have hRetF_le_U (n j : ℕ) : ∀ ω, Ret n (F j) ω ≤ U j n ω := by
    let RF : Plane × Ω → ℝ := fun q => retainedEndpointKernelFunction Z (ρ n)
      (t / 3) t (ρ n) (hZrt n) (hρgood n).1 a (F j) q
    let EF : Plane × Ω → ℝ := fun q => endpointJointPairing Z (ρ n) t
      (hZrt n) (hρgood n).1 (F j) q
    have hEFmeas : Measurable EF := measurable_endpointJointPairing
      Z (ρ n) t (hZrt n) (hρgood n).1 (F j)
    have hEFbounds (q : Plane × Ω) : 0 ≤ EF q ∧ EF q ≤ 1 :=
      endpointJointPairing_bounds Z (ρ n) t (hZrt n) (hρgood n).1 (F j)
        (hFbounds j) q
    have hRFleEF (q : Plane × Ω) : RF q ≤ EF q := by
      by_cases hEvent : a ≤ modifiedEndpointRatio Z (ρ n) (t / 3) t (ρ n) q
      · simp [RF, EF, retainedEndpointKernelFunction, hEvent]
      · simp [RF, EF, retainedEndpointKernelFunction, hEvent, (hEFbounds q).1]
    have hmono := spatialAverage_mono ψ hψ RF EF (hRetMeas n (F j)) hEFmeas
      (fun q => hRetBounds n (F j) (hFbounds j) q) hEFbounds hRFleEF
    simpa only [Ret, U, RF, EF, spatialAverage, endpointAverage] using hmono
  have hEtaBound (n j : ℕ) :
      Eta n ≤ᵐ[P] fun ω => Q j ω + |D j n ω - M j| := by
    have hRetGint := hRetInt n (G j) (hGbounds j)
    have hRetFint := hRetInt n (F j) (hFbounds j)
    have hCEsplit : P[Ret n φ | m n] =ᵐ[P]
        P[Ret n (G j) | m n] + P[Ret n (F j) | m n] := by
      exact (condExp_congr_ae (m := m n) (hRetSplit n j)).trans
        (condExp_add hRetGint hRetFint (m n))
    have hCEg := condExp_spatialRetainedEndpoint_le P Z ϑ hZ hsym hdense
      ht (hρgood n).1 (hρgood n).2.2 ha ψ hψ hψ₁ (G j)
      (fun x => (hGbounds j x).1) (fun x => (hGbounds j x).2)
    have hCEg' : P[Ret n (G j) | m n] ≤ᵐ[P] fun ω => B * V j ω := by
      simpa only [Ret, m, B, V] using hCEg
    have hCEf := condExp_mono (m := m n) hRetFint (hUintegrable j n)
      (Filter.Eventually.of_forall (hRetF_le_U n j))
    have hCEf' : P[Ret n (F j) | m n] ≤ᵐ[P] D j n := by
      simpa only [D, U, m] using hCEf
    filter_upwards [hCEsplit, hCEg', hCEf'] with ω hsplit hg hf
    have hDle : D j n ω ≤ M j + |D j n ω - M j| := by
      linarith [le_abs_self (D j n ω - M j)]
    change P[Ret n φ | m n] ω ≤ Q j ω + |D j n ω - M j|
    rw [hsplit]
    calc
      P[Ret n (G j) | m n] ω + P[Ret n (F j) | m n] ω ≤
          B * V j ω + D j n ω := add_le_add hg hf
      _ ≤ B * V j ω + (M j + |D j n ω - M j|) := add_le_add le_rfl hDle
      _ = Q j ω + |D j n ω - M j| := by dsimp [Q]; ring
  have hErrLimit (j : ℕ) : Tendsto
      (fun n => ∫ ω, |D j n ω - M j| ∂P) atTop (𝓝 0) := by
    simpa only [D, U, m, M] using conditional_endpoint_pairing_error_tendsto_zero P Z ϑ hZ ht ψ hψ hψ₁
      μ ρ (fun n => (hρgood n).1) (fun n => (hρgood n).2.2) hμρ (F j) (hFbounds j)
  have hsmallJEvent := hprefixIntegralLimit.eventually_lt_const
    (show 0 < c / 4 by positivity)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hsmallJEvent
  have hQsmall : ∫ ω, runningMinimum Q J ω ∂P < c / 4 := hJ J le_rfl
  let tol : ℝ := c / (4 * (J + 1))
  have htol : 0 < tol := by dsimp [tol]; positivity
  have hErrEventually (j : ℕ) : ∀ᶠ n in atTop,
      ∫ ω, |D j n ω - M j| ∂P < tol := (hErrLimit j).eventually_lt_const htol
  have hErrAll : ∀ᶠ n in atTop, ∀ j ∈ Finset.range (J + 1),
      ∫ ω, |D j n ω - M j| ∂P < tol := by
    exact (Finset.range (J + 1)).eventually_all.mpr fun j hj => hErrEventually j
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hErrAll
  have hErrAtN : ∀ j ∈ Finset.range (J + 1),
      ∫ ω, |D j n₀ ω - M j| ∂P < tol := hn₀ n₀ le_rfl
  let Err : ℕ → ℕ → Ω → ℝ := fun n K =>
    fun ω => ∑ j ∈ Finset.range (K + 1), |D j n ω - M j|
  have hEtaBoundAll : ∀ᵐ ω ∂P, ∀ j ∈ Finset.range (J + 1),
      Eta n₀ ω ≤ Q j ω + |D j n₀ ω - M j| := by
    exact (Finset.range (J + 1)).eventually_all.mpr fun j hj => (hEtaBound n₀ j).mono
      fun ω hω => hω
  have hGlobal : Eta n₀ ≤ᵐ[P] fun ω => runningMinimum Q J ω + Err n₀ J ω := by
    filter_upwards [hEtaBoundAll] with ω hAll
    obtain ⟨j, hjJ, hmin⟩ := runningMinimum_mem Q J ω
    have hjrange : j ∈ Finset.range (J + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hjJ)
    have herrsum : |D j n₀ ω - M j| ≤
        ∑ k ∈ Finset.range (J + 1), |D k n₀ ω - M k| :=
      Finset.single_le_sum (f := fun k => |D k n₀ ω - M k|) (a := j)
        (fun k hk => abs_nonneg _) hjrange
    calc
      Eta n₀ ω ≤ Q j ω + |D j n₀ ω - M j| := hAll j hjrange
      _ ≤ runningMinimum Q J ω + Err n₀ J ω := by
        dsimp [Err]
        rw [← hmin]
        exact add_le_add le_rfl herrsum
  have hEtaInt : Integrable (Eta n₀) P := by
    dsimp [Eta]
    exact integrable_condExp
  have hErrInt (j : ℕ) : Integrable (fun ω => |D j n₀ ω - M j|) P := by
    have hDint : Integrable (D j n₀) P := by
      dsimp [D]
      exact integrable_condExp
    exact (hDint.sub (integrable_const (M j))).abs
  have hErrSumInt : Integrable (Err n₀ J) P := by
    dsimp [Err]
    have hsumEq : (fun ω => ∑ j ∈ Finset.range (J + 1),
        |D j n₀ ω - M j|) =
        ∑ j ∈ Finset.range (J + 1), fun ω => |D j n₀ ω - M j| := by
      funext ω
      simp
    rw [hsumEq]
    exact integrable_finsetSum' (Finset.range (J + 1)) (fun j hj => hErrInt j)
  have hRhsInt : Integrable (fun ω => runningMinimum Q J ω + Err n₀ J ω) P :=
    (hQprefixInt J).add hErrSumInt
  have hEtaIntegral : (∫ ω, Eta n₀ ω ∂P) = ∫ ω, Ret n₀ φ ω ∂P := by
    dsimp [Eta]
    exact integral_condExp (hm n₀)
  have hretainedAtN := hretained (ρ n₀) (hρgood n₀).1 (hρgood n₀).2.1 (hρgood n₀).2.2
  have hEtaLower : c ≤ ∫ ω, Eta n₀ ω ∂P := by
    rw [hEtaIntegral]
    simpa only [Ret] using hretainedAtN.2
  have hErrIntegral : (∫ ω, Err n₀ J ω ∂P) ≤ c / 4 := by
    have hsumInt : (∫ ω, Err n₀ J ω ∂P) =
        ∑ j ∈ Finset.range (J + 1), ∫ ω, |D j n₀ ω - M j| ∂P := by
      dsimp [Err]
      exact integral_finsetSum (Finset.range (J + 1)) (fun j hj => hErrInt j)
    rw [hsumInt]
    calc
      _ ≤ ∑ j ∈ Finset.range (J + 1), tol :=
        Finset.sum_le_sum fun j hj => (hErrAtN j hj).le
      _ = (J + 1 : ℝ) * tol := by simp
      _ = c / 4 := by
        dsimp [tol]
        field_simp [ne_of_gt (show 0 < (J + 1 : ℝ) by positivity)]
  have hIntUpper := integral_mono_ae hEtaInt hRhsInt hGlobal
  have hImpossible : c < c / 2 := by
    calc
      c ≤ ∫ ω, Eta n₀ ω ∂P := hEtaLower
      _ ≤ ∫ ω, runningMinimum Q J ω + Err n₀ J ω ∂P := hIntUpper
      _ = (∫ ω, runningMinimum Q J ω ∂P) + ∫ ω, Err n₀ J ω ∂P :=
        integral_add (hQprefixInt J) hErrSumInt
      _ ≤ (∫ ω, runningMinimum Q J ω ∂P) + c / 4 := add_le_add le_rfl hErrIntegral
      _ < c / 2 := by linarith
  linarith

end Critical2DKPZ.NonGaussian

end
