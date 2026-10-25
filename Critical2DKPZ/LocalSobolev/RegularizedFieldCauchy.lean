/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.Inputs
public import Critical2DKPZ.LocalSobolev.RegularizedPairingMeasurability
public import Critical2DKPZ.LocalSobolev.ReversalLaw
public import Critical2DKPZ.LocalSobolev.InitialNegSobolev
public import Critical2DKPZ.LocalSobolev.ModulatedSobolevMomentBounds
import Critical2DKPZ.JointConvergence.KPZRegularizedReverseLaw
import Critical2DKPZ.JointConvergence.LogHeatFieldMeasurability
import Critical2DKPZ.Analysis.Sobolev.ExpectedHeatEnergy
import Critical2DKPZ.Analysis.Sobolev.Rellich.FrozenNorm
import Critical2DKPZ.Analysis.Sobolev.Rellich.FrozenDistributionBound
import Critical2DKPZ.Analysis.Sobolev.Rellich.RellichKernelFamilyBounds
import Critical2DKPZ.Analysis.Sobolev.TestFunctionFamily
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-! # The regularized field Cauchy estimate -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BoundedContinuousFunction ENNReal Topology

universe u

namespace Critical2DKPZ.LocalSobolev

private theorem locallyIntegrable_of_ae_bound {f : Plane → ℝ} {M : ℝ}
    (hf : AEStronglyMeasurable f volume)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ M) : LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  rw [IntegrableOn]
  have hKfinite : volume K < ⊤ := hK.measure_lt_top
  have hconstant : Integrable (fun _ : Plane => M) (volume.restrict K) := by
    exact (integrableOn_const_iff (μ := volume) (s := K) (C := M)).2
      (Or.inr hKfinite)
  refine hconstant.mono' hf.restrict ?_
  filter_upwards [ae_restrict_of_ae hbound] with x hx
  exact hx

private theorem ae_locallyIntegrable_kpzRegularized_of_initial (ϑ : ℝ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (h₀ : Plane →ᵇ ℝ) :
    ∀ᵐ ω ∂P, LocallyIntegrable (fun x => kpzRegularized P Z t δ h₀ x ω) volume := by
  obtain ⟨Y, hYmeas, hYeq, hYloc⟩ :=
    kpzRegularized_flat_locallyIntegrable_version_of ϑ P Z hZ hsym hδ hδt
  have hXhmeas := kpzRegularized_joint_aestronglyMeasurable_of_initial
    ϑ P Z hZ hδ hδt h₀
  have hX0meas := kpzRegularized_joint_aestronglyMeasurable_of_initial
    ϑ P Z hZ hδ hδt (0 : Plane →ᵇ ℝ)
  let Xh : Ω × Plane → ℝ := fun q => kpzRegularized P Z t δ h₀ q.2 q.1
  let X0 : Ω × Plane → ℝ := fun q => kpzRegularized P Z t δ 0 q.2 q.1
  let D : Ω × Plane → ℝ := fun q => Xh q - X0 q
  have hXh : AEStronglyMeasurable Xh (P.prod volume) := by
    simpa only [Xh] using hXhmeas
  have hX0 : AEStronglyMeasurable X0 (P.prod volume) := by
    simpa only [X0] using hX0meas
  have hD : AEStronglyMeasurable D (P.prod volume) := hXh.sub hX0
  let Dswap : Plane × Ω → ℝ := fun q => D (q.2, q.1)
  have hDswap : AEStronglyMeasurable Dswap (volume.prod P) := by
    simpa only [Dswap, Function.comp_def, Prod.swap] using
      hD.comp_measurePreserving
        (Measure.measurePreserving_swap (μ := volume) (ν := P))
  let E : Set ℝ := {r | |r| > ‖h₀‖}
  let Bad : Set (Plane × Ω) := Dswap ⁻¹' E
  have hE : MeasurableSet E := by
    dsimp [E]
    exact (isOpen_lt continuous_const continuous_abs).measurableSet
  have hBadMeas : NullMeasurableSet Bad (volume.prod P) :=
    hDswap.aemeasurable.nullMeasurableSet_preimage hE
  have hBadSlice (x : Plane) : P ((fun ω => (x, ω)) ⁻¹' Bad) = 0 := by
    have hAvoid : ∀ᵐ ω ∂P, |Dswap (x, ω)| ≤ ‖h₀‖ := by
      filter_upwards [kpzRegularized_shift_bound_ae ϑ P Z hZ hsym hδ hδt h₀ x]
        with ω hω
      simpa [Dswap, D, Xh, X0] using hω
    have hAvoidZero : P {ω | ¬ |Dswap (x, ω)| ≤ ‖h₀‖} = 0 := (ae_iff).1 hAvoid
    simpa [Bad, E, not_le] using hAvoidZero
  have hBadZero : (volume.prod P) Bad = 0 := by
    rw [Measure.prod_apply₀ hBadMeas]
    calc
      _ = ∫⁻ x : Plane, (0 : ℝ≥0∞) ∂volume := by
        apply lintegral_congr
        intro x
        exact hBadSlice x
      _ = 0 := by simp
  have hDswapBound : ∀ᵐ q : Plane × Ω ∂volume.prod P, |Dswap q| ≤ ‖h₀‖ := by
    rw [ae_iff]
    simpa [Bad, E, not_le] using hBadZero
  have hDbound : ∀ᵐ q : Ω × Plane ∂P.prod volume, |D q| ≤ ‖h₀‖ := by
    have h := (Measure.measurePreserving_swap (μ := P) (ν := volume)).quasiMeasurePreserving.ae
      hDswapBound
    simpa only [Dswap, Prod.swap] using h
  have hDsectionBound : ∀ᵐ ω ∂P, ∀ᵐ x ∂volume, |D (ω, x)| ≤ ‖h₀‖ :=
    Measure.ae_ae_of_ae_prod hDbound
  let Dm : Ω × Plane → ℝ := hD.aemeasurable.mk D
  have hDmeas : Measurable Dm := hD.aemeasurable.measurable_mk
  have hDeq : D =ᵐ[P.prod volume] Dm := hD.aemeasurable.ae_eq_mk
  have hDsectionMeas : ∀ᵐ ω ∂P, AEStronglyMeasurable (fun x => D (ω, x)) volume := by
    filter_upwards [Measure.ae_ae_of_ae_prod hDeq] with ω hω
    have hm : Measurable (fun x : Plane => Dm (ω, x)) :=
      hDmeas.comp (measurable_const.prodMk measurable_id)
    have hω' : (fun x : Plane => Dm (ω, x)) =ᵐ[volume] (fun x => D (ω, x)) :=
      hω.mono fun x hx => hx.symm
    exact hm.aestronglyMeasurable.congr hω'
  have hDloc : ∀ᵐ ω ∂P, LocallyIntegrable (fun x => D (ω, x)) volume := by
    filter_upwards [hDsectionMeas, hDsectionBound] with ω hωmeas hωbound
    have hωbound' : ∀ᵐ x ∂volume, ‖D (ω, x)‖ ≤ ‖h₀‖ := by
      filter_upwards [hωbound] with x hx
      simpa [Real.norm_eq_abs] using hx
    exact locallyIntegrable_of_ae_bound hωmeas hωbound'
  have hFlatLoc : ∀ᵐ ω ∂P, LocallyIntegrable (fun x => X0 (ω, x)) volume := by
    filter_upwards [Measure.ae_ae_of_ae_prod hYeq] with ω hω
    have hEq : (fun x => Y (ω, x)) =ᵐ[volume] (fun x => X0 (ω, x)) := by
      filter_upwards [hω] with x hx
      simpa [X0] using hx
    exact (hYloc ω).congr hEq
  filter_upwards [hFlatLoc, hDloc] with ω hω0 hωD
  have hsum : (fun x => X0 (ω, x)) + (fun x => D (ω, x)) =ᵐ[volume]
      (fun x => Xh (ω, x)) := by
    filter_upwards [] with x
    simp [D, Xh, X0]
  have hXhLoc := (hω0.add hωD).congr hsum
  simpa only [Xh] using hXhLoc

private theorem aemeasurable_kpzRegularizedDistribution_eval_of_initial (ϑ : ℝ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn) :
    AEMeasurable (fun ω => Distribution.ofFun ⊤
      (fun x => kpzRegularized P Z t δ h₀ x ω) volume ⊤ φ) P := by
  have hLI := ae_locallyIntegrable_kpzRegularized_of_initial
    ϑ P Z hZ hsym hδ hδt h₀
  have hPair := aemeasurable_integral_kpzRegularized_of ϑ P Z hZ hδ hδt h₀ φ
  have hEq : (fun ω => Distribution.ofFun ⊤
      (fun x => kpzRegularized P Z t δ h₀ x ω) volume ⊤ φ) =ᵐ[P]
      fun ω => ∫ x, φ x * kpzRegularized P Z t δ h₀ x ω := by
    filter_upwards [hLI] with ω hω
    exact Distribution.ofFun_apply (hω.locallyIntegrableOn _)
  exact hPair.congr hEq.symm

private theorem aemeasurable_uncurry_of_continuous_of_aemeasurable
    {α : Type*} [MeasurableSpace α] {ν : Measure Plane} {μ : Measure α} [SFinite μ]
    {f : Plane → α → ℂ}
    (hfcont : ∀ x, Continuous fun i => f i x)
    (hf : ∀ i, AEMeasurable (f i) μ) :
    AEMeasurable (Function.uncurry f) (ν.prod μ) := by
  classical
  let q : ℕ → SimpleFunc Plane Plane := stronglyMeasurable_id.approx
  let g (n : ℕ) (i : (q n).range) : α → ℂ := (hf i.1).mk (f i.1)
  have hg (n : ℕ) (i : (q n).range) : Measurable (g n i) :=
    (hf i.1).measurable_mk
  let G (n : ℕ) (z : Plane × α) : ℂ :=
    g n ⟨q n z.1, SimpleFunc.mem_range_self _ _⟩ z.2
  have hG (n : ℕ) : Measurable (G n) := by
    let H : α × (q n).range → ℂ := fun z => g n z.2 z.1
    have hH : Measurable H := measurable_from_prod_countable_left fun i => hg n i
    have hH' : Measurable (fun z : (q n).range × α => g n z.1 z.2) := by
      have hEq : (fun z : (q n).range × α => g n z.1 z.2) = H ∘ Prod.swap := rfl
      rw [hEq, measurable_swap_iff]
      exact hH
    have hfst : Measurable (fun ξ : Plane =>
        (⟨q n ξ, SimpleFunc.mem_range_self _ _⟩ : (q n).range)) := by
      exact (q n).measurable.subtype_mk
    have hmap : Measurable (fun z : Plane × α =>
        ((⟨q n z.1, SimpleFunc.mem_range_self _ _⟩ : (q n).range), z.2)) := by
      exact (hfst.comp measurable_fst).prodMk measurable_snd
    exact hH'.comp hmap
  have hω' (n : ℕ) : ∀ᵐ x ∂μ, ∀ i : (q n).range, g n i x = f i.1 x := by
    rw [ae_all_iff]
    intro i
    exact (hf i.1).ae_eq_mk.symm
  have hω : ∀ᵐ x ∂μ, ∀ n, ∀ i : (q n).range, g n i x = f i.1 x := by
    rw [ae_all_iff]
    exact hω'
  let S : Set α := {x | ∀ n, ∀ i : (q n).range, g n i x = f i.1 x}
  have hS : S =ᵐ[μ] univ := by
    filter_upwards [hω] with x hx
    simp [S, hx]
  have hωprodSet :=
    (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := μ)).preimage_ae_eq hS
  have hωprod : ∀ᵐ z ∂ν.prod μ, ∀ n, ∀ i : (q n).range,
      g n i z.2 = f i.1 z.2 := by
    filter_upwards [hωprodSet] with z hz
    have hzS : z.2 ∈ S := by
      change (z.2 ∈ S) = True at hz
      simpa using hz
    simpa [S] using hzS
  have hconv : ∀ᵐ z ∂ν.prod μ,
      Tendsto (fun n => G n z) atTop (𝓝 (f z.1 z.2)) := by
    filter_upwards [hωprod] with z hz
    have hseq : (fun n => G n z) = fun n => f (q n z.1) z.2 := by
      funext n
      exact hz n ⟨q n z.1, SimpleFunc.mem_range_self _ _⟩
    rw [hseq]
    exact (hfcont z.2).tendsto z.1 |>.comp (stronglyMeasurable_id.tendsto_approx z.1)
  exact aemeasurable_of_tendsto_metrizable_ae' (fun n => (hG n).aemeasurable) hconv

private theorem aemeasurable_localizedFourier_uncurry_of_pairings
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {T : Ω → Distr}
    (hT : ∀ φ : TestFn, AEMeasurable (fun ω => T ω φ) P) (χ : TestFn) :
    AEMeasurable (fun q : Ω × Plane => localizedFourier (T q.1) χ q.2) (P.prod volume) := by
  let f : Plane → Ω → ℂ := fun ξ ω => localizedFourier (T ω) χ ξ
  have hfcont (ω : Ω) : Continuous (f · ω) := continuous_localizedFourier (T ω) χ
  have hf (ξ : Plane) : AEMeasurable (f ξ) P := by
    dsimp [f, localizedFourier]
    have hmul : Measurable (fun r : ℝ => Complex.I * (r : ℂ)) :=
      (continuous_const.mul Complex.continuous_ofReal).measurable
    exact (Complex.continuous_ofReal.measurable.comp_aemeasurable
      (hT (χ.mulCos ξ))).sub (hmul.comp_aemeasurable (hT (χ.mulSin ξ)))
  have huncurry := aemeasurable_uncurry_of_continuous_of_aemeasurable
    (ν := volume) (μ := P) hfcont hf
  simpa [f, Function.uncurry, Prod.swap] using huncurry.prod_swap

private theorem aemeasurable_localizedFourierEnergy_uncurry_of_pairings
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {T : Ω → Distr}
    (hT : ∀ φ : TestFn, AEMeasurable (fun ω => T ω φ) P) (a : ℝ) (χ : TestFn) :
    AEMeasurable (fun q : Plane × Ω => ENNReal.ofReal
      ((1 + ‖q.1‖ ^ 2) ^ (-a) *
        ‖localizedFourier (T q.2) χ q.1‖ ^ 2)) (volume.prod P) := by
  have hFourier0 := aemeasurable_localizedFourier_uncurry_of_pairings P hT χ
  have hFourier : AEMeasurable
      (fun q : Plane × Ω => localizedFourier (T q.2) χ q.1) (volume.prod P) := by
    simpa only [Function.comp_def, Prod.swap] using hFourier0.prod_swap
  have hw : Measurable (fun ξ : Plane => (1 + ‖ξ‖ ^ 2) ^ (-a)) := by
    fun_prop
  have hweight : Measurable (fun q : Plane × Ω => (1 + ‖q.1‖ ^ 2) ^ (-a)) :=
    hw.comp measurable_fst
  exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable
    (hweight.aemeasurable.mul (hFourier.norm.pow_const 2))


private theorem aemeasurable_localNegSobolevSq_of_pairings
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : Ω → Distr} (hT : ∀ φ : TestFn, AEMeasurable (fun ω => T ω φ) P)
    (a : ℝ) (χ : TestFn) :
    AEMeasurable (fun ω => localNegSobolevSq a (T ω) χ) P := by
  have hjoint := aemeasurable_localizedFourierEnergy_uncurry_of_pairings P hT a χ
  have hinter := hjoint.lintegral_prod_left'
  simpa only [localNegSobolevSq, ← norm_localizedFourier_sq] using
    hinter.const_mul (ENNReal.ofReal ((2 * Real.pi)⁻¹ ^ 2))

private theorem aemeasurable_integral_kpzRegularizedReversed_of (ϑ : ℝ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t T δ : ℝ} (ht : 0 < t) (hδ : 0 < δ) (hδt : δ < T - t)
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn) :
    AEMeasurable (fun ω => ∫ x, φ x * kpzRegularizedReversed P Z t T δ h₀ x ω) P := by
  classical
  let μ : Ω → Measure (Plane × Plane) := fun ω => Z (t + δ) T ω
  have hμ : Measurable μ := hZ.1 (t + δ) T (by linarith) (by linarith)
  have hlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
    filter_upwards [hZ.2.1 (t + δ) T (by linarith) (by linarith)] with ω hω
    exact hω.1
  let g : Plane → ℝ := fun y => Real.exp (h₀ y)
  have hg : Measurable g := (Real.continuous_exp.comp h₀.continuous).measurable
  have hgn : ∀ y, 0 ≤ g y := fun y => (Real.exp_pos _).le
  let c : ℝ := ∫ ω', Real.log
    (shfPairing Z (t + δ) T (fun y => heatKernel δ y) (fun _ => 1) ω') ∂P
  have hlog := JointConvergence.aemeasurable_integral_log_heatPairing
    P μ hμ hlocal δ c hδ g φ hg hgn φ.continuous.measurable
  change AEMeasurable (fun ω => ∫ x, φ x *
      (Real.log (∫ p, heatKernel δ (p.1 - x) * g p.2 ∂μ ω) - c)) P
  simpa [kpzRegularizedReversed, shfPairing, g, c, μ] using hlog

private theorem localNegSobolevSq_sub_le (a : ℝ) (T U : Distr) (χ : TestFn) :
    localNegSobolevSq a (T - U) χ ≤
      2 * localNegSobolevSq a T χ + 2 * localNegSobolevSq a U χ := by
  have hfourier : localizedFourier (T - U) χ =
      localizedFourier T χ - localizedFourier U χ := by
    funext ξ
    change ((T - U) (χ.mulCos ξ) : ℂ) -
        Complex.I * ((T - U) (χ.mulSin ξ) : ℂ) =
      (((T (χ.mulCos ξ) : ℂ) - Complex.I * (T (χ.mulSin ξ) : ℂ)) -
        ((U (χ.mulCos ξ) : ℂ) - Complex.I * (U (χ.mulSin ξ) : ℂ)))
    simp only [sub_apply, Complex.ofReal_sub]
    ring
  have hnorm : localNegSobolevENorm a (T - U) χ ≤
      localNegSobolevENorm a T χ + localNegSobolevENorm a U χ := by
    rw [localNegSobolevENorm, hfourier]
    exact eLpNorm_sub_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hpow := ENNReal.rpow_le_rpow hnorm (by norm_num : (0 : ℝ) ≤ 2)
  calc
    localNegSobolevSq a (T - U) χ = localNegSobolevENorm a (T - U) χ ^ 2 :=
      (localNegSobolevENorm_sq a (T - U) χ).symm
    _ ≤ (localNegSobolevENorm a T χ + localNegSobolevENorm a U χ) ^ (2 : ℝ) := by
      simpa only [ENNReal.rpow_two] using hpow
    _ ≤ 2 * (localNegSobolevENorm a T χ ^ 2 + localNegSobolevENorm a U χ ^ 2) := by
      have h := ENNReal.rpow_add_le_mul_rpow_add_rpow
        (localNegSobolevENorm a T χ) (localNegSobolevENorm a U χ)
        (by norm_num : (1 : ℝ) ≤ 2)
      norm_num at h ⊢
      exact h
    _ = 2 * localNegSobolevSq a T χ + 2 * localNegSobolevSq a U χ := by
      rw [localNegSobolevENorm_sq, localNegSobolevENorm_sq]
      ring

private theorem lintegral_localNegSobolevSq_sub_le_of_moment
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {t s C : ℝ} (F : ℝ → Ω → Distr)
    (hF : ∀ δ, 0 < δ → δ < t / 2 → ∀ φ,
      AEMeasurable (fun ω => F δ ω φ) P)
    (χ : TestFn) (hC : 0 ≤ C)
    (hMoment : ∀ δ, 0 < δ → δ < t / 2 →
      ∫⁻ ω, localNegSobolevSq s (F δ ω) χ ∂P ≤ ENNReal.ofReal C)
    (p : ℝ × ℝ) (hp₁ : 0 < p.1) (hp₁t : p.1 < t / 2)
    (hp₂ : 0 < p.2) (hp₂t : p.2 < t / 2) :
    ∫⁻ ω, localNegSobolevSq s (F p.1 ω - F p.2 ω) χ ∂P ≤
      ENNReal.ofReal (4 * C) := by
  have hE₁ := aemeasurable_localNegSobolevSq_of_pairings P (hF p.1 hp₁ hp₁t) s χ
  have hE₂ := aemeasurable_localNegSobolevSq_of_pairings P (hF p.2 hp₂ hp₂t) s χ
  calc
    _ ≤ ∫⁻ ω, 2 * localNegSobolevSq s (F p.1 ω) χ +
        2 * localNegSobolevSq s (F p.2 ω) χ ∂P := by
      apply lintegral_mono
      intro ω
      exact localNegSobolevSq_sub_le s (F p.1 ω) (F p.2 ω) χ
    _ = 2 * ∫⁻ ω, localNegSobolevSq s (F p.1 ω) χ ∂P +
        2 * ∫⁻ ω, localNegSobolevSq s (F p.2 ω) χ ∂P := by
      have hscaled₁ : AEMeasurable
          (fun ω => (2 : ℝ≥0∞) * localNegSobolevSq s (F p.1 ω) χ) P :=
        (ENNReal.continuous_const_mul (by simp : (2 : ℝ≥0∞) ≠ ⊤)).measurable.comp_aemeasurable hE₁
      rw [lintegral_add_left' hscaled₁,
        lintegral_const_mul'' (2 : ℝ≥0∞) hE₁,
        lintegral_const_mul'' (2 : ℝ≥0∞) hE₂]
    _ ≤ 2 * ENNReal.ofReal C + 2 * ENNReal.ofReal C := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hMoment p.1 hp₁ hp₁t) bot_le)
        (mul_le_mul_of_nonneg_left (hMoment p.2 hp₂ hp₂t) bot_le)
    _ = ENNReal.ofReal (4 * C) := by
      have hC' : 0 ≤ 2 * C := by positivity
      rw [show 4 * C = 2 * C + 2 * C by ring,
        ENNReal.ofReal_add (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC)]
      have hmul : ENNReal.ofReal (2 * C) = 2 * ENNReal.ofReal C := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      rw [hmul]

/-- The expected square of a measurable test pairing is controlled by the expected localized
negative Sobolev energy on any cutoff equal to one over the test support. -/
theorem lintegral_pairing_sq_le_of_local_energy
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : Ω → Distr} (hT : ∀ φ : TestFn, AEMeasurable (fun ω => T ω φ) P)
    (s : ℝ) (ψ φ : TestFn) (hψ : ∀ x ∈ tsupport φ, ψ x = 1)
    {C : ℝ} (hC : ∫⁻ ω, localNegSobolevSq s (T ω) ψ ∂P ≤ ENNReal.ofReal C) :
    ∫⁻ ω, ENNReal.ofReal ((T ω φ) ^ 2) ∂P ≤
      Analysis.Sobolev.Rellich.sobolevNormSq 2 s (fun x => (φ x : ℝ)) * ENNReal.ofReal C := by
  let S := Analysis.Sobolev.Rellich.sobolevNormSq 2 s (fun x => (φ x : ℝ))
  have hpoint (ω : Ω) : ENNReal.ofReal ((T ω φ) ^ 2) ≤
      S * localNegSobolevSq s (T ω) ψ := by
    have hdual := Analysis.Sobolev.Rellich.distribution_pairing_le_localNegSobolev_product
      s (T ω) ψ φ hψ
    have hsq := ENNReal.rpow_le_rpow hdual (by norm_num : 0 ≤ (2 : ℝ))
    have hlhs : (ENNReal.ofReal |T ω φ|) ^ (2 : ℝ) =
        ENNReal.ofReal ((T ω φ) ^ 2) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num : 0 ≤ (2 : ℝ))]
      rw [Real.rpow_two, sq_abs]
    have hrhs : ((S ^ ((1 : ℝ) / 2)) *
        (localNegSobolevSq s (T ω) ψ) ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) =
        S * localNegSobolevSq s (T ω) ψ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (2 : ℝ)),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      congr 1 <;> norm_num
    rw [hlhs, hrhs] at hsq
    simpa [S] using hsq
  have henergy := aemeasurable_localNegSobolevSq_of_pairings P hT s ψ
  calc
    _ ≤ ∫⁻ ω, S * localNegSobolevSq s (T ω) ψ ∂P := by
      apply lintegral_mono
      exact hpoint
    _ = S * ∫⁻ ω, localNegSobolevSq s (T ω) ψ ∂P :=
      lintegral_const_mul'' S henergy
    _ ≤ S * ENNReal.ofReal C := by gcongr

private theorem lintegral_localNegSobolevSq_eq_expectedFourierEnergy
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : Ω → Distr}
    (hT : ∀ φ : TestFn, AEMeasurable (fun ω => T ω φ) P)
    (a : ℝ) (χ : TestFn) :
    ∫⁻ ω, localNegSobolevSq a (T ω) χ ∂P =
      ENNReal.ofReal ((2 * Real.pi)⁻¹ ^ 2) *
        ∫⁻ ξ : Plane, ∫⁻ ω, ENNReal.ofReal
          ((1 + ‖ξ‖ ^ 2) ^ (-a) *
            ‖localizedFourier (T ω) χ ξ‖ ^ 2) ∂P := by
  have hjoint := aemeasurable_localizedFourierEnergy_uncurry_of_pairings P hT a χ
  have hslice := hjoint.lintegral_prod_left'
  calc
    _ = ∫⁻ ω, ENNReal.ofReal ((2 * Real.pi)⁻¹ ^ 2) *
        ∫⁻ ξ : Plane, ENNReal.ofReal
          ((1 + ‖ξ‖ ^ 2) ^ (-a) *
            ‖localizedFourier (T ω) χ ξ‖ ^ 2) ∂volume ∂P := by
      apply lintegral_congr
      intro ω
      simp only [localNegSobolevSq, ← norm_localizedFourier_sq]
    _ = ENNReal.ofReal ((2 * Real.pi)⁻¹ ^ 2) *
        ∫⁻ ω, ∫⁻ ξ : Plane, ENNReal.ofReal
          ((1 + ‖ξ‖ ^ 2) ^ (-a) *
            ‖localizedFourier (T ω) χ ξ‖ ^ 2) ∂volume ∂P :=
      lintegral_const_mul'' _ hslice
    _ = ENNReal.ofReal ((2 * Real.pi)⁻¹ ^ 2) *
        ∫⁻ ξ : Plane, ∫⁻ ω, ENNReal.ofReal
          ((1 + ‖ξ‖ ^ 2) ^ (-a) *
            ‖localizedFourier (T ω) χ ξ‖ ^ 2) ∂P := by
      rw [lintegral_lintegral_swap hjoint.prod_swap]

private theorem lintegral_weightedFourier_eq_pairings
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {T : Ω → Distr}
    (hT : ∀ φ : TestFn, AEMeasurable (fun ω => T ω φ) P)
    (a : ℝ) (χ : TestFn) (ξ : Plane) :
    ∫⁻ ω, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-a) *
        ‖localizedFourier (T ω) χ ξ‖ ^ 2) ∂P =
      ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-a)) *
        (∫⁻ ω, ENNReal.ofReal ((T ω (χ.mulCos ξ)) ^ 2) ∂P +
          ∫⁻ ω, ENNReal.ofReal ((T ω (χ.mulSin ξ)) ^ 2) ∂P) := by
  let w : ℝ := (1 + ‖ξ‖ ^ 2) ^ (-a)
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hpoint (ω : Ω) : ENNReal.ofReal (w *
      ‖localizedFourier (T ω) χ ξ‖ ^ 2) =
      ENNReal.ofReal w *
        (ENNReal.ofReal ((T ω (χ.mulCos ξ)) ^ 2) +
          ENNReal.ofReal ((T ω (χ.mulSin ξ)) ^ 2)) := by
    rw [norm_localizedFourier_sq]
    rw [ENNReal.ofReal_mul hw,
      ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  calc
    _ = ∫⁻ ω, ENNReal.ofReal w *
        (ENNReal.ofReal ((T ω (χ.mulCos ξ)) ^ 2) +
          ENNReal.ofReal ((T ω (χ.mulSin ξ)) ^ 2)) ∂P := by
      apply lintegral_congr
      intro ω
      exact hpoint ω
    _ = _ := by
      have hcosSq : AEMeasurable (fun ω => (T ω (χ.mulCos ξ)) ^ 2) P :=
        (continuous_id.pow 2).measurable.comp_aemeasurable (hT (χ.mulCos ξ))
      have hcos : AEMeasurable (fun ω => ENNReal.ofReal
          ((T ω (χ.mulCos ξ)) ^ 2)) P :=
        ENNReal.continuous_ofReal.measurable.comp_aemeasurable hcosSq
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left' hcos]

private theorem tendsto_lintegral_ofReal_sq_of_eLpNorm
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : ι → Ω → ℝ)
    (hmeas : ∀ᶠ i in l, AEMeasurable (f i) μ)
    (hnorm : Tendsto (fun i => eLpNorm (f i) 2 μ) l (𝓝 (0 : ℝ≥0∞))) :
    Tendsto (fun i => ∫⁻ ω, ENNReal.ofReal ((f i ω) ^ 2) ∂μ) l (𝓝 0) := by
  have heq (i : ι) (hi : AEMeasurable (f i) μ) :
      eLpNorm (f i) 2 μ ^ 2 = ∫⁻ ω, ENNReal.ofReal ((f i ω) ^ 2) ∂μ := by
    have hpow := eLpNorm_nnreal_pow_eq_lintegral (f := f i) (p := (2 : NNReal))
      (by norm_num) hi.aestronglyMeasurable
    have hpow' : eLpNorm (f i) 2 μ ^ 2 =
        ∫⁻ ω, ENNReal.ofReal (‖f i ω‖ ^ 2) ∂μ := by
      simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two,
        ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)] using hpow
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (‖f i ω‖ ^ 2) ∂μ := hpow'
      _ = _ := by
        apply lintegral_congr
        intro ω
        congr 1
        rw [Real.norm_eq_abs, sq_abs]
  have hpow : Tendsto (fun i => eLpNorm (f i) 2 μ ^ 2) l (𝓝 (0 : ℝ≥0∞)) := by
    have hpow' := hnorm.ennrpow_const (2 : ℝ)
    simpa only [ENNReal.rpow_two, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] using hpow'
  have hEq : (fun i => eLpNorm (f i) 2 μ ^ 2) =ᶠ[l]
      (fun i => ∫⁻ ω, ENNReal.ofReal ((f i ω) ^ 2) ∂μ) :=
    hmeas.mono fun i hi => heq i hi
  exact hpow.congr' hEq

/-- Every fixed test pairing of the forward regularized field is Cauchy in L² under the reversed-field convergence hypothesis. -/
theorem kpzRegularized_testPairing_cauchy_of (ϑ : ℝ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hC12 : ToyJointAt ϑ P Z) {t : ℝ} (ht : 0 < t)
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn) :
    Tendsto (fun p : ℝ × ℝ => eLpNorm (fun ω =>
        (∫ x, φ x * kpzRegularized P Z t p.1 h₀ x ω) -
          (∫ x, φ x * kpzRegularized P Z t p.2 h₀ x ω)) 2 P)
      (nhdsWithin 0 (Ioi 0) ×ˢ nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  let T : ℝ := 2 * t
  have hT : 0 < T := by dsimp [T]; positivity
  obtain ⟨X, hXmeas, hXrate, hXLp, hXlat, hXlaw⟩ := hC12 T hT
  have hXLpPair := hXLp t h₀ φ 2 (by linarith [ht])
    (by dsimp [T]; linarith [ht]) (by norm_num) (by norm_num)
  let A : ℝ → Ω → ℝ := fun δ ω =>
    ∫ x, φ x * kpzRegularized P Z t δ h₀ x ω
  let B : ℝ → Ω → ℝ := fun δ ω =>
    ∫ x, φ x * kpzRegularizedReversed P Z t T δ h₀ x ω
  let vecF : ℝ × ℝ → Ω → Fin 2 → ℝ := fun p ω i =>
    if i.val = 0 then A p.1 ω else A p.2 ω
  let vecR : ℝ × ℝ → Ω → Fin 2 → ℝ := fun p ω i =>
    if i.val = 0 then B p.1 ω else B p.2 ω
  let diffV : (Fin 2 → ℝ) → ℝ := fun v => v 0 - v 1
  have hdiffmeas : Measurable diffV := by
    apply Measurable.sub
    · exact measurable_pi_apply 0
    · exact measurable_pi_apply 1
  have hdiffsm (μ : Measure (Fin 2 → ℝ)) :
      AEStronglyMeasurable diffV μ := hdiffmeas.aestronglyMeasurable
  have hforwardAE (p : ℝ × ℝ) (hp : 0 < p.1 ∧ p.1 < t ∧ 0 < p.2 ∧ p.2 < t) :
      AEMeasurable (vecF p) P := by
    apply aemeasurable_pi_iff.mpr
    intro i
    by_cases hi : i.val = 0
    · have hi0 : i = 0 := Fin.ext hi
      subst i
      simpa [vecF, A] using
        aemeasurable_integral_kpzRegularized_of ϑ P Z hZ hp.1 hp.2.1 h₀ φ
    · have hi1 : i = 1 := by
        apply Fin.ext
        have hv := i.isLt
        omega
      subst i
      simpa [vecF, A] using
        aemeasurable_integral_kpzRegularized_of ϑ P Z hZ hp.2.2.1 hp.2.2.2 h₀ φ
  have hreverseAE (p : ℝ × ℝ) (hp : 0 < p.1 ∧ p.1 < t ∧ 0 < p.2 ∧ p.2 < t) :
      AEMeasurable (vecR p) P := by
    apply aemeasurable_pi_iff.mpr
    intro i
    by_cases hi : i.val = 0
    · have hi0 : i = 0 := Fin.ext hi
      subst i
      simpa [vecR, B] using
        aemeasurable_integral_kpzRegularizedReversed_of ϑ P Z hZ ht hp.1
          (by change p.1 < 2 * t - t; linarith [hp.2.1]) h₀ φ
    · have hi1 : i = 1 := by
        apply Fin.ext
        have hv := i.isLt
        omega
      subst i
      simpa [vecR, B] using
        aemeasurable_integral_kpzRegularizedReversed_of ϑ P Z hZ ht hp.2.2.1
          (by change p.2 < 2 * t - t; linarith [hp.2.2.2]) h₀ φ
  have hmap (p : ℝ × ℝ) (hp : 0 < p.1 ∧ p.1 < t ∧ 0 < p.2 ∧ p.2 < t) :
      P.map (vecF p) = P.map (vecR p) := by
    let δ : Fin 2 → ℝ := fun i => if i.val = 0 then p.1 else p.2
    let times : Fin 2 → ℝ := fun _ => t
    have hδ : ∀ i, 0 < δ i ∧ δ i < times i ∧ times i ≤ T := by
      intro i
      fin_cases i
      · simp only [δ, Fin.zero_eta, Fin.val_zero, ↓reduceIte, times]
        exact ⟨hp.1, hp.2.1, by dsimp [T]; linarith [ht]⟩
      · simp only [δ, Fin.mk_one, Fin.val_one, times]
        exact ⟨hp.2.2.1, hp.2.2.2, by dsimp [T]; linarith [ht]⟩
    have hrev := JointConvergence.kpzRegularized_reverse_law_of ϑ P Z hZ T
      (shfReversal_measureLaw_of ϑ P Z hZ T) 2 times δ (fun _ => h₀)
      (fun _ => φ) hδ
    have hvecF : (fun ω i => ∫ x, φ x *
        kpzRegularized P Z t (δ i) h₀ x ω) = vecF p := by
      funext ω i
      by_cases hi : i.val = 0
      · have hi0 : i = 0 := Fin.ext hi
        subst i
        simp [δ, vecF, A]
      · have hi1 : i = 1 := by
          apply Fin.ext
          have hv := i.isLt
          omega
        subst i
        simp [δ, vecF, A]
    have hvecR : (fun ω i => ∫ x, φ x *
        kpzRegularizedReversed P Z (T - t) T (δ i) h₀ x ω) = vecR p := by
      have hTt : T - t = t := by dsimp [T]; ring
      funext ω i
      by_cases hi : i.val = 0
      · have hi0 : i = 0 := Fin.ext hi
        subst i
        simp [δ, vecR, B, hTt]
      · have hi1 : i = 1 := by
          apply Fin.ext
          have hv := i.isLt
          omega
        subst i
        simp [δ, vecR, B, hTt]
    rw [← hvecF, ← hvecR]
    exact hrev
  have hpairwise (p : ℝ × ℝ) (hp : 0 < p.1 ∧ p.1 < t ∧ 0 < p.2 ∧ p.2 < t) :
      eLpNorm (fun ω => A p.1 ω - A p.2 ω) 2 P ≤
        eLpNorm (fun ω => B p.1 ω - X t h₀ φ ω) 2 P +
          eLpNorm (fun ω => B p.2 ω - X t h₀ φ ω) 2 P := by
    have hF := hforwardAE p hp
    have hR := hreverseAE p hp
    have hmap' := hmap p hp
    have hscalarMap : P.map (diffV ∘ vecF p) = P.map (diffV ∘ vecR p) := by
      calc
        P.map (diffV ∘ vecF p) = (P.map (vecF p)).map diffV :=
          (AEMeasurable.map_map_of_aemeasurable hdiffmeas.aemeasurable hF).symm
        _ = (P.map (vecR p)).map diffV := by rw [hmap']
        _ = P.map (diffV ∘ vecR p) :=
          AEMeasurable.map_map_of_aemeasurable hdiffmeas.aemeasurable hR
    have hnormMap :
        eLpNorm (diffV ∘ vecF p) 2 P = eLpNorm (diffV ∘ vecR p) 2 P := by
      calc
        eLpNorm (diffV ∘ vecF p) 2 P =
            eLpNorm diffV 2 (P.map (vecF p)) :=
          (eLpNorm_map_measure (hdiffsm (P.map (vecF p))) hF).symm
        _ = eLpNorm diffV 2 (P.map (vecR p)) := by rw [hmap']
        _ = eLpNorm (diffV ∘ vecR p) 2 P :=
          eLpNorm_map_measure (hdiffsm (P.map (vecR p))) hR
    have hleft :
        eLpNorm (fun ω => B p.1 ω - B p.2 ω) 2 P ≤
          eLpNorm (fun ω => B p.1 ω - X t h₀ φ ω) 2 P +
            eLpNorm (fun ω => B p.2 ω - X t h₀ φ ω) 2 P := by
      calc
        _ = eLpNorm (fun ω =>
            (B p.1 ω - X t h₀ φ ω) - (B p.2 ω - X t h₀ φ ω)) 2 P := by
          congr 1
          funext ω
          ring
        _ ≤ _ := eLpNorm_sub_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hFpair : diffV ∘ vecF p = fun ω => A p.1 ω - A p.2 ω := by
      funext ω
      simp [diffV, vecF, A]
    have hRpair : diffV ∘ vecR p = fun ω => B p.1 ω - B p.2 ω := by
      funext ω
      simp [diffV, vecR, B]
    rw [hFpair, hRpair] at hnormMap
    rw [hnormMap]
    exact hleft
  have hleftLimit : Tendsto (fun p : ℝ × ℝ =>
      eLpNorm (fun ω => B p.1 ω - X t h₀ φ ω) 2 P)
      (nhdsWithin 0 (Ioi 0) ×ˢ nhdsWithin 0 (Ioi 0)) (𝓝 0) :=
    (hXLpPair.comp tendsto_fst).congr' (Filter.Eventually.of_forall fun _ => rfl)
  have hrightLimit : Tendsto (fun p : ℝ × ℝ =>
      eLpNorm (fun ω => B p.2 ω - X t h₀ φ ω) 2 P)
      (nhdsWithin 0 (Ioi 0) ×ˢ nhdsWithin 0 (Ioi 0)) (𝓝 0) :=
    (hXLpPair.comp tendsto_snd).congr' (Filter.Eventually.of_forall fun _ => rfl)
  have hsumLimit : Tendsto (fun p : ℝ × ℝ =>
      eLpNorm (fun ω => B p.1 ω - X t h₀ φ ω) 2 P +
        eLpNorm (fun ω => B p.2 ω - X t h₀ φ ω) 2 P)
      (nhdsWithin 0 (Ioi 0) ×ˢ nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    simpa using hleftLimit.add hrightLimit
  have hfst : Tendsto (fun p : ℝ × ℝ => p.1)
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)) ×ˢ nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)))
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) :=
    tendsto_fst
  have hsnd : Tendsto (fun p : ℝ × ℝ => p.2)
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)) ×ˢ nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)))
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) :=
    tendsto_snd
  have hIio : Iio t ∈ nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)) :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      ⟨Iio t, Iio_mem_nhds ht, by intro x hx; exact hx.1⟩
  have hev1 : ∀ᶠ p : ℝ × ℝ in nhdsWithin 0 (Ioi 0) ×ˢ nhdsWithin 0 (Ioi 0),
      0 < p.1 ∧ p.1 < t := by
    filter_upwards [hfst.eventually_mem self_mem_nhdsWithin,
      hfst.eventually_mem hIio] with p hp₀ hpt
    exact ⟨hp₀, hpt⟩
  have hev2 : ∀ᶠ p : ℝ × ℝ in nhdsWithin 0 (Ioi 0) ×ˢ nhdsWithin 0 (Ioi 0),
      0 < p.2 ∧ p.2 < t := by
    filter_upwards [hsnd.eventually_mem self_mem_nhdsWithin,
      hsnd.eventually_mem hIio] with p hp₀ hpt
    exact ⟨hp₀, hpt⟩
  have hbound : ∀ᶠ p : ℝ × ℝ in nhdsWithin 0 (Ioi 0) ×ˢ nhdsWithin 0 (Ioi 0),
      eLpNorm (fun ω => A p.1 ω - A p.2 ω) 2 P ≤
        eLpNorm (fun ω => B p.1 ω - X t h₀ φ ω) 2 P +
          eLpNorm (fun ω => B p.2 ω - X t h₀ φ ω) 2 P := by
    filter_upwards [hev1, hev2] with p hp₁ hp₂
    exact hpairwise p ⟨hp₁.1, hp₁.2, hp₂.1, hp₂.2⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsumLimit
  · exact Filter.Eventually.of_forall fun _ => bot_le
  · exact hbound

/-- The regularized fields are Cauchy in expected local negative Sobolev energy. -/
theorem kpzRegularized_negSobolev_cauchy_of (hVD : Smoothing.PropVDBound) (ϑ : ℝ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hHeatStartLogInput : HeatStartLogAt ϑ P Z) (hsym : ShfSymmetriesAt ϑ P Z) (hC12 : ToyJointAt ϑ P Z)
    {t : ℝ} (ht : 0 < t) (h₀ : Plane →ᵇ ℝ) {a : ℝ} (ha : 0 < a) (χ : TestFn) :
    Tendsto (fun p : ℝ × ℝ => ∫⁻ ω, localNegSobolevSq a
        (Distribution.ofFun ⊤ (fun x => kpzRegularized P Z t p.1 h₀ x ω) volume ⊤ -
          Distribution.ofFun ⊤ (fun x => kpzRegularized P Z t p.2 h₀ x ω) volume ⊤) χ ∂P)
      (nhdsWithin 0 (Set.Ioi 0) ×ˢ nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  let l := nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)) ×ˢ nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))
  let F : ℝ → Ω → Distr := fun δ ω =>
    Distribution.ofFun ⊤ (fun x => kpzRegularized P Z t δ h₀ x ω) volume ⊤
  let D : ℝ × ℝ → Ω → Distr := fun p ω => F p.1 ω - F p.2 ω
  have hfst : Tendsto (fun p : ℝ × ℝ => p.1) l (nhdsWithin 0 (Ioi 0)) := tendsto_fst
  have hsnd : Tendsto (fun p : ℝ × ℝ => p.2) l (nhdsWithin 0 (Ioi 0)) := tendsto_snd
  have hsmall : Iio (t / 2) ∈ nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)) := by
    apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    refine ⟨Iio (t / 2), Iio_mem_nhds (by linarith [ht]), ?_⟩
    intro x hx
    exact hx.1
  have hpos₁ : ∀ᶠ p in l, 0 < p.1 ∧ p.1 < t / 2 := by
    filter_upwards [hfst.eventually_mem self_mem_nhdsWithin,
      hfst.eventually_mem hsmall] with p hp₀ hpt
    exact ⟨hp₀, hpt⟩
  have hpos₂ : ∀ᶠ p in l, 0 < p.2 ∧ p.2 < t / 2 := by
    filter_upwards [hsnd.eventually_mem self_mem_nhdsWithin,
      hsnd.eventually_mem hsmall] with p hp₀ hpt
    exact ⟨hp₀, hpt⟩
  have hpos : ∀ᶠ p in l, 0 < p.1 ∧ p.1 < t / 2 ∧ 0 < p.2 ∧ p.2 < t / 2 := by
    filter_upwards [hpos₁, hpos₂] with p hp₁ hp₂
    exact ⟨hp₁.1, hp₁.2, hp₂.1, hp₂.2⟩
  have hFpair (δ : ℝ) (hδ : 0 < δ) (hδt : δ < t / 2) (φ : TestFn) :
      AEMeasurable (fun ω => F δ ω φ) P := by
    simpa only [F] using aemeasurable_kpzRegularizedDistribution_eval_of_initial
      ϑ P Z hZ hsym hδ (by linarith [hδt, ht]) h₀ φ
  have hFpairEq (δ : ℝ) (hδ : 0 < δ) (hδt : δ < t / 2) (φ : TestFn) :
      (fun ω => F δ ω φ) =ᵐ[P]
        (fun ω => ∫ x, φ x * kpzRegularized P Z t δ h₀ x ω) := by
    filter_upwards [ae_locallyIntegrable_kpzRegularized_of_initial
      ϑ P Z hZ hsym (t := t) (δ := δ) hδ (by linarith [hδt, ht]) h₀] with ω hω
    exact Distribution.ofFun_apply (hω.locallyIntegrableOn _)
  have hDpair (p : ℝ × ℝ) (hp : 0 < p.1 ∧ p.1 < t / 2 ∧ 0 < p.2 ∧ p.2 < t / 2)
      (φ : TestFn) : AEMeasurable (fun ω => D p ω φ) P := by
    dsimp [D]
    exact (hFpair p.1 hp.1 hp.2.1 φ).sub (hFpair p.2 hp.2.2.1 hp.2.2.2 φ)
  have hPairSqLimit (φ : TestFn) : Tendsto
      (fun p : ℝ × ℝ => ∫⁻ ω, ENNReal.ofReal ((D p ω φ) ^ 2) ∂P) l (𝓝 0) := by
    have hmeas : ∀ᶠ p in l, AEMeasurable (fun ω => D p ω φ) P := by
      filter_upwards [hpos] with p hp
      exact hDpair p ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩ φ
    have hnorm : Tendsto (fun p : ℝ × ℝ => eLpNorm (fun ω => D p ω φ) 2 P) l
        (𝓝 (0 : ℝ≥0∞)) := by
      have hbase := kpzRegularized_testPairing_cauchy_of ϑ P Z hZ hC12 ht h₀ φ
      have hEq : (fun p : ℝ × ℝ => eLpNorm (fun ω => D p ω φ) 2 P) =ᶠ[l]
          (fun p => eLpNorm (fun ω =>
            (∫ x, φ x * kpzRegularized P Z t p.1 h₀ x ω) -
              (∫ x, φ x * kpzRegularized P Z t p.2 h₀ x ω)) 2 P) := by
        filter_upwards [hpos] with p hp
        have hpairEq : (fun ω => D p ω φ) =ᵐ[P]
            (fun ω =>
              (∫ x, φ x * kpzRegularized P Z t p.1 h₀ x ω) -
                (∫ x, φ x * kpzRegularized P Z t p.2 h₀ x ω)) := by
          filter_upwards [hFpairEq p.1 hp.1 hp.2.1 φ,
            hFpairEq p.2 hp.2.2.1 hp.2.2.2 φ] with ω h₁ h₂
          change F p.1 ω φ - F p.2 ω φ = _
          rw [h₁, h₂]
        exact eLpNorm_congr_ae hpairEq
      exact hbase.congr' hEq.symm
    exact tendsto_lintegral_ofReal_sq_of_eLpNorm P (fun p ω => D p ω φ) hmeas hnorm
  let s : ℝ := a / 2
  have hspos : 0 < s := by dsimp [s]; linarith [ha]
  obtain ⟨N, hN⟩ := exists_localizer_eq_one_on_compact χ.hasCompactSupport.isCompact
  let ψ : TestFn := localizer N
  have hψ : ∀ x ∈ tsupport χ, ψ x = 1 := by
    intro x hx
    exact hN N le_rfl x hx
  have hFpairForMoment : ∀ δ, 0 < δ → δ < t / 2 → ∀ φ,
      AEMeasurable (fun ω => F δ ω φ) P := by
    intro δ hδ hδt φ
    exact hFpair δ hδ hδt φ
  obtain ⟨Cψ, hCψ⟩ := kpzRegularized_negSobolev_moment_le_of
    hVD ϑ P Z hZ hHeatStartLogInput hsym ht h₀ (a := s) hspos ψ
  obtain ⟨Cχ, hCχ⟩ := kpzRegularized_negSobolev_moment_le_of
    hVD ϑ P Z hZ hHeatStartLogInput hsym ht h₀ (a := s) hspos χ
  let Cψ₀ : ℝ := max Cψ 0
  let Cχ₀ : ℝ := max Cχ 0
  have hCψ₀ : 0 ≤ Cψ₀ := le_max_right Cψ 0
  have hCχ₀ : 0 ≤ Cχ₀ := le_max_right Cχ 0
  have hMomentψ (δ : ℝ) (hδ : 0 < δ) (hδt : δ < t / 2) :
      ∫⁻ ω, localNegSobolevSq s (F δ ω) ψ ∂P ≤ ENNReal.ofReal Cψ₀ :=
    (hCψ δ hδ hδt).trans (ENNReal.ofReal_le_ofReal (le_max_left Cψ 0))
  have hMomentχ (δ : ℝ) (hδ : 0 < δ) (hδt : δ < t / 2) :
      ∫⁻ ω, localNegSobolevSq s (F δ ω) χ ∂P ≤ ENNReal.ofReal Cχ₀ :=
    (hCχ δ hδ hδt).trans (ENNReal.ofReal_le_ofReal (le_max_left Cχ 0))
  have hDiffEnergyψ (p : ℝ × ℝ)
      (hp : 0 < p.1 ∧ p.1 < t / 2 ∧ 0 < p.2 ∧ p.2 < t / 2) :
      ∫⁻ ω, localNegSobolevSq s (D p ω) ψ ∂P ≤ ENNReal.ofReal (4 * Cψ₀) := by
    simpa [D] using lintegral_localNegSobolevSq_sub_le_of_moment
      P F hFpairForMoment ψ hCψ₀ hMomentψ p hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  have hDiffEnergyχ (p : ℝ × ℝ)
      (hp : 0 < p.1 ∧ p.1 < t / 2 ∧ 0 < p.2 ∧ p.2 < t / 2) :
      ∫⁻ ω, localNegSobolevSq s (D p ω) χ ∂P ≤ ENNReal.ofReal (4 * Cχ₀) := by
    simpa [D] using lintegral_localNegSobolevSq_sub_le_of_moment
      P F hFpairForMoment χ hCχ₀ hMomentχ p hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  let cFourier : ℝ≥0∞ := ENNReal.ofReal ((2 * Real.pi)⁻¹ ^ 2)
  let energy (q : ℝ × ℝ) (ξ : Plane) : ℝ≥0∞ :=
    ∫⁻ ω, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-a) *
      ‖localizedFourier (D q ω) χ ξ‖ ^ 2) ∂P
  let energyHalf (q : ℝ × ℝ) (ξ : Plane) : ℝ≥0∞ :=
    ∫⁻ ω, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-s) *
      ‖localizedFourier (D q ω) χ ξ‖ ^ 2) ∂P
  have hEnergyFreqEq (p : ℝ × ℝ)
      (hp : 0 < p.1 ∧ p.1 < t / 2 ∧ 0 < p.2 ∧ p.2 < t / 2) (ξ : Plane) :
      energy p ξ = ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-a)) *
        (∫⁻ ω, ENNReal.ofReal ((D p ω (χ.mulCos ξ)) ^ 2) ∂P +
          ∫⁻ ω, ENNReal.ofReal ((D p ω (χ.mulSin ξ)) ^ 2) ∂P) := by
    exact lintegral_weightedFourier_eq_pairings P (hDpair p hp) a χ ξ
  have hEnergyHalfFreqEq (p : ℝ × ℝ)
      (hp : 0 < p.1 ∧ p.1 < t / 2 ∧ 0 < p.2 ∧ p.2 < t / 2) (ξ : Plane) :
      energyHalf p ξ = ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-s)) *
        (∫⁻ ω, ENNReal.ofReal ((D p ω (χ.mulCos ξ)) ^ 2) ∂P +
          ∫⁻ ω, ENNReal.ofReal ((D p ω (χ.mulSin ξ)) ^ 2) ∂P) := by
    exact lintegral_weightedFourier_eq_pairings P (hDpair p hp) s χ ξ
  have hJoint (p : ℝ × ℝ)
      (hp : 0 < p.1 ∧ p.1 < t / 2 ∧ 0 < p.2 ∧ p.2 < t / 2) :
      AEMeasurable (fun q : Plane × Ω => ENNReal.ofReal
        ((1 + ‖q.1‖ ^ 2) ^ (-a) *
          ‖localizedFourier (D p q.2) χ q.1‖ ^ 2)) (volume.prod P) :=
    aemeasurable_localizedFourierEnergy_uncurry_of_pairings P (hDpair p hp) a χ
  have hEnergyAEM (p : ℝ × ℝ)
      (hp : 0 < p.1 ∧ p.1 < t / 2 ∧ 0 < p.2 ∧ p.2 < t / 2) :
      AEMeasurable (energy p) volume := by
    simpa only [energy, Function.uncurry] using (hJoint p hp).lintegral_prod_right'
  have hEnergyHalfAEM (p : ℝ × ℝ)
      (hp : 0 < p.1 ∧ p.1 < t / 2 ∧ 0 < p.2 ∧ p.2 < t / 2) :
      AEMeasurable (energyHalf p) volume := by
    simpa only [energyHalf, Function.uncurry] using
      (aemeasurable_localizedFourierEnergy_uncurry_of_pairings P (hDpair p hp) s χ).lintegral_prod_right'
  have hEnergySq (p : ℝ × ℝ)
      (hp : 0 < p.1 ∧ p.1 < t / 2 ∧ 0 < p.2 ∧ p.2 < t / 2) :
      ∫⁻ ω, localNegSobolevSq a (D p ω) χ ∂P =
        cFourier * ∫⁻ ξ : Plane, energy p ξ := by
    simpa only [D, cFourier, energy] using
      lintegral_localNegSobolevSq_eq_expectedFourierEnergy P (hDpair p hp) a χ
  have hEnergyHalfSq (p : ℝ × ℝ)
      (hp : 0 < p.1 ∧ p.1 < t / 2 ∧ 0 < p.2 ∧ p.2 < t / 2) :
      ∫⁻ ω, localNegSobolevSq s (D p ω) χ ∂P =
        cFourier * ∫⁻ ξ : Plane, energyHalf p ξ := by
    simpa only [D, cFourier, energyHalf] using
      lintegral_localNegSobolevSq_eq_expectedFourierEnergy P (hDpair p hp) s χ
  have hpointwise (ξ : Plane) : Tendsto (fun p : ℝ × ℝ => energy p ξ) l (𝓝 0) := by
    have hcos := hPairSqLimit (χ.mulCos ξ)
    have hsin := hPairSqLimit (χ.mulSin ξ)
    have hsum := hcos.add hsin
    have hmul : Tendsto (fun p : ℝ × ℝ => ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-a)) *
        (∫⁻ ω, ENNReal.ofReal ((D p ω (χ.mulCos ξ)) ^ 2) ∂P +
          ∫⁻ ω, ENNReal.ofReal ((D p ω (χ.mulSin ξ)) ^ 2) ∂P)) l (𝓝 0) := by
      have hcont := ENNReal.continuous_const_mul (ENNReal.ofReal_ne_top
        (r := (1 + ‖ξ‖ ^ 2) ^ (-a)))
      simpa [Function.comp_def] using hcont.continuousAt.tendsto.comp hsum
    have hEq : (fun p : ℝ × ℝ => energy p ξ) =ᶠ[l]
        (fun p => ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-a)) *
          (∫⁻ ω, ENNReal.ofReal ((D p ω (χ.mulCos ξ)) ^ 2) ∂P +
            ∫⁻ ω, ENNReal.ofReal ((D p ω (χ.mulSin ξ)) ^ 2) ∂P)) := by
      filter_upwards [hpos] with p hp
      exact hEnergyFreqEq p ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩ ξ
    exact hmul.congr' hEq.symm
  have hcompact (R : ℝ) : Tendsto
      (fun p : ℝ × ℝ => ∫⁻ ξ in Metric.closedBall (0 : Plane) R, energy p ξ ∂volume)
      l (𝓝 0) := by
    obtain ⟨Kcos, hKcos, hKcosBound⟩ := exists_uniform_sobolev_bound_mulCos χ s R
    obtain ⟨Ksin, hKsin, hKsinBound⟩ := exists_uniform_sobolev_bound_mulSin χ s R
    let B : ℝ := (4 * Cψ₀) * (Kcos + Ksin)
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hBallMeas : MeasurableSet (Metric.closedBall (0 : Plane) R) :=
      measurableSet_closedBall
    have hBallFinite : volume (Metric.closedBall (0 : Plane) R) < ⊤ :=
      (isCompact_closedBall (0 : Plane) R).measure_lt_top
    have hfin : ∫⁻ ξ, ENNReal.ofReal B ∂(volume.restrict
        (Metric.closedBall (0 : Plane) R)) ≠ ⊤ := by
      rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ]
      simp only [Set.univ_inter]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBallFinite.ne
    have hfreqBound (p : ℝ × ℝ)
        (hp : 0 < p.1 ∧ p.1 < t / 2 ∧ 0 < p.2 ∧ p.2 < t / 2)
        (ξ : Plane) (hξ : ξ ∈ Metric.closedBall (0 : Plane) R) :
        energy p ξ ≤ ENNReal.ofReal B := by
      have hpairCos := lintegral_pairing_sq_le_of_local_energy P (hDpair p hp)
        s ψ (χ.mulCos ξ) (fun x hx => hψ x (tsupport_mul_subset_left hx))
        (hDiffEnergyψ p hp)
      have hpairSin := lintegral_pairing_sq_le_of_local_energy P (hDpair p hp)
        s ψ (χ.mulSin ξ) (fun x hx => hψ x (tsupport_mul_subset_left hx))
        (hDiffEnergyψ p hp)
      have hcos : ∫⁻ ω, ENNReal.ofReal ((D p ω (χ.mulCos ξ)) ^ 2) ∂P ≤
          ENNReal.ofReal (Kcos * (4 * Cψ₀)) := by
        calc
          _ ≤ Analysis.Sobolev.Rellich.sobolevNormSq 2 s
              (fun x => (χ.mulCos ξ x : ℝ)) * ENNReal.ofReal (4 * Cψ₀) := hpairCos
          _ ≤ ENNReal.ofReal Kcos * ENNReal.ofReal (4 * Cψ₀) :=
            mul_le_mul_of_nonneg_right (hKcosBound ξ hξ) bot_le
          _ = ENNReal.ofReal (Kcos * (4 * Cψ₀)) := by
            rw [← ENNReal.ofReal_mul hKcos]
      have hsin' : ∫⁻ ω, ENNReal.ofReal ((D p ω (χ.mulSin ξ)) ^ 2) ∂P ≤
          ENNReal.ofReal (Ksin * (4 * Cψ₀)) := by
        calc
          _ ≤ Analysis.Sobolev.Rellich.sobolevNormSq 2 s
              (fun x => (χ.mulSin ξ x : ℝ)) * ENNReal.ofReal (4 * Cψ₀) := hpairSin
          _ ≤ ENNReal.ofReal Ksin * ENNReal.ofReal (4 * Cψ₀) :=
            mul_le_mul_of_nonneg_right (hKsinBound ξ hξ) bot_le
          _ = ENNReal.ofReal (Ksin * (4 * Cψ₀)) := by
            rw [← ENNReal.ofReal_mul hKsin]
      have hw : (1 + ‖ξ‖ ^ 2) ^ (-a) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos
          (by nlinarith [sq_nonneg ‖ξ‖]) (neg_nonpos.mpr ha.le)
      rw [hEnergyFreqEq p hp ξ]
      calc
        _ ≤ 1 * (∫⁻ ω, ENNReal.ofReal ((D p ω (χ.mulCos ξ)) ^ 2) ∂P +
            ∫⁻ ω, ENNReal.ofReal ((D p ω (χ.mulSin ξ)) ^ 2) ∂P) := by
          apply mul_le_mul_of_nonneg_right _ bot_le
          exact (ENNReal.ofReal_le_ofReal hw).trans_eq (by simp)
        _ ≤ ENNReal.ofReal (Kcos * (4 * Cψ₀)) +
            ENNReal.ofReal (Ksin * (4 * Cψ₀)) := by
          simp only [one_mul]
          exact add_le_add hcos hsin'
        _ = ENNReal.ofReal B := by
          rw [← ENNReal.ofReal_add (mul_nonneg hKcos (by positivity))
            (mul_nonneg hKsin (by positivity))]
          congr 1
          dsimp [B]
          ring
    have hmeas : ∀ᶠ p in l, AEMeasurable (energy p)
        (volume.restrict (Metric.closedBall (0 : Plane) R)) := by
      filter_upwards [hpos] with p hp
      exact (hEnergyAEM p ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩).restrict
    have hbound : ∀ᶠ p in l, ∀ᵐ ξ ∂volume.restrict
        (Metric.closedBall (0 : Plane) R), energy p ξ ≤ ENNReal.ofReal B := by
      filter_upwards [hpos] with p hp
      filter_upwards [ae_restrict_mem hBallMeas] with ξ hξ
      exact hfreqBound p ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩ ξ hξ
    have hlim : ∀ᵐ ξ ∂volume.restrict (Metric.closedBall (0 : Plane) R),
        Tendsto (fun p : ℝ × ℝ => energy p ξ) l (𝓝 0) :=
      Filter.Eventually.of_forall hpointwise
    have hdc := tendsto_lintegral_filter_of_dominated_convergence'
      (μ := volume.restrict (Metric.closedBall (0 : Plane) R))
      (F := fun p ξ => energy p ξ) (f := fun _ : Plane => (0 : ℝ≥0∞))
      (bound := fun _ => ENNReal.ofReal B) hmeas hbound hfin hlim
    simpa only [lintegral_zero] using hdc
  let Eχ : ℝ := 4 * Cχ₀
  have hEχ : 0 ≤ Eχ := by dsimp [Eχ]; positivity
  have hq : Tendsto (fun R : ℝ => (1 + R ^ 2) ^ (-s)) atTop (𝓝 0) := by
    have hbase : Tendsto (fun R : ℝ => 1 + R ^ 2) atTop atTop := by
      simpa [add_comm] using tendsto_atTop_add_const_right atTop (1 : ℝ)
        (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))
    exact (tendsto_rpow_neg_atTop hspos).comp hbase
  have htailConstant : Tendsto
      (fun R : ℝ => ENNReal.ofReal ((1 + R ^ 2) ^ (-s) * Eχ)) atTop (𝓝 0) := by
    have hmul : Tendsto (fun R : ℝ => (1 + R ^ 2) ^ (-s) * Eχ) atTop (𝓝 0) := by
      simpa using hq.mul_const Eχ
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hmul
  have hweightTail (R : ℝ) (hR : 0 ≤ R) (ξ : Plane)
      (hξ : ξ ∉ Metric.closedBall (0 : Plane) R) :
      (1 + ‖ξ‖ ^ 2) ^ (-a) ≤
        (1 + R ^ 2) ^ (-s) * (1 + ‖ξ‖ ^ 2) ^ (-s) := by
    have hnorm : R < ‖ξ‖ := by
      have hx := hξ
      simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hx
      exact hx
    have hb : 1 + R ^ 2 ≤ 1 + ‖ξ‖ ^ 2 := by nlinarith [norm_nonneg ξ]
    have hratio : (1 + ‖ξ‖ ^ 2) ^ (-s) ≤ (1 + R ^ 2) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hb (neg_nonpos.mpr hspos.le)
    have hfactor : (1 + ‖ξ‖ ^ 2) ^ (-a) =
        (1 + ‖ξ‖ ^ 2) ^ (-s) * (1 + ‖ξ‖ ^ 2) ^ (-s) := by
      calc
        _ = (1 + ‖ξ‖ ^ 2) ^ ((-s) + (-s)) := by congr 1; dsimp [s]; ring
        _ = _ := Real.rpow_add (by positivity) _ _
    rw [hfactor]
    exact mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg (by positivity) _)
  have htail (R : ℝ) (hR : 0 ≤ R)
      (p : ℝ × ℝ) (hp : 0 < p.1 ∧ p.1 < t / 2 ∧ 0 < p.2 ∧ p.2 < t / 2) :
      cFourier * ∫⁻ ξ in (Metric.closedBall (0 : Plane) R)ᶜ, energy p ξ ∂volume ≤
        ENNReal.ofReal ((1 + R ^ 2) ^ (-s) * Eχ) := by
    have hqpos : 0 ≤ (1 + R ^ 2) ^ (-s) := by positivity
    have hfreq (ξ : Plane) (hξ : ξ ∉ Metric.closedBall (0 : Plane) R) :
        energy p ξ ≤ ENNReal.ofReal ((1 + R ^ 2) ^ (-s)) * energyHalf p ξ := by
      let J : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal ((D p ω (χ.mulCos ξ)) ^ 2) ∂P +
        ∫⁻ ω, ENNReal.ofReal ((D p ω (χ.mulSin ξ)) ^ 2) ∂P
      have hweight := hweightTail R hR ξ hξ
      have hweightENN : ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-a)) ≤
          ENNReal.ofReal ((1 + R ^ 2) ^ (-s) * (1 + ‖ξ‖ ^ 2) ^ (-s)) :=
        ENNReal.ofReal_le_ofReal hweight
      calc
        energy p ξ = ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-a)) * J := by
          simpa [J] using hEnergyFreqEq p hp ξ
        _ ≤ ENNReal.ofReal ((1 + R ^ 2) ^ (-s) * (1 + ‖ξ‖ ^ 2) ^ (-s)) * J :=
          mul_le_mul_of_nonneg_right hweightENN bot_le
        _ = ENNReal.ofReal ((1 + R ^ 2) ^ (-s)) *
            (ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ (-s)) * J) := by
          rw [ENNReal.ofReal_mul hqpos]
          ac_rfl
        _ = ENNReal.ofReal ((1 + R ^ 2) ^ (-s)) * energyHalf p ξ := by
          rw [hEnergyHalfFreqEq p hp ξ]
    have htailFreq : ∫⁻ ξ in (Metric.closedBall (0 : Plane) R)ᶜ, energy p ξ ∂volume ≤
        ENNReal.ofReal ((1 + R ^ 2) ^ (-s)) *
          ∫⁻ ξ in (Metric.closedBall (0 : Plane) R)ᶜ, energyHalf p ξ ∂volume := by
      calc
        _ ≤ ∫⁻ ξ in (Metric.closedBall (0 : Plane) R)ᶜ,
            ENNReal.ofReal ((1 + R ^ 2) ^ (-s)) * energyHalf p ξ ∂volume := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem (Metric.isClosed_closedBall.measurableSet.compl)] with ξ hξ
          exact hfreq ξ hξ
        _ = ENNReal.ofReal ((1 + R ^ 2) ^ (-s)) *
            ∫⁻ ξ in (Metric.closedBall (0 : Plane) R)ᶜ, energyHalf p ξ ∂volume := by
          rw [lintegral_const_mul'' _ (hEnergyHalfAEM p hp).restrict]
    have htailAll : ∫⁻ ξ in (Metric.closedBall (0 : Plane) R)ᶜ, energyHalf p ξ ∂volume ≤
        ∫⁻ ξ : Plane, energyHalf p ξ :=
      by
        simpa using (lintegral_mono_set (μ := volume)
          (s := (Metric.closedBall (0 : Plane) R)ᶜ) (t := Set.univ)
          (f := fun ξ : Plane => energyHalf p ξ) (Set.subset_univ _))
    calc
      _ ≤ cFourier * (ENNReal.ofReal ((1 + R ^ 2) ^ (-s)) *
          ∫⁻ ξ : Plane, energyHalf p ξ) := by
        exact mul_le_mul_of_nonneg_left (htailFreq.trans
          (mul_le_mul_of_nonneg_left htailAll bot_le)) bot_le
      _ = ENNReal.ofReal ((1 + R ^ 2) ^ (-s)) *
          ∫⁻ ω, localNegSobolevSq s (D p ω) χ ∂P := by
        rw [hEnergyHalfSq p hp]
        ac_rfl
      _ ≤ ENNReal.ofReal ((1 + R ^ 2) ^ (-s)) * ENNReal.ofReal Eχ :=
        mul_le_mul_of_nonneg_left (hDiffEnergyχ p hp) bot_le
      _ = ENNReal.ofReal ((1 + R ^ 2) ^ (-s) * Eχ) := by
        rw [ENNReal.ofReal_mul hqpos]
  have henergyTendsto : Tendsto
      (fun p : ℝ × ℝ => ∫⁻ ω, localNegSobolevSq a (D p ω) χ ∂P) l (𝓝 0) := by
    apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    by_cases hεtop : ε = ∞
    · filter_upwards [] with p
      rw [hεtop]
      exact le_top
    ·
      have hhalf : (0 : ℝ≥0∞) < ε / 2 :=
        ENNReal.div_pos (ne_of_gt hε) (by norm_num)
      have hhalfNeTop : ε / 2 ≠ ∞ :=
        ENNReal.div_ne_top hεtop (by norm_num)
      have htailSmall : ∀ᶠ R : ℝ in atTop,
          ENNReal.ofReal ((1 + R ^ 2) ^ (-s) * Eχ) < ε / 2 :=
        htailConstant.eventually (Iio_mem_nhds hhalf)
      have hRpos : ∀ᶠ R : ℝ in atTop, 0 ≤ R := eventually_ge_atTop 0
      obtain ⟨R, hRsmall, hRnonneg⟩ := (htailSmall.and hRpos).exists
      have hcompScaled : Tendsto
          (fun p : ℝ × ℝ => cFourier *
            ∫⁻ ξ in Metric.closedBall (0 : Plane) R, energy p ξ ∂volume) l (𝓝 0) := by
        have hcont := ENNReal.continuous_const_mul
          (ENNReal.ofReal_ne_top (r := (2 * Real.pi)⁻¹ ^ 2))
        simpa [cFourier, Function.comp_def] using hcont.continuousAt.tendsto.comp (hcompact R)
      have hcompSmall : ∀ᶠ p in l, cFourier *
          ∫⁻ ξ in Metric.closedBall (0 : Plane) R, energy p ξ ∂volume < ε / 2 :=
        hcompScaled.eventually (Iio_mem_nhds hhalf)
      filter_upwards [hpos, hcompSmall] with p hp hball
      apply le_of_lt
      have hsplit : ∫⁻ ξ : Plane, energy p ξ =
          ∫⁻ ξ in Metric.closedBall (0 : Plane) R, energy p ξ ∂volume +
            ∫⁻ ξ in (Metric.closedBall (0 : Plane) R)ᶜ, energy p ξ ∂volume :=
        (lintegral_add_compl (energy p) measurableSet_closedBall).symm
      have htailBound := htail R hRnonneg p ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩
      have htailSmall' : cFourier *
          ∫⁻ ξ in (Metric.closedBall (0 : Plane) R)ᶜ, energy p ξ ∂volume < ε / 2 :=
        htailBound.trans_lt hRsmall
      calc
        _ = cFourier * (∫⁻ ξ in Metric.closedBall (0 : Plane) R, energy p ξ ∂volume +
            ∫⁻ ξ in (Metric.closedBall (0 : Plane) R)ᶜ, energy p ξ ∂volume) := by
          rw [hEnergySq p ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩, ← hsplit]
        _ = cFourier * ∫⁻ ξ in Metric.closedBall (0 : Plane) R, energy p ξ ∂volume +
            cFourier * ∫⁻ ξ in (Metric.closedBall (0 : Plane) R)ᶜ, energy p ξ ∂volume := by
          rw [mul_add]
        _ ≤ cFourier * ∫⁻ ξ in Metric.closedBall (0 : Plane) R, energy p ξ ∂volume + ε / 2 :=
          add_le_add le_rfl htailSmall'.le
        _ < ε / 2 + ε / 2 :=
          ENNReal.add_lt_add_right hhalfNeTop hball
        _ = ε := ENNReal.add_halves ε
  simpa only [D, F, l] using henergyTendsto

end Critical2DKPZ.LocalSobolev

end
