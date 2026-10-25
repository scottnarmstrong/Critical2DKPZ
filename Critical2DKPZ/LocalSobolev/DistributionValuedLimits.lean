/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.Inputs
public import Critical2DKPZ.LocalSobolev.InitialNegSobolev
public import Critical2DKPZ.LocalSobolev.LatticeMoment
public import Critical2DKPZ.LocalSobolev.NegSobolevLimit
public import Critical2DKPZ.LocalSobolev.MeasurableFieldVersions
public import Critical2DKPZ.Definitions.ToLocNegSobolevTuple
public import Critical2DKPZ.Analysis.Sobolev.ExpectedField
public import Critical2DKPZ.Analysis.Sobolev.FunctionBound
public import Critical2DKPZ.Analysis.Sobolev.LocNegSobolevCompactness
public import Critical2DKPZ.LocalSobolev.TupleConvergence
public import Critical2DKPZ.SHF.Moments.PairingFubini
import Critical2DKPZ.JointConvergence.LogHeatFieldMeasurability
import Critical2DKPZ.JointConvergence.KPZRegularizedReversal
import Critical2DKPZ.Smoothing.UnitHorizonBounds

/-! Expected local Sobolev Cauchy estimates yield measurable random distribution limits. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory TopologicalSpace
open scoped BoundedContinuousFunction ENNReal Topology
open Critical2DKPZ.Analysis.Sobolev.Rellich

namespace Critical2DKPZ.LocalSobolev

private theorem locallyIntegrable_of_aestronglyMeasurable_ae_bound {f : Plane → ℝ} {M : ℝ}
    (hf : AEStronglyMeasurable f volume) (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ M) :
    LocallyIntegrable f volume := by
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

set_option linter.style.haveILetI false in
private theorem locallyFinite_of_closedBall_mass (μ : Measure (Plane × Plane))
    (hμ : ∀ n : ℕ, μ (Metric.closedBall (0 : Plane × Plane) (n : ℝ)) < ∞) :
    IsLocallyFiniteMeasure μ := by
  have hfc : IsFiniteMeasureOnCompacts μ := by
    refine ⟨?_⟩
    intro K hK
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : Plane × Plane)
    obtain ⟨n, hn⟩ := exists_nat_gt r
    calc
      μ K ≤ μ (Metric.closedBall (0 : Plane × Plane) r) := measure_mono hr
      _ ≤ μ (Metric.closedBall (0 : Plane × Plane) (n : ℝ)) :=
        measure_mono (Metric.closedBall_subset_closedBall (le_of_lt hn))
      _ < ∞ := hμ n
  letI : IsFiniteMeasureOnCompacts μ := hfc
  infer_instance

def kpzRegularizedDistribution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (t δ : ℝ) (h₀ : Plane →ᵇ ℝ) (ω : Ω) : Distr :=
  Distribution.ofFun ⊤ (fun x => kpzRegularized P Z t δ h₀ x ω) volume ⊤

private theorem exists_kpzRegularized_distributionVersionFamily
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ϑ : ℝ) (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) {t : ℝ} (ht : 0 < t) (h₀ : Plane →ᵇ ℝ) :
    ∃ F : ℝ → Ω → Distr,
      (∀ δ φ, Measurable[shfSigma Z] fun ω => F δ ω φ) ∧
      ∀ δ, 0 < δ → δ < t → F δ =ᵐ[P] kpzRegularizedDistribution P Z t δ h₀ := by
  classical
  let F : ℝ → Ω → Distr := fun δ =>
    if hδ : 0 < δ ∧ δ < t then
      Classical.choose (exists_shfSigma_measurable_kpzRegularized_distribution
        ϑ P Z hZ (t := t) (δ := δ) ht hδ.1 hδ.2 h₀)
    else fun _ => 0
  refine ⟨F, ?_, ?_⟩
  · intro δ φ
    by_cases hδ : 0 < δ ∧ δ < t
    · simpa [F, hδ] using
        (Classical.choose_spec (exists_shfSigma_measurable_kpzRegularized_distribution
          ϑ P Z hZ (t := t) (δ := δ) ht hδ.1 hδ.2 h₀)).1 φ
    · simp [F, hδ]
  · intro δ hδ hδt
    change F δ =ᵐ[P] (fun ω => Distribution.ofFun ⊤
      (fun x => kpzRegularized P Z t δ h₀ x ω) volume ⊤)
    simpa [F, hδ, hδt, kpzRegularizedDistribution] using
      (Classical.choose_spec (exists_shfSigma_measurable_kpzRegularized_distribution
        ϑ P Z hZ (t := t) (δ := δ) ht hδ hδt h₀)).2

/-- The local Sobolev Cauchy estimate gives a measurable random distribution limit for the regularized field. -/
theorem exists_kpzRegularized_localSobolev_limit_of
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ϑ : ℝ) (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z)
    {t : ℝ} (ht : 0 < t) (h₀ : Plane →ᵇ ℝ)
    (hCauchy : ∀ {a : ℝ}, 0 < a → ∀ χ : TestFn,
      Tendsto (fun p : ℝ × ℝ => ∫⁻ ω, localNegSobolevSq a
          (kpzRegularizedDistribution P Z t p.1 h₀ ω -
            kpzRegularizedDistribution P Z t p.2 h₀ ω) χ ∂P)
        (nhdsWithin 0 (Set.Ioi 0) ×ˢ nhdsWithin 0 (Set.Ioi 0)) (𝓝 0)) :
    ∃ H : Ω → Distr,
      (∀ φ : TestFn, Measurable[shfSigma Z] fun ω => H ω φ) ∧
      ∀ a : ℝ, 0 < a → ∀ χ : TestFn,
        Tendsto (fun δ => ∫⁻ ω, localNegSobolevSq a
            (kpzRegularizedDistribution P Z t δ h₀ ω - H ω) χ ∂P)
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  obtain ⟨F, hFmeas, hFeq⟩ :=
    exists_kpzRegularized_distributionVersionFamily P ϑ Z hZ ht h₀
  have hSigma : shfSigma Z ≤ (inferInstance : MeasurableSpace Ω) := by
    dsimp [shfSigma]
    apply iSup_le
    intro s
    apply iSup_le
    intro u
    apply iSup_le
    intro hsu
    exact (hZ.1 s u hsu.1 hsu.2).comap_le
  have hδsmall : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < δ ∧ δ < t := by
    have hδpos : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < δ := by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact hδ
    have hnhds : ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ), δ < t :=
      Iio_mem_nhds ht
    exact hδpos.and (hnhds.filter_mono nhdsWithin_le_nhds)
  have hpSmall : ∀ᶠ p : ℝ × ℝ in
      nhdsWithin 0 (Set.Ioi 0) ×ˢ nhdsWithin 0 (Set.Ioi 0),
      0 < p.1 ∧ p.1 < t ∧ 0 < p.2 ∧ p.2 < t := by
    apply Filter.eventually_prod_iff.mpr
    refine ⟨fun δ => 0 < δ ∧ δ < t, hδsmall, fun δ => 0 < δ ∧ δ < t, hδsmall, ?_⟩
    intro δ hδ δ' hδ'
    exact ⟨hδ.1, hδ.2, hδ'.1, hδ'.2⟩
  have hFCauchy : ∀ a : ℝ, 0 < a → ∀ χ : TestFn,
      Tendsto (fun p : ℝ × ℝ => ∫⁻ ω, localNegSobolevSq a
          (F p.1 ω - F p.2 ω) χ ∂P)
        (nhdsWithin 0 (Set.Ioi 0) ×ˢ nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    intro a ha χ
    have heq : (fun p : ℝ × ℝ => ∫⁻ ω, localNegSobolevSq a
          (F p.1 ω - F p.2 ω) χ ∂P) =ᶠ[
          nhdsWithin 0 (Set.Ioi 0) ×ˢ nhdsWithin 0 (Set.Ioi 0)]
        (fun p : ℝ × ℝ => ∫⁻ ω, localNegSobolevSq a
          (kpzRegularizedDistribution P Z t p.1 h₀ ω -
            kpzRegularizedDistribution P Z t p.2 h₀ ω) χ ∂P) := by
      filter_upwards [hpSmall] with p hp
      have hdist : ∀ᵐ ω ∂P, F p.1 ω - F p.2 ω =
          kpzRegularizedDistribution P Z t p.1 h₀ ω -
            kpzRegularizedDistribution P Z t p.2 h₀ ω := by
        filter_upwards [hFeq p.1 hp.1 hp.2.1, hFeq p.2 hp.2.2.1 hp.2.2.2] with ω h₁ h₂
        simp [h₁, h₂]
      exact lintegral_congr_ae (hdist.mono fun ω hω => by simp [hω])
    exact Tendsto.congr' heq.symm (hCauchy ha χ)
  obtain ⟨H, hHmeas, hHenergy⟩ :=
    exists_negSobolev_limit P (shfSigma Z) hSigma F (fun δ _ φ => hFmeas δ φ) hFCauchy
  refine ⟨H, hHmeas, ?_⟩
  intro a ha χ
  have heq : (fun δ : ℝ => ∫⁻ ω, localNegSobolevSq a
        (kpzRegularizedDistribution P Z t δ h₀ ω - H ω) χ ∂P) =ᶠ[
        nhdsWithin 0 (Set.Ioi 0)]
      (fun δ : ℝ => ∫⁻ ω, localNegSobolevSq a (F δ ω - H ω) χ ∂P) := by
    filter_upwards [hδsmall] with δ hδ
    have hdist : ∀ᵐ ω ∂P, F δ ω - H ω =
        kpzRegularizedDistribution P Z t δ h₀ ω - H ω := by
      filter_upwards [hFeq δ hδ.1 hδ.2] with ω hω
      simp [hω]
    exact lintegral_congr_ae (hdist.mono fun ω hω => by simp [hω])
  exact Tendsto.congr' heq.symm (hHenergy a ha χ)

/-- The limits from `exists_kpzRegularized_localSobolev_limit_of` form a measurable family indexed by positive time and bounded continuous initial profiles. -/
theorem exists_kpzRegularized_limitFamily_of
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ϑ : ℝ) (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hCauchy : ∀ {t : ℝ}, 0 < t → ∀ (h₀ : Plane →ᵇ ℝ), ∀ {a : ℝ}, 0 < a →
      ∀ χ : TestFn, Tendsto (fun p : ℝ × ℝ => ∫⁻ ω, localNegSobolevSq a
        (kpzRegularizedDistribution P Z t p.1 h₀ ω -
          kpzRegularizedDistribution P Z t p.2 h₀ ω) χ ∂P)
        (nhdsWithin 0 (Set.Ioi 0) ×ˢ nhdsWithin 0 (Set.Ioi 0)) (𝓝 0)) :
    ∃ H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr,
      (∀ t, 0 < t → ∀ (h₀ : Plane →ᵇ ℝ), ∀ φ : TestFn,
        Measurable[shfSigma Z] (fun ω => H t h₀ ω φ)) ∧
      (∀ t, 0 < t → ∀ (h₀ : Plane →ᵇ ℝ), ∀ a, 0 < a → ∀ χ : TestFn,
        Tendsto (fun δ => ∫⁻ ω, localNegSobolevSq a
          (kpzRegularizedDistribution P Z t δ h₀ ω - H t h₀ ω) χ ∂P)
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0)) := by
  classical
  let H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr := fun t h₀ =>
    if ht : 0 < t then
      Classical.choose (exists_kpzRegularized_localSobolev_limit_of P ϑ Z hZ ht h₀
        (hCauchy ht h₀))
    else fun _ => 0
  refine ⟨H, ?_, ?_⟩
  · intro t ht h₀ φ
    dsimp [H]
    rw [dite_eq_left ht]
    exact (Classical.choose_spec (exists_kpzRegularized_localSobolev_limit_of P ϑ Z hZ ht h₀
      (hCauchy ht h₀))).1 φ
  · intro t ht h₀ a ha χ
    dsimp [H]
    rw [dite_eq_left ht]
    exact (Classical.choose_spec (exists_kpzRegularized_localSobolev_limit_of P ϑ Z hZ ht h₀
      (hCauchy ht h₀))).2 a ha χ

private theorem tendstoInMeasure_of_expected_localNegSobolevSq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type*} {l : Filter ι} (F : ι → Ω → Distr) (H : Ω → Distr) (a : ℝ)
    (hFmeas : ∀ i (φ : TestFn), Measurable fun ω => F i ω φ)
    (hHmeas : ∀ φ : TestFn, Measurable fun ω => H ω φ)
    (henergy : ∀ χ : TestFn, Tendsto (fun i => ∫⁻ ω,
      localNegSobolevSq a (F i ω - H ω) χ ∂P) l (𝓝 0))
    (φ : TestFn) :
    TendstoInMeasure P (fun i ω => F i ω φ) l (fun ω => H ω φ) := by
  obtain ⟨R, hR⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : Plane)
  obtain ⟨k, hk⟩ := exists_nat_gt R
  let D : Set Plane := compactnessDomain k
  have hkRadius : R < (k : ℝ) + 1 := by exact lt_trans hk (by linarith)
  have hφD : IsTestFn D (fun x => (φ x : ℝ)) := by
    refine ⟨φ.contDiff, φ.hasCompactSupport, ?_⟩
    intro x hx
    change x ∈ Metric.ball 0 ((k : ℝ) + 1)
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (hR hx) hkRadius
  have hχ : ∀ x ∈ D, localizer k x = 1 := by
    intro x hx
    apply localizer_eq_one_of_mem_closedBall
    change x ∈ Metric.ball 0 ((k : ℝ) + 1) at hx
    rw [Metric.mem_ball] at hx
    exact Metric.mem_closedBall.mpr hx.le
  obtain ⟨B, hB, hSob⟩ := exists_test_sobolev_norm_bound a φ
  let E : ι → Ω → ℝ≥0∞ := fun i ω =>
    localNegSobolevSq a (F i ω - H ω) (localizer k)
  have hEmeas (i : ι) : Measurable (E i) := by
    apply measurable_localNegSobolevSq
    intro ψ
    exact (hFmeas i ψ).sub (hHmeas ψ)
  have hErootMeas (i : ι) : Measurable (fun ω => E i ω ^ (1 / 2 : ℝ)) := by
    exact ENNReal.continuous_rpow_const.measurable.comp (hEmeas i)
  have hErootBound (i : ι) : ∫⁻ ω, E i ω ^ (1 / 2 : ℝ) ∂P ≤
      (∫⁻ ω, E i ω ∂P) ^ (1 / 2 : ℝ) :=
    lintegral_rpow_half_le_rpow_lintegral P (E i) (hEmeas i)
  have hEroot : Tendsto (fun i => ∫⁻ ω, E i ω ^ (1 / 2 : ℝ) ∂P) l (𝓝 0) := by
    have hpow : Tendsto (fun i => (∫⁻ ω, E i ω ∂P) ^ (1 / 2 : ℝ)) l (𝓝 0) := by
      have hcomp := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto
        (0 : ℝ≥0∞) |>.comp
        (henergy (localizer k))
      have hcomp0 : Tendsto
          ((fun x : ℝ≥0∞ => x ^ (1 / 2 : ℝ)) ∘
            fun i => ∫⁻ ω, E i ω ∂P) l (𝓝 0) := by
        simpa only [ENNReal.zero_rpow_of_pos (by norm_num : 0 < (1 / 2 : ℝ))] using hcomp
      have heq : (fun i => (∫⁻ ω, E i ω ∂P) ^ (1 / 2 : ℝ)) =ᶠ[l]
          ((fun x : ℝ≥0∞ => x ^ (1 / 2 : ℝ)) ∘
            fun i => ∫⁻ ω, E i ω ∂P) := by
        filter_upwards [] with i
        rfl
      exact Tendsto.congr' heq.symm hcomp0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hpow
      (fun i => by positivity) ?_
    exact fun i => hErootBound i
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  let c : ℝ≥0∞ := ENNReal.ofReal (ε / B)
  have hcpos : 0 < c := by
    dsimp [c]
    exact ENNReal.ofReal_pos.mpr (div_pos hε hB)
  have hctop : c ≠ ⊤ := by dsimp [c]; exact ENNReal.ofReal_ne_top
  have hBenn : ENNReal.ofReal B ≠ 0 := (ENNReal.ofReal_pos.mpr hB).ne'
  have hBtop : ENNReal.ofReal B ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpairBound (i : ι) (ω : Ω) :
      ENNReal.ofReal |(F i ω - H ω) φ| ≤
        ENNReal.ofReal B * (E i ω ^ (1 / 2 : ℝ)) := by
    let U : Distr := F i ω - H ω
    have hsmul : ∀ (r : ℝ) f, IsTestFn D f →
        distributionFunctional U (fun x => r * f x) =
          r * distributionFunctional U f := by
      intro r f hf
      exact distributionFunctional_smul U
        ⟨hf.1, hf.2.1, Set.subset_univ _⟩ r
    have hdual := distributionFunctional_negSobolevNorm_le_localEnergy
      U (localizer k) a hχ
    have happly := abs_apply_le_negSobolevNorm (D := D) a B hB
      (distributionFunctional U) hsmul hφD hSob
    have heval : distributionFunctional U (fun x => (φ x : ℝ)) = U φ := by
      rw [distributionFunctional_apply U hφD]
      rfl
    calc
      _ = ENNReal.ofReal |distributionFunctional U (fun x => (φ x : ℝ))| := by
        rw [heval]
      _ ≤ ENNReal.ofReal B * negSobolevNorm 2 a D (distributionFunctional U) := happly
      _ ≤ ENNReal.ofReal B * (E i ω ^ (1 / 2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa [E, Critical2DKPZ.localNegSobolevENorm_eq_rpow] using hdual
  have hthreshold (i : ι) (ω : Ω)
      (hω : ε ≤ ‖F i ω φ - H ω φ‖) : c ≤ E i ω ^ (1 / 2 : ℝ) := by
    have hεabs : ε ≤ |(F i ω - H ω) φ| := by simpa [Real.norm_eq_abs] using hω
    have hle := (ENNReal.ofReal_le_ofReal hεabs).trans (hpairBound i ω)
    have hmul : ENNReal.ofReal ε = c * ENNReal.ofReal B := by
      dsimp [c]
      calc
        ENNReal.ofReal ε = ENNReal.ofReal ((ε / B) * B) := by
          congr 1
          field_simp
        _ = ENNReal.ofReal (ε / B) * ENNReal.ofReal B :=
          ENNReal.ofReal_mul (div_nonneg hε.le hB.le)
    rw [hmul, mul_comm c] at hle
    exact (ENNReal.mul_le_mul_iff_right hBenn hBtop).mp hle
  have hq : Tendsto (fun i => (∫⁻ ω, E i ω ^ (1 / 2 : ℝ) ∂P).toReal /
      c.toReal) l (𝓝 0) := by
    have hrootReal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hEroot
    simpa using hrootReal.div_const c.toReal
  let qfun : ι → ℝ := fun i =>
    if hfinite : ∫⁻ ω, E i ω ^ (1 / 2 : ℝ) ∂P ≠ ⊤ then
      (∫⁻ ω, E i ω ^ (1 / 2 : ℝ) ∂P).toReal / c.toReal
    else 1
  have hrootSmall : ∀ᶠ i : ι in l, ∫⁻ ω, E i ω ^ (1 / 2 : ℝ) ∂P < 1 :=
    hEroot.eventually (Iio_mem_nhds (by norm_num))
  have hqeq : qfun =ᶠ[l] fun i =>
      (∫⁻ ω, E i ω ^ (1 / 2 : ℝ) ∂P).toReal / c.toReal := by
    filter_upwards [hrootSmall] with i hi
    have hfinite : ∫⁻ ω, E i ω ^ (1 / 2 : ℝ) ∂P ≠ ⊤ :=
      ne_of_lt (lt_trans hi ENNReal.one_lt_top)
    change (if h : ∫⁻ ω, E i ω ^ (1 / 2 : ℝ) ∂P ≠ ⊤ then
      (∫⁻ ω, E i ω ^ (1 / 2 : ℝ) ∂P).toReal / c.toReal else 1) = _
    rw [dite_eq_left hfinite]
  have hqfun : Tendsto qfun l (𝓝 0) := Tendsto.congr' hqeq.symm hq
  have hmeasure (i : ι) : P.real {ω | ε ≤ ‖F i ω φ - H ω φ‖} ≤ qfun i := by
    have hmarkov := meas_ge_le_lintegral_div (μ := P) (hErootMeas i).aemeasurable
      (ne_of_gt hcpos) hctop
    have hsubset : {ω | ε ≤ ‖F i ω φ - H ω φ‖} ⊆
        {ω | c ≤ E i ω ^ (1 / 2 : ℝ)} := by
      intro ω hω
      exact hthreshold i ω hω
    by_cases hfinite : ∫⁻ ω, E i ω ^ (1 / 2 : ℝ) ∂P ≠ ⊤
    · have hquotientTop :
          (∫⁻ ω, E i ω ^ (1 / 2 : ℝ) ∂P) / c ≠ ⊤ :=
        ENNReal.div_ne_top hfinite (ne_of_gt hcpos)
      rw [measureReal_def]
      calc
        (P {ω | ε ≤ ‖F i ω φ - H ω φ‖}).toReal ≤
            ((∫⁻ ω, E i ω ^ (1 / 2 : ℝ) ∂P) / c).toReal :=
          ENNReal.toReal_mono hquotientTop ((measure_mono hsubset).trans hmarkov)
        _ = (∫⁻ ω, E i ω ^ (1 / 2 : ℝ) ∂P).toReal / c.toReal := by
          rw [ENNReal.toReal_div]
        _ = qfun i := by
          change _ = (if h : ∫⁻ ω, E i ω ^ (1 / 2 : ℝ) ∂P ≠ ⊤ then
            (∫⁻ ω, E i ω ^ (1 / 2 : ℝ) ∂P).toReal / c.toReal else 1)
          rw [dite_eq_left hfinite]
    · have hqone : qfun i = 1 := by
        change (if h : ∫⁻ ω, E i ω ^ (1 / 2 : ℝ) ∂P ≠ ⊤ then
          (∫⁻ ω, E i ω ^ (1 / 2 : ℝ) ∂P).toReal / c.toReal else 1) = 1
        rw [dite_eq_right hfinite]
      rw [hqone, measureReal_def]
      calc
        (P {ω | ε ≤ ‖F i ω φ - H ω φ‖}).toReal ≤ (P Set.univ).toReal :=
          ENNReal.toReal_mono (by simp)
            (measure_mono (Set.subset_univ {ω | ε ≤ ‖F i ω φ - H ω φ‖}))
        _ = 1 := by simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hqfun
    (fun i => by positivity) (fun i => hmeasure i)

private theorem tendsto_measure_lt_of_lintegral_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {ι : Type*} {l : Filter ι} (E : ι → Ω → ℝ≥0∞)
    (hEmeas : ∀ i, Measurable (E i))
    (hE : Tendsto (fun i => ∫⁻ ω, E i ω ∂P) l (𝓝 0))
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    Tendsto (fun i => P {ω | ε < E i ω}) l (𝓝 0) := by
  by_cases hεtop : ε = ⊤
  · subst ε
    have heq : (fun i => P {ω | (⊤ : ℝ≥0∞) < E i ω}) = fun _ => 0 := by
      funext i
      simp
    rw [heq]
    exact tendsto_const_nhds
  have hquot : Tendsto (fun i => (∫⁻ ω, E i ω ∂P) / ε) l (𝓝 0) := by
    apply ENNReal.tendsto_nhds_zero.mpr
    intro η hη
    have hsmall := (ENNReal.tendsto_nhds_zero.mp hE) (η * ε)
      (ENNReal.mul_pos hη.ne' hε.ne')
    filter_upwards [hsmall] with i hi
    rw [ENNReal.div_le_iff_le_mul (Or.inl hε.ne') (Or.inl hεtop)]
    simpa [mul_comm] using hi
  have hbound (i : ι) : P {ω | ε < E i ω} ≤
      (∫⁻ ω, E i ω ∂P) / ε := by
    have hmarkov := meas_ge_le_lintegral_div (μ := P) (f := E i)
      (hEmeas i).aemeasurable
      hε.ne' hεtop
    exact (measure_mono (fun ω hω => by
      change ε < E i ω at hω
      exact hω.le)).trans hmarkov
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hquot
    (fun _ => by positivity) hbound

/-- For every admissible smoothing width, the regularized field with bounded continuous initial data has locally integrable spatial sections almost surely. -/
theorem kpzRegularized_locallyIntegrable_ae_of_initial
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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
    exact locallyIntegrable_of_aestronglyMeasurable_ae_bound hωmeas hωbound'
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
  exact ((hω0.add hωD).congr hsum)

/-- The local Sobolev limits form a measurable critical KPZ process. -/
theorem exists_kpzRegularized_criticalProcess_of
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ϑ : ℝ) (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) (hsym : ShfSymmetriesAt ϑ P Z)
    (hCauchy : ∀ {t : ℝ}, 0 < t → ∀ (h₀ : Plane →ᵇ ℝ), ∀ {a : ℝ}, 0 < a →
      ∀ χ : TestFn, Tendsto (fun p : ℝ × ℝ => ∫⁻ ω, localNegSobolevSq a
        (kpzRegularizedDistribution P Z t p.1 h₀ ω -
          kpzRegularizedDistribution P Z t p.2 h₀ ω) χ ∂P)
        (nhdsWithin 0 (Set.Ioi 0) ×ˢ nhdsWithin 0 (Set.Ioi 0)) (𝓝 0)) :
    ∃ H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr,
      IsCriticalKPZ P Z H ∧
      (∀ t, 0 < t → ∀ (h₀ : Plane →ᵇ ℝ) (φ : TestFn),
        Measurable[shfSigma Z] (fun ω => H t h₀ ω φ)) ∧
      (∀ t δ, 0 < δ → δ < t → ∀ h₀ : Plane →ᵇ ℝ, ∀ᵐ ω ∂P,
        LocallyIntegrable (fun x => kpzRegularized P Z t δ h₀ x ω)) ∧
      (∀ t, 0 < t → ∀ (h₀ : Plane →ᵇ ℝ) (a : ℝ), 0 < a →
        ∀ (χ : TestFn) (ε : ℝ≥0∞), 0 < ε →
        Tendsto (fun δ => P {ω | ε < localNegSobolevSq a
          (kpzRegularizedDistribution P Z t δ h₀ ω - H t h₀ ω) χ})
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0)) ∧
      (∀ t, 0 < t → ∀ (h₀ : Plane →ᵇ ℝ) (a : ℝ), 0 < a → ∀ χ : TestFn,
        Tendsto (fun δ => ∫⁻ ω, localNegSobolevSq a
          (kpzRegularizedDistribution P Z t δ h₀ ω - H t h₀ ω) χ ∂P)
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0)) := by
  obtain ⟨H, hHmeas, hHenergy⟩ :=
    exists_kpzRegularized_limitFamily_of P ϑ Z hZ hCauchy
  have hSigma : shfSigma Z ≤ (inferInstance : MeasurableSpace Ω) := by
    dsimp [shfSigma]
    apply iSup_le
    intro s
    apply iSup_le
    intro u
    apply iSup_le
    intro hsu
    exact (hZ.1 s u hsu.1 hsu.2).comap_le
  refine ⟨H, ?_, hHmeas, ?_, ?_, hHenergy⟩
  intro t ht h₀ φ
  obtain ⟨F, hFmeasSigma, hFeq⟩ :=
    exists_kpzRegularized_distributionVersionFamily P ϑ Z hZ ht h₀
  have hFmeas (δ : ℝ) (ψ : TestFn) : Measurable fun ω => F δ ω ψ := by
    exact (hFmeasSigma δ ψ).mono hSigma le_rfl
  have hHmeasFull (ψ : TestFn) : Measurable (fun ω => H t h₀ ω ψ) :=
    (hHmeas t ht h₀ ψ).mono hSigma le_rfl
  have hδpos : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < δ := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hδ
  have hδlt : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), δ < t := by
    have hnhds : ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ), δ < t := Iio_mem_nhds ht
    exact hnhds.filter_mono nhdsWithin_le_nhds
  have hδvalid : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < δ ∧ δ < t :=
    hδpos.and hδlt
  have henergy (a : ℝ) (ha : 0 < a) (χ : TestFn) :
      Tendsto (fun δ => ∫⁻ ω, localNegSobolevSq a (F δ ω - H t h₀ ω) χ ∂P)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    have heq : (fun δ => ∫⁻ ω, localNegSobolevSq a
          (F δ ω - H t h₀ ω) χ ∂P) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun δ => ∫⁻ ω, localNegSobolevSq a
          (kpzRegularizedDistribution P Z t δ h₀ ω - H t h₀ ω) χ ∂P) := by
      filter_upwards [hδvalid] with δ hδ
      have hdist : ∀ᵐ ω ∂P, F δ ω - H t h₀ ω =
          kpzRegularizedDistribution P Z t δ h₀ ω - H t h₀ ω := by
        filter_upwards [hFeq δ hδ.1 hδ.2] with ω hω
        simp [hω]
      exact lintegral_congr_ae (hdist.mono fun ω hω => by simp [hω])
    exact Tendsto.congr' heq.symm (hHenergy t ht h₀ a ha χ)
  have hmeasure := tendstoInMeasure_of_expected_localNegSobolevSq P F (H t h₀) 1
    hFmeas hHmeasFull (fun χ => henergy 1 (by norm_num) χ) φ
  have hpairEq : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (fun ω => F δ ω φ) =ᵐ[P]
        (fun ω => ∫ x, φ x * kpzRegularized P Z t δ h₀ x ω) := by
    filter_upwards [hδvalid] with δ hδ
    have hloc := kpzRegularized_locallyIntegrable_ae_of_initial
      ϑ P Z hZ hsym hδ.1 hδ.2 h₀
    filter_upwards [hFeq δ hδ.1 hδ.2, hloc] with ω hdist hω
    have hLI : LocallyIntegrableOn (fun x => kpzRegularized P Z t δ h₀ x ω)
        (⊤ : TopologicalSpace.Opens Plane) volume := hω.locallyIntegrableOn ⊤
    have hEq : kpzRegularizedDistribution P Z t δ h₀ ω φ =
        ∫ x, φ x * kpzRegularized P Z t δ h₀ x ω := by
      change Distribution.ofFun ⊤
        (fun x => kpzRegularized P Z t δ h₀ x ω) volume ⊤ φ = _
      rw [Distribution.ofFun_apply hLI]
      rfl
    calc
      F δ ω φ = kpzRegularizedDistribution P Z t δ h₀ ω φ :=
        congrArg (fun D : Distr => D φ) hdist
      _ = ∫ x, φ x * kpzRegularized P Z t δ h₀ x ω := hEq
  exact hmeasure.congr' hpairEq EventuallyEq.rfl
  · intro t δ hδ hδt h₀
    exact kpzRegularized_locallyIntegrable_ae_of_initial
      ϑ P Z hZ hsym hδ hδt h₀
  · intro t ht h₀ a ha χ ε hε
    obtain ⟨F, hFmeasSigma, hFeq⟩ :=
      exists_kpzRegularized_distributionVersionFamily P ϑ Z hZ ht h₀
    have hFmeas (δ : ℝ) (ψ : TestFn) : Measurable (fun ω => F δ ω ψ) := by
      exact (hFmeasSigma δ ψ).mono hSigma le_rfl
    have hHmeasFull (ψ : TestFn) : Measurable (fun ω => H t h₀ ω ψ) :=
      (hHmeas t ht h₀ ψ).mono hSigma le_rfl
    let E : ℝ → Ω → ℝ≥0∞ := fun δ ω =>
      localNegSobolevSq a (F δ ω - H t h₀ ω) χ
    have hEmeas (δ : ℝ) : Measurable (E δ) := by
      apply measurable_localNegSobolevSq
      intro ψ
      exact (hFmeas δ ψ).sub (hHmeasFull ψ)
    have hvalid : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0),
        0 < δ ∧ δ < t := by
      have hpos : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < δ := by
        filter_upwards [self_mem_nhdsWithin] with δ hδ
        exact hδ
      have hlt : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), δ < t := by
        have hnhds : ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ), δ < t := Iio_mem_nhds ht
        exact hnhds.filter_mono nhdsWithin_le_nhds
      exact hpos.and hlt
    have hEtend : Tendsto (fun δ => ∫⁻ ω, E δ ω ∂P)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
      have heq : (fun δ => ∫⁻ ω, E δ ω ∂P) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          (fun δ => ∫⁻ ω, localNegSobolevSq a
            (kpzRegularizedDistribution P Z t δ h₀ ω - H t h₀ ω) χ ∂P) := by
        filter_upwards [hvalid] with δ hδ
        have hdist : ∀ᵐ ω ∂P, F δ ω - H t h₀ ω =
            kpzRegularizedDistribution P Z t δ h₀ ω - H t h₀ ω := by
          filter_upwards [hFeq δ hδ.1 hδ.2] with ω hω
          simp [hω]
        exact lintegral_congr_ae (hdist.mono fun ω hω => by simp [E, hω])
      exact Tendsto.congr' heq.symm (hHenergy t ht h₀ a ha χ)
    have hprob : Tendsto (fun δ => P {ω | ε < E δ ω})
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) :=
      tendsto_measure_lt_of_lintegral_tendsto_zero P E hEmeas hEtend ε hε
    have heq : (fun δ => P {ω | ε < E δ ω}) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun δ => P {ω | ε < localNegSobolevSq a
          (kpzRegularizedDistribution P Z t δ h₀ ω - H t h₀ ω) χ}) := by
      filter_upwards [hvalid] with δ hδ
      have hset : {ω | ε < E δ ω} =ᵐ[P] {ω | ε < localNegSobolevSq a
          (kpzRegularizedDistribution P Z t δ h₀ ω - H t h₀ ω) χ} := by
        filter_upwards [hFeq δ hδ.1 hδ.2] with ω hω
        simp [E, hω]
      exact measure_congr hset
    exact Tendsto.congr' heq hprob

/-- A uniform expected-energy bound for the regularized fields, together with expected-energy
convergence to a measurable limit, implies almost-sure finiteness of every fixed local energy of
that limit. The countable localizer exhaustion then gives local negative-Sobolev membership. -/
theorem kpzRegularized_limit_memLocalNegSobolev_of
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ϑ : ℝ) (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t : ℝ} (ht : 0 < t) (h₀ : Plane →ᵇ ℝ) (H : Ω → Distr)
    (hHmeas : ∀ φ : TestFn, Measurable[shfSigma Z] fun ω => H ω φ)
    {a : ℝ} (ha : 0 < a)
    (hHenergy : ∀ χ : TestFn, Tendsto (fun δ => ∫⁻ ω,
      localNegSobolevSq a (kpzRegularizedDistribution P Z t δ h₀ ω - H ω) χ ∂P)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
    (hMoment : ∀ χ : TestFn, ∃ C : ℝ, ∀ δ : ℝ, 0 < δ → δ < t / 2 →
      ∫⁻ ω, localNegSobolevSq a (kpzRegularizedDistribution P Z t δ h₀ ω) χ ∂P ≤
        ENNReal.ofReal C) :
    ∀ᵐ ω ∂P, MemLocalNegSobolev a (H ω) := by
  obtain ⟨V, hVmeas, hVeq⟩ :=
    exists_kpzRegularized_distributionVersionFamily P ϑ Z hZ ht h₀
  have hSigma : shfSigma Z ≤ (inferInstance : MeasurableSpace Ω) := by
    dsimp [shfSigma]
    apply iSup_le
    intro s
    apply iSup_le
    intro u
    apply iSup_le
    intro hsu
    exact (hZ.1 s u hsu.1 hsu.2).comap_le
  have hLocalFinite (n : ℕ) : ∀ᵐ ω ∂P,
      localNegSobolevSq a (H ω) (localizer n) < ⊤ := by
    obtain ⟨C, hC⟩ := hMoment (localizer n)
    have hδpos : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < δ := by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact hδ
    have hδlt : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), δ < t / 2 := by
      have hnhds : ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ), δ < t / 2 :=
        Iio_mem_nhds (half_pos ht)
      exact hnhds.filter_mono nhdsWithin_le_nhds
    have hδdiff : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ∫⁻ ω, localNegSobolevSq a
          (kpzRegularizedDistribution P Z t δ h₀ ω - H ω) (localizer n) ∂P < 1 :=
      (hHenergy (localizer n)).eventually (Iio_mem_nhds (by norm_num))
    have hδall := (hδpos.and hδlt).and hδdiff
    obtain ⟨δ, hδall⟩ := hδall.exists
    rcases hδall with ⟨⟨hδpos', hδlt'⟩, hδdiff'⟩
    have hδt : δ < t := by linarith [hδlt', ht]
    have hRawIntegral := hC δ hδpos' hδlt'
    have hRawFinite :
        ∫⁻ ω, localNegSobolevSq a
          (kpzRegularizedDistribution P Z t δ h₀ ω) (localizer n) ∂P < ⊤ :=
      lt_of_le_of_lt hRawIntegral ENNReal.ofReal_lt_top
    have hDiffFinite :
        ∫⁻ ω, localNegSobolevSq a
          (kpzRegularizedDistribution P Z t δ h₀ ω - H ω) (localizer n) ∂P < ⊤ :=
      lt_trans hδdiff' ENNReal.one_lt_top
    have hVmeasFull (φ : TestFn) : Measurable (fun ω => V δ ω φ) :=
      (hVmeas δ φ).mono hSigma le_rfl
    have hHmeasFull (φ : TestFn) : Measurable (fun ω => H ω φ) :=
      (hHmeas φ).mono hSigma le_rfl
    have hRawAEMeas : AEMeasurable
        (fun ω => localNegSobolevSq a
          (kpzRegularizedDistribution P Z t δ h₀ ω) (localizer n)) P := by
      have hmeas := measurable_localNegSobolevSq hVmeasFull a (localizer n)
      have hEq : (fun ω => localNegSobolevSq a (V δ ω) (localizer n)) =ᵐ[P]
          (fun ω => localNegSobolevSq a
            (kpzRegularizedDistribution P Z t δ h₀ ω) (localizer n)) := by
        filter_upwards [hVeq δ hδpos' hδt] with ω hω
        simp [hω]
      exact hmeas.aemeasurable.congr hEq
    have hDiffAEMeas : AEMeasurable
        (fun ω => localNegSobolevSq a
          (kpzRegularizedDistribution P Z t δ h₀ ω - H ω) (localizer n)) P := by
      have hSubMeas (φ : TestFn) : Measurable (fun ω => (V δ ω - H ω) φ) := by
        change Measurable (fun ω => V δ ω φ - H ω φ)
        exact (hVmeasFull φ).sub (hHmeasFull φ)
      have hmeas := measurable_localNegSobolevSq hSubMeas a (localizer n)
      have hEq : (fun ω => localNegSobolevSq a (V δ ω - H ω) (localizer n)) =ᵐ[P]
          (fun ω => localNegSobolevSq a
            (kpzRegularizedDistribution P Z t δ h₀ ω - H ω) (localizer n)) := by
        filter_upwards [hVeq δ hδpos' hδt] with ω hω
        simp [hω]
      exact hmeas.aemeasurable.congr hEq
    have hRawAEFinite : ∀ᵐ ω ∂P,
        localNegSobolevSq a (kpzRegularizedDistribution P Z t δ h₀ ω) (localizer n) < ⊤ :=
      ae_lt_top' hRawAEMeas hRawFinite.ne
    have hDiffAEFinite : ∀ᵐ ω ∂P,
        localNegSobolevSq a
          (kpzRegularizedDistribution P Z t δ h₀ ω - H ω) (localizer n) < ⊤ :=
      ae_lt_top' hDiffAEMeas hDiffFinite.ne
    filter_upwards [hRawAEFinite, hDiffAEFinite] with ω hRaw hDiff
    have hRawNorm := (localNegSobolevENorm_lt_top_iff a
      (kpzRegularizedDistribution P Z t δ h₀ ω) (localizer n)).2 hRaw
    have hDiffNorm := (localNegSobolevENorm_lt_top_iff a
      (kpzRegularizedDistribution P Z t δ h₀ ω - H ω) (localizer n)).2 hDiff
    have hsum : H ω = kpzRegularizedDistribution P Z t δ h₀ ω +
        -(kpzRegularizedDistribution P Z t δ h₀ ω - H ω) := by abel
    have htriangle : localNegSobolevENorm a (H ω) (localizer n) ≤
        localNegSobolevENorm a (kpzRegularizedDistribution P Z t δ h₀ ω) (localizer n) +
          localNegSobolevENorm a (kpzRegularizedDistribution P Z t δ h₀ ω - H ω)
            (localizer n) := by
      calc
        _ = localNegSobolevENorm a
            (kpzRegularizedDistribution P Z t δ h₀ ω +
              -(kpzRegularizedDistribution P Z t δ h₀ ω - H ω)) (localizer n) :=
          congrArg (fun D : Distr => localNegSobolevENorm a D (localizer n)) hsum
        _ ≤ localNegSobolevENorm a (kpzRegularizedDistribution P Z t δ h₀ ω) (localizer n) +
            localNegSobolevENorm a (kpzRegularizedDistribution P Z t δ h₀ ω - H ω)
              (localizer n) := by
          simpa only [localNegSobolevENorm_neg] using
            (localNegSobolevENorm_add_le a
              (kpzRegularizedDistribution P Z t δ h₀ ω)
              (-(kpzRegularizedDistribution P Z t δ h₀ ω - H ω)) (localizer n))
    have hsumFinite := ENNReal.add_lt_top.mpr ⟨hRawNorm, hDiffNorm⟩
    exact (localNegSobolevENorm_lt_top_iff a (H ω) (localizer n)).mp
      (htriangle.trans_lt hsumFinite)
  have hAll : ∀ᵐ ω ∂P, ∀ n : ℕ,
      localNegSobolevSq a (H ω) (localizer n) < ⊤ := by
    apply ae_all_iff.mpr
    exact hLocalFinite
  filter_upwards [hAll] with ω hω
  exact Critical2DKPZ.Analysis.Sobolev.memLocalNegSobolev_of_localizer_energy_lt_top
    ha.le (H ω) hω

set_option linter.style.haveILetI false in
/-- A spatial test pairing of a regularized field has a version measurable with respect to the
sigma algebra generated by the SHF coordinates. The field is expressed through the swapped random
measure, and the compact-exhaustion measurability theorem supplies a measurable representative. -/
theorem exists_shfSigma_measurable_kpzRegularized_integral
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (h₀ : Plane →ᵇ ℝ) (φ : TestFn) :
    ∃ f : Ω → ℝ, Measurable[shfSigma Z] f ∧
      f =ᵐ[P] (fun ω => ∫ x, φ x * kpzRegularized P Z t δ h₀ x ω) := by
  classical
  let T : ℝ := t - δ
  let μ : Ω → Measure (Plane × Plane) := fun ω => (Z 0 T ω).map Prod.swap
  have hTpos : 0 < T := by dsimp [T]; linarith
  have hTlt : T < t := by dsimp [T]; linarith
  have hZmeas : Measurable (Z 0 T) := hZ.1 0 T le_rfl hTpos
  have hμmeas : Measurable μ :=
    (Measure.measurable_map Prod.swap measurable_swap).comp hZmeas
  have hμlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
    filter_upwards [hZ.2.1 0 T le_rfl hTpos] with ω hω
    letI : IsLocallyFiniteMeasure (Z 0 T ω) := hω.1
    exact Critical2DKPZ.SHF.Symmetries.locallyFinite_map_homeomorph
      (Homeomorph.prodComm Plane Plane) (Z 0 T ω)
  let K : ℕ → Set (Plane × Plane) := fun n => Metric.closedBall 0 (n : ℝ)
  let S : Set (Measure (Plane × Plane)) := {m | ∀ n, m (K n) < ∞}
  have hKmeas (n : ℕ) : MeasurableSet (K n) :=
    Metric.isClosed_closedBall.measurableSet
  have hSmeas : MeasurableSet S := by
    simp only [S, Set.ofPred_forall]
    exact MeasurableSet.iInter fun n =>
      measurableSet_lt (Measure.measurable_coe (hKmeas n)) measurable_const
  have hsource : ∀ᵐ ω ∂P, μ ω ∈ S := by
    filter_upwards [hμlocal] with ω hω
    intro n
    letI : IsLocallyFiniteMeasure (μ ω) := hω
    exact (isCompact_closedBall 0 (n : ℝ)).measure_lt_top
  let ν : Measure (Measure (Plane × Plane)) := P.map μ
  have hmassLaw : ∀ᵐ m ∂ν, m ∈ S := (ae_map_iff hμmeas.aemeasurable hSmeas).2 hsource
  have hνlocal : ∀ᵐ m ∂ν, IsLocallyFiniteMeasure m := by
    filter_upwards [hmassLaw] with m hm
    apply locallyFinite_of_closedBall_mass
    intro n
    exact hm n
  let c : ℝ := ∫ ω, Real.log
    (shfPairing Z 0 T (fun _ => (1 : ℝ)) (fun y => heatKernel δ y) ω) ∂P
  let g : Plane → ℝ := fun y => Real.exp (h₀ y)
  let F : Measure (Plane × Plane) → ℝ := fun m =>
    ∫ x, φ x * (Real.log (∫ p, heatKernel δ (p.1 - x) * g p.2 ∂m) - c)
  have hg : Measurable g := Real.continuous_exp.measurable.comp h₀.continuous.measurable
  have hgn (y : Plane) : 0 ≤ g y := (Real.exp_pos _).le
  have hφ : Measurable (φ : Plane → ℝ) := φ.continuous.measurable
  have hF : AEMeasurable F ν :=
    Critical2DKPZ.JointConvergence.aemeasurable_integral_log_heatPairing
      ν (fun m => m) measurable_id hνlocal δ c hδ g φ hg hgn hφ
  let Fm : Measure (Plane × Plane) → ℝ := hF.mk F
  have hFm : Measurable Fm := hF.measurable_mk
  have hle : MeasurableSpace.comap (Z 0 T) inferInstance ≤ shfSigma Z := by
    dsimp [shfSigma]
    apply le_iSup_of_le 0
    apply le_iSup_of_le T
    exact le_iSup_of_le ⟨le_rfl, hTpos⟩ le_rfl
  have hZsigma : Measurable[shfSigma Z] (Z 0 T) :=
    Measurable.of_comap_le hle
  have hμsigma : Measurable[shfSigma Z] μ := by
    exact (Measure.measurable_map Prod.swap measurable_swap).comp hZsigma
  have hAE : (F ∘ μ) =ᵐ[P] (Fm ∘ μ) := ae_eq_comp hμmeas.aemeasurable hF.ae_eq_mk
  have hcenter (ω : Ω) :
      (∫ p, heatKernel δ p.1 ∂μ ω) =
        shfPairing Z 0 T (fun _ => (1 : ℝ)) (fun y => heatKernel δ y) ω := by
    have hmap := integral_map (μ := Z 0 T ω) measurable_swap.aemeasurable
      (((measurable_heatKernel δ).comp measurable_fst).aestronglyMeasurable)
    simpa [μ, shfPairing] using hmap
  have hcenterIntegral :
      (∫ ω, Real.log (∫ p, heatKernel δ p.1 ∂μ ω) ∂P) = c := by
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [hcenter ω]
  have hpoint (ω : Ω) (x : Plane) :
      kpzRegularized P Z t δ h₀ x ω =
        Real.log (∫ p, heatKernel δ (p.1 - x) * g p.2 ∂μ ω) - c := by
    have hrev := Critical2DKPZ.JointConvergence.kpzRegularized_eq_kpzRegularizedReversed_of_reverseMeasure
      P Z t t δ h₀ x ω
    rw [hrev]
    simp [kpzRegularizedReversed, μ, c, g, shfPairing, T, hcenterIntegral]
  have hEq : (fun ω => ∫ x, φ x * kpzRegularized P Z t δ h₀ x ω) = F ∘ μ := by
    funext ω
    dsimp [F]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hpoint ω x]
  refine ⟨Fm ∘ μ, hFm.comp hμsigma, ?_⟩
  filter_upwards [hAE.symm] with ω hω
  change Fm (μ ω) = ∫ x, φ x * kpzRegularized P Z t δ h₀ x ω
  calc
    Fm (μ ω) = F (μ ω) := hω
    _ = ∫ x, φ x * kpzRegularized P Z t δ h₀ x ω := (congrFun hEq ω).symm

/-- The lattice field's logarithmic integral at a lattice terminal site. -/
def kpzLattice_siteValue (ϑ : ℝ) (N : ℕ) (t : ℝ)
    (h₀ : Plane →ᵇ ℝ) (z : Site) (ω : Disorder) : ℝ :=
  Real.log (∫ y : Plane, Real.exp (h₀ y) *
    ((N / 4 : ℝ) * pointToPoint (criticalBeta ϑ N) 0
      (evenCeil ((N : ℝ) * t)) (latticePoint N y) z ω)) -
    kpzLatticeCentring ϑ N t

/-- A fixed lattice-site value of the lattice field is measurable in the disorder. -/
theorem measurable_kpzLattice_siteValue (ϑ : ℝ) (N : ℕ) (t : ℝ)
    (h₀ : Plane →ᵇ ℝ) (z : Site) :
    Measurable (fun ω : Disorder => kpzLattice_siteValue ϑ N t h₀ z ω) := by
  let ψ : Plane × Disorder → ℝ := fun q => Real.exp (h₀ q.1) *
    ((N / 4 : ℝ) * pointToPoint (criticalBeta ϑ N) 0
      (evenCeil ((N : ℝ) * t)) (latticePoint N q.1) z q.2)
  have hsite : Measurable (fun q : Site × Disorder =>
      pointToPoint (criticalBeta ϑ N) 0 (evenCeil ((N : ℝ) * t)) q.1 z q.2) :=
    measurable_from_prod_countable_right fun w =>
      Critical2DKPZ.Polymer.measurable_pointToPoint
        (criticalBeta ϑ N) 0 (evenCeil ((N : ℝ) * t)) w z
  have hcoord : Measurable (fun q : Plane × Disorder => (latticePoint N q.1, q.2)) :=
    ((measurable_latticePoint N).comp measurable_fst).prodMk measurable_snd
  have hpoint : Measurable (fun q : Plane × Disorder =>
      pointToPoint (criticalBeta ϑ N) 0 (evenCeil ((N : ℝ) * t))
        (latticePoint N q.1) z q.2) := by
    have hfactor : (fun q : Plane × Disorder =>
        pointToPoint (criticalBeta ϑ N) 0 (evenCeil ((N : ℝ) * t))
          (latticePoint N q.1) z q.2) =
        (fun p : Site × Disorder =>
          pointToPoint (criticalBeta ϑ N) 0 (evenCeil ((N : ℝ) * t)) p.1 z p.2) ∘
          (fun q : Plane × Disorder => (latticePoint N q.1, q.2)) := by
      funext q
      rfl
    rw [hfactor]
    exact hsite.comp hcoord
  have hψ : Measurable ψ := by
    dsimp [ψ]
    exact (Real.continuous_exp.measurable.comp
      (h₀.continuous.measurable.comp measurable_fst)).mul
        (hpoint.const_mul (N / 4))
  have hlin : Measurable (fun ω : Disorder =>
      ∫⁻ y : Plane, ENNReal.ofReal (ψ (y, ω)) ∂volume) :=
    (ENNReal.measurable_ofReal.comp hψ).lintegral_prod_left'
  have hreal (ω : Disorder) :
      (∫ y : Plane, ψ (y, ω) ∂volume) =
        (∫⁻ y : Plane, ENNReal.ofReal (ψ (y, ω)) ∂volume).toReal := by
    apply integral_eq_lintegral_of_nonneg_ae
    · filter_upwards [] with y
      exact mul_nonneg (Real.exp_pos _).le
        (mul_nonneg (by positivity)
          (Critical2DKPZ.Polymer.pointToPoint_nonneg _ _ _ _ _ _))
    · exact (hψ.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hrepr : (fun ω : Disorder => kpzLattice_siteValue ϑ N t h₀ z ω) =
      fun ω => Real.log ((∫⁻ y : Plane,
        ENNReal.ofReal (ψ (y, ω)) ∂volume).toReal) - kpzLatticeCentring ϑ N t := by
    funext ω
    dsimp [kpzLattice_siteValue]
    have hEq : (∫ y : Plane, Real.exp (h₀ y) *
        ((N / 4 : ℝ) * pointToPoint (criticalBeta ϑ N) 0
          (evenCeil ((N : ℝ) * t)) (latticePoint N y) z ω) ∂volume) =
        ∫ y : Plane, ψ (y, ω) ∂volume := by
      rfl
    rw [hEq, hreal ω]
  rw [hrepr]
  exact (Real.measurable_log.comp hlin.ennreal_toReal).sub_const _

/-- The field at all lattice sites is jointly measurable in site and disorder. -/
theorem measurable_kpzLattice_siteProduct (ϑ : ℝ) (N : ℕ) (t : ℝ)
    (h₀ : Plane →ᵇ ℝ) :
    Measurable (fun q : Disorder × Site => kpzLattice_siteValue ϑ N t h₀ q.2 q.1) :=
  measurable_from_prod_countable_left fun z => measurable_kpzLattice_siteValue ϑ N t h₀ z

/-- The site-value field evaluated at its nearest lattice point is jointly measurable. -/
theorem measurable_kpzLattice_sitePullback (ϑ : ℝ) (N : ℕ) (t : ℝ)
    (h₀ : Plane →ᵇ ℝ) :
    Measurable (fun q : Disorder × Plane =>
      kpzLattice_siteValue ϑ N t h₀ (latticePoint N q.2) q.1) := by
  have hmap : Measurable (fun q : Disorder × Plane => (q.1, latticePoint N q.2)) :=
    measurable_fst.prodMk ((measurable_latticePoint N).comp measurable_snd)
  have hfactor : (fun q : Disorder × Plane =>
      kpzLattice_siteValue ϑ N t h₀ (latticePoint N q.2) q.1) =
      (fun q : Disorder × Site => kpzLattice_siteValue ϑ N t h₀ q.2 q.1) ∘
        (fun q : Disorder × Plane => (q.1, latticePoint N q.2)) := by
    funext q
    rfl
  rw [hfactor]
  exact (measurable_kpzLattice_siteProduct ϑ N t h₀).comp hmap

/-- The lattice field is the site-value field evaluated at its nearest lattice point. -/
theorem kpzLattice_eq_siteValue_latticePoint (ϑ : ℝ) (N : ℕ) (t : ℝ)
    (h₀ : Plane →ᵇ ℝ) :
    (fun q : Disorder × Plane => kpzLattice ϑ N t h₀ q.2 q.1) =
      fun q => kpzLattice_siteValue ϑ N t h₀ (latticePoint N q.2) q.1 := by
  funext q
  simp [kpzLattice_siteValue, kpzLattice, rescaledP2P]

/-- Joint measurability of the discrete KPZ lattice field. -/
theorem measurable_kpzLattice_joint (ϑ : ℝ) (N : ℕ) (t : ℝ)
    (h₀ : Plane →ᵇ ℝ) :
    Measurable (fun q : Disorder × Plane => kpzLattice ϑ N t h₀ q.2 q.1) := by
  rw [kpzLattice_eq_siteValue_latticePoint]
  exact measurable_kpzLattice_sitePullback ϑ N t h₀

/-- Every spatial section of the lattice KPZ field is measurable. -/
theorem measurable_kpzLattice_section (ϑ : ℝ) (N : ℕ) (t : ℝ)
    (h₀ : Plane →ᵇ ℝ) (ω : Disorder) :
    Measurable (fun x : Plane => kpzLattice ϑ N t h₀ x ω) := by
  let g : Site → ℝ := fun z =>
    Real.log (∫ y : Plane, Real.exp (h₀ y) *
      ((N / 4 : ℝ) * pointToPoint (criticalBeta ϑ N) 0
        (evenCeil ((N : ℝ) * t)) (latticePoint N y) z ω)) -
      kpzLatticeCentring ϑ N t
  have hg : Measurable g := measurable_of_countable g
  have hfactor : (fun x : Plane => kpzLattice ϑ N t h₀ x ω) = g ∘ latticePoint N := by
    funext x
    simp [g, kpzLattice, rescaledP2P]
  rw [hfactor]
  exact hg.comp (measurable_latticePoint N)

theorem kpzLattice_bounded_on_compact (ϑ : ℝ) (N : ℕ) (t : ℝ)
    (h₀ : Plane →ᵇ ℝ) (ω : Disorder) (K : Set Plane) (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, ‖kpzLattice ϑ N t h₀ x ω‖ ≤ B := by
  classical
  let g : Site → ℝ := fun z =>
    Real.log (∫ y : Plane, Real.exp (h₀ y) *
      ((N / 4 : ℝ) * pointToPoint (criticalBeta ϑ N) 0
        (evenCeil ((N : ℝ) * t)) (latticePoint N y) z ω)) -
      kpzLatticeCentring ϑ N t
  have hfactor : (fun x : Plane => kpzLattice ϑ N t h₀ x ω) =
      g ∘ latticePoint N := by
    funext x
    simp [g, kpzLattice, rescaledP2P]
  have hfinite := Critical2DKPZ.SHF.Limit.finite_latticePoint_image_of_bounded
    (N := N) hK.isBounded
  let values : Set ℝ := g '' (latticePoint N '' K)
  have hvfinite : values.Finite := hfinite.image g
  obtain ⟨M, hM⟩ := hvfinite.bddAbove
  obtain ⟨m, hm⟩ := hvfinite.bddBelow
  let B : ℝ := max |M| |m|
  refine ⟨B, ?_, fun x hx => ?_⟩
  · dsimp [B]
    positivity
  have hvalue : kpzLattice ϑ N t h₀ x ω ∈ values := by
    rw [congrFun hfactor x]
    exact ⟨latticePoint N x, ⟨x, hx, rfl⟩, rfl⟩
  have hupper : kpzLattice ϑ N t h₀ x ω ≤ M := hM hvalue
  have hlower : m ≤ kpzLattice ϑ N t h₀ x ω := hm hvalue
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · dsimp [B]
    exact (neg_le_neg (le_max_right |M| |m|)).trans ((neg_abs_le m).trans hlower)
  · dsimp [B]
    exact hupper.trans (le_abs_self M |>.trans (le_max_left |M| |m|))

/-- Every discrete lattice path is locally integrable in space. -/
theorem kpzLattice_locallyIntegrable (ϑ : ℝ) (N : ℕ) (t : ℝ)
    (h₀ : Plane →ᵇ ℝ) (ω : Disorder) :
    LocallyIntegrable (fun x => kpzLattice ϑ N t h₀ x ω) volume := by
  have hmeas : Measurable (fun x : Plane => kpzLattice ϑ N t h₀ x ω) :=
    measurable_kpzLattice_section ϑ N t h₀ ω
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨B, _, hB⟩ := kpzLattice_bounded_on_compact ϑ N t h₀ ω K hK
  exact Measure.integrableOn_of_bounded (ne_of_lt hK.measure_lt_top)
    hmeas.aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      exact hB x hx)

/-- The lattice field has finite local negative Sobolev energy at every nonnegative order. -/
theorem kpzLattice_memLocalNegSobolev (ϑ : ℝ) (N : ℕ) (t : ℝ)
    (h₀ : Plane →ᵇ ℝ) (ω : Disorder) {a : ℝ} (ha : 0 ≤ a) :
    MemLocalNegSobolev a
      (Distribution.ofFun ⊤ (fun x => kpzLattice ϑ N t h₀ x ω) volume ⊤) := by
  apply memLocalNegSobolev_ofFun ha (kpzLattice_locallyIntegrable ϑ N t h₀ ω)
  intro χ
  let f : Plane → ℝ := fun x => χ x * kpzLattice ϑ N t h₀ x ω
  have hmeas : Measurable f := by
    dsimp [f]
    exact χ.continuous.measurable.mul
      (measurable_kpzLattice_section ϑ N t h₀ ω)
  have hcompact : HasCompactSupport f := by
    dsimp [f]
    exact (show HasCompactSupport (χ : Plane → ℝ) from χ.hasCompactSupport).mul_right
  have hχrange : IsCompact ((fun x : Plane => ‖χ x‖) '' tsupport χ) :=
    χ.hasCompactSupport.isCompact.image χ.continuous.norm
  obtain ⟨Mχ, hMχ⟩ := hχrange.bddAbove
  let Bχ : ℝ := max Mχ 0
  have hBχ : 0 ≤ Bχ := le_max_right _ _
  have hχbound : ∀ x : Plane, ‖χ x‖ ≤ Bχ := by
    intro x
    by_cases hx : x ∈ tsupport χ
    · exact (hMχ ⟨x, hx, rfl⟩).trans (le_max_left _ _)
    · have hx0 : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hx0, Bχ]
  obtain ⟨M, hM0, hM⟩ := kpzLattice_bounded_on_compact ϑ N t h₀ ω (tsupport χ)
    χ.hasCompactSupport.isCompact
  let C : ℝ := Bχ * M
  have hC : 0 ≤ C := mul_nonneg hBχ hM0
  have hfbnd : ∀ x, |f x| ≤ C := by
    intro x
    by_cases hx : x ∈ tsupport χ
    · have hχx : |χ x| ≤ Bχ := by
        simpa only [Real.norm_eq_abs] using hχbound x
      have hfx : ‖kpzLattice ϑ N t h₀ x ω‖ ≤ M := hM x hx
      rw [Real.norm_eq_abs] at hfx
      dsimp [f, C]
      rw [abs_mul]
      exact mul_le_mul hχx hfx (abs_nonneg _) hBχ
    · have hx0 : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simpa [f, hx0] using hC
  have hsqMeas : Measurable (fun x => f x ^ 2) := hmeas.pow_const 2
  have hsqCompact : HasCompactSupport (fun x => f x ^ 2) := by
    have hcomp : HasCompactSupport ((fun r : ℝ => r ^ 2) ∘ f) :=
      hcompact.comp_left (g := fun r : ℝ => r ^ 2) (by norm_num)
    have heq : (fun x : Plane => f x ^ 2) = (fun r : ℝ => r ^ 2) ∘ f := by
      funext x
      rfl
    rw [heq]
    exact hcomp
  have hsqBound : ∃ B : ℝ, ∀ x, |f x ^ 2| ≤ B := by
    refine ⟨C ^ 2, fun x => ?_⟩
    have hC' : |f x| ≤ C := hfbnd x
    rw [abs_of_nonneg (sq_nonneg (f x))]
    nlinarith [sq_abs (f x), abs_nonneg (f x), hC]
  have hsqInt : Integrable (fun x => f x ^ 2) volume :=
    Critical2DKPZ.Smoothing.integrable_of_measurable_compactSupport_bounded
      hsqMeas hsqCompact hsqBound
  exact (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).mpr hsqInt

/-- Lattice distribution evaluations are measurable in the disorder. -/
theorem measurable_kpzLattice_distribution_pairing (ϑ : ℝ) (N : ℕ) (t : ℝ)
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn) :
    Measurable (fun ω : Disorder =>
      (Distribution.ofFun ⊤ (fun x => kpzLattice ϑ N t h₀ x ω) volume ⊤) φ) := by
  exact measurable_ofFun_evaluation (measurable_kpzLattice_joint ϑ N t h₀)
    (fun ω => kpzLattice_locallyIntegrable ϑ N t h₀ ω) φ

/-- Scalar test convergence, as in `kpzLattice_testFn_tendsto_of`, and uniform local-energy bounds give joint local Sobolev convergence via `tendstoInDistribution_locNegSobolevTuple`. -/
theorem kpzLattice_localSobolevTuple_tendsto_internal
    (ϑ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hC12 : ToyJointAt ϑ P Z)
    (hrevN : LatticeReverseLawClose ϑ)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (hHmeas : ∀ t, 0 < t → ∀ h₀ : Plane →ᵇ ℝ, ∀ φ : TestFn,
      Measurable[shfSigma Z] fun ω => H t h₀ ω φ)
    (hHmem : ∀ t, 0 < t → ∀ h₀ : Plane →ᵇ ℝ, ∀ᵐ ω ∂P,
      ∀ a, 0 < a → MemLocalNegSobolev a (H t h₀ ω))
    {k : ℕ} (t : Fin k → ℝ) (h₀ : Fin k → (Plane →ᵇ ℝ))
    (ht : ∀ i, 0 < t i) {a : ℝ} (ha : 0 < a)
    (hEnergy : ∀ i (χ : TestFn), ∃ C : ℝ, ∀ N : ℕ,
      ∫⁻ ω, localNegSobolevSq (a / 2)
        (Distribution.ofFun ⊤ (fun x => kpzLattice ϑ N (t i) (h₀ i) x ω) volume ⊤)
        χ ∂disorderLaw ≤ ENNReal.ofReal C)
    (hTestFn : IsCriticalKPZ P Z H → ShfSymmetriesAt ϑ P Z →
      ToyJointAt ϑ P Z → LatticeReverseLawClose ϑ →
      ∀ (k' : ℕ) (t' : Fin k' → ℝ)
      (h₀' : Fin k' → (Plane →ᵇ ℝ)) (φ' : Fin k' → TestFn),
      (∀ i, 0 < t' i) →
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) (i : Fin k') =>
          ∫ x, φ' i x * kpzLattice ϑ N (t' i) (h₀' i) x ω)
        atTop (fun ω i => H (t' i) (h₀' i) ω (φ' i))
        (fun _ => disorderLaw) P) :
    TendstoInDistribution
      (fun (N : ℕ) (ω : Disorder) => toLocNegSobolevTuple a fun i =>
        Distribution.ofFun ⊤ (fun x => kpzLattice ϑ N (t i) (h₀ i) x ω) volume ⊤)
      atTop (fun ω => toLocNegSobolevTuple a fun i => H (t i) (h₀ i) ω)
      (fun _ => disorderLaw) P := by
  let F : ℕ → Disorder → Fin k → Distr := fun N ω i =>
    Distribution.ofFun ⊤ (fun x => kpzLattice ϑ N (t i) (h₀ i) x ω) volume ⊤
  let G : Ω → Fin k → Distr := fun ω i => H (t i) (h₀ i) ω
  have hmeasF : ∀ N i (φ : TestFn), Measurable (fun ω : Disorder =>
      (Distribution.ofFun ⊤ (fun x => kpzLattice ϑ N (t i) (h₀ i) x ω) volume ⊤) φ) := by
    intro N i φ
    exact measurable_kpzLattice_distribution_pairing ϑ N (t i) (h₀ i) φ
  have hF : ∀ N ω i, MemLocalNegSobolev a
      (Distribution.ofFun ⊤ (fun x => kpzLattice ϑ N (t i) (h₀ i) x ω) volume ⊤) := by
    intro N ω i
    exact kpzLattice_memLocalNegSobolev ϑ N (t i) (h₀ i) ω (le_of_lt ha)
  have hLoc : ∀ N ω i, LocallyIntegrable (fun x => kpzLattice ϑ N (t i) (h₀ i) x ω) := by
    intro N ω i
    exact kpzLattice_locallyIntegrable ϑ N (t i) (h₀ i) ω
  have hmeas : ∀ N i (φ : TestFn), Measurable fun ω => F N ω i φ := by
    intro N i φ
    exact hmeasF N i φ
  have hGmeas : ∀ i (φ : TestFn), Measurable fun ω => G ω i φ := by
    intro i φ
    exact (hHmeas (t i) (ht i) (h₀ i) φ).mono
      (show shfSigma Z ≤ (inferInstance : MeasurableSpace Ω) from by
        dsimp [shfSigma]
        apply iSup_le
        intro s
        apply iSup_le
        intro u
        apply iSup_le
        intro hsu
        exact (hZ.1 s u hsu.1 hsu.2).comap_le)
      le_rfl
  have hG : ∀ᵐ ω ∂P, ∀ i, MemLocalNegSobolev a (G ω i) := by
    apply ae_all_iff.mpr
    intro i
    exact (hHmem (t i) (ht i) (h₀ i)).mono fun ω hω => hω a ha
  have hbound : ∀ i (χ : TestFn), ∃ C : ℝ, ∀ N : ℕ,
      ∫⁻ ω, localNegSobolevSq (a / 2) (F N ω i) χ ∂disorderLaw ≤ ENNReal.ofReal C := by
    intro i χ
    simpa only [F] using hEnergy i χ
  have htest : ∀ φ : Fin k → TestFn,
      TendstoInDistribution (fun N ω i => F N ω i (φ i)) atTop
        (fun ω i => G ω i (φ i)) (fun _ => disorderLaw) P := by
    intro φ
    have hscalar := hTestFn hH hsym hC12 hrevN k t h₀ φ ht
    have hEq (N : ℕ) : (fun ω i => F N ω i (φ i)) =ᵐ[disorderLaw]
        (fun ω i => ∫ x, φ i x * kpzLattice ϑ N (t i) (h₀ i) x ω) := by
      filter_upwards [] with ω
      funext i
      have hLI : LocallyIntegrableOn
          (fun x : Plane => kpzLattice ϑ N (t i) (h₀ i) x ω)
          (⊤ : TopologicalSpace.Opens Plane) volume :=
        (hLoc N ω i).locallyIntegrableOn _
      change Distribution.ofFun ⊤
        (fun x => kpzLattice ϑ N (t i) (h₀ i) x ω) volume ⊤ (φ i) = _
      rw [Distribution.ofFun_apply hLI]
      rfl
    exact TendstoInDistribution.congr (fun N => (hEq N).symm)
      (Filter.Eventually.of_forall fun ω => rfl) hscalar
  simpa [F, G] using tendstoInDistribution_locNegSobolevTuple P
    (fun _ : ℕ => disorderLaw) ha F G
    hmeas hGmeas hF hG hbound htest

end Critical2DKPZ.LocalSobolev

end

end
