/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Positivity.FinitePathEhrhard
public import Critical2DKPZ.SHF.Positivity.HeatStartMean
public import Critical2DKPZ.Polymer.Profiles
public import Critical2DKPZ.JointConvergence.HeatStartProfileApprox
public import Critical2DKPZ.Provider.EhrhardTypeCharacterization
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Tactic

/-! # Ehrhard type of the full polymer heat-start pairing -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.SHF.Positivity
open scoped BoundedContinuousFunction Topology

namespace Critical2DKPZ.SHF.Positivity

/-- The polymer heat-start integrand with a bounded exponential terminal profile is integrable
for almost every disorder. -/
theorem ae_integrable_polymer_heat_pairing_integrand (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    {s t δ : ℝ} (_hs : 0 ≤ s) (_hst : s < t) (hδ : 0 < δ) (x : Plane)
    (h₀ : Plane →ᵇ ℝ) :
    ∀ᵐ ω ∂disorderLaw,
      Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x) * Real.exp (h₀ p.2))
        (polymerMeasure ϑ N s t ω) := by
  filter_upwards [ae_integrable_polymer_heat_start ϑ hN s t δ hδ x] with ω hheat
  let μ := polymerMeasure ϑ N s t ω
  have hG : AEStronglyMeasurable (fun p : Plane × Plane => Real.exp (h₀ p.2)) μ := by
    exact (Real.continuous_exp.comp (h₀.continuous.comp continuous_snd)).aestronglyMeasurable
  have hGbound : ∀ᵐ p ∂μ, ‖Real.exp (h₀ p.2)‖ ≤ Real.exp ‖h₀‖ := by
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) (by
      simpa only [Real.norm_eq_abs] using h₀.norm_coe_le_norm p.2))
  have hheat' : Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x)) μ := by
    simpa only [μ] using hheat
  exact hheat'.mul_bdd hG hGbound

/-- Truncating the heat-start integrand on increasing balls converges to the full pairing
whenever the full integrand is integrable. -/
theorem tendsto_truncatedHeatPairing_of_integrable (ϑ : ℝ) (N : ℕ)
    {s t δ : ℝ} (hδ : 0 < δ) (x : Plane) (h₀ : Plane →ᵇ ℝ) (ω : Disorder)
    (hInt : Integrable
      (fun p : Plane × Plane => heatKernel δ (p.1 - x) * Real.exp (h₀ p.2))
      (polymerMeasure ϑ N s t ω)) :
    Tendsto (fun k : ℕ => truncatedHeatPairing ϑ N s t δ x h₀ (k + 1) ω)
      atTop (𝓝 (∫ p, heatKernel δ (p.1 - x) * Real.exp (h₀ p.2)
        ∂(polymerMeasure ϑ N s t ω))) := by
  let μ := polymerMeasure ϑ N s t ω
  let F : ℕ → Plane × Plane → ℝ := fun k p =>
    heatKernel δ (p.1 - x) *
      Set.indicator (Metric.closedBall (0 : Plane) ((k : ℝ) + 1)) (fun _ => (1 : ℝ)) p.1 *
      Real.exp (h₀ p.2)
  let f : Plane × Plane → ℝ := fun p => heatKernel δ (p.1 - x) * Real.exp (h₀ p.2)
  have hInt' : Integrable f μ := by simpa only [f, μ] using hInt
  have hFk (k : ℕ) : Integrable (F k) μ := by
    dsimp [F, μ]
    exact integrable_truncatedHeatPairing_integrand ϑ N s t δ x h₀ (k + 1) ω hδ
  have hFmeas : ∀ k, AEStronglyMeasurable (F k) μ := fun k => (hFk k).1
  have hFbound : ∀ k, ∀ᵐ p ∂μ, ‖F k p‖ ≤ f p := by
    intro k
    filter_upwards [] with p
    by_cases hball : p.1 ∈ Metric.closedBall (0 : Plane) ((k : ℝ) + 1)
    · have hkernel : 0 ≤ heatKernel δ (p.1 - x) :=
        Critical2DKPZ.heatKernel_nonneg hδ.le _
      have hexp : 0 ≤ Real.exp (h₀ p.2) := (Real.exp_pos _).le
      have hvalue : F k p = f p := by simp [F, f, hball]
      rw [hvalue, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hkernel hexp)]
    · have hkernel : 0 ≤ heatKernel δ (p.1 - x) :=
        Critical2DKPZ.heatKernel_nonneg hδ.le _
      have hexp : 0 ≤ Real.exp (h₀ p.2) := (Real.exp_pos _).le
      have hzero : F k p = 0 := by simp [F, hball]
      rw [hzero]
      simp only [norm_zero]
      exact mul_nonneg hkernel hexp
  have hFlim : ∀ᵐ p ∂μ, Tendsto (fun k => F k p) atTop (𝓝 (f p)) := by
    apply Filter.Eventually.of_forall
    intro p
    let k₀ : ℕ := ⌈‖p.1‖⌉₊
    have hceil : ‖p.1‖ ≤ (k₀ : ℝ) := by
      exact Nat.le_ceil _
    have hEq : ∀ᶠ k : ℕ in atTop, F k p = f p := by
      filter_upwards [eventually_ge_atTop k₀] with k hk
      have hk' : (k₀ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hball : p.1 ∈ Metric.closedBall (0 : Plane) ((k : ℝ) + 1) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        linarith
      simp [F, f, hball]
    exact Tendsto.congr' (hEq.mono fun k hk => hk.symm) tendsto_const_nhds
  have hlim := tendsto_integral_of_dominated_convergence f hFmeas hInt' hFbound hFlim
  have hEq : (fun k : ℕ => truncatedHeatPairing ϑ N s t δ x h₀ (k + 1) ω) =ᶠ[atTop]
      fun k => ∫ p, F k p ∂μ := by
    filter_upwards [] with k
    simp only [F, μ, truncatedHeatPairing]
  exact Tendsto.congr' hEq hlim

/-- Every finite-cutoff polymer heat pairing is measurable in the disorder, by its cell-profile
representation. -/
theorem measurable_truncatedHeatPairing (ϑ : ℝ) (N : ℕ) (hN : 0 < N) (s t δ : ℝ)
    (x : Plane) (h₀ : Plane →ᵇ ℝ) (K : ℝ) (hδ : 0 < δ) :
    Measurable (fun ω => truncatedHeatPairing ϑ N s t δ x h₀ K ω) := by
  let ν : Site → ℝ := fun w => ∫ y in cell N w, heatKernel δ (y - x) *
    Set.indicator (Metric.closedBall (0 : Plane) K) (fun _ => (1 : ℝ)) y
  let f : Site → ℝ := cellAverage N (fun y => Real.exp (h₀ y))
  have hEq : (fun ω => truncatedHeatPairing ϑ N s t δ x h₀ K ω) =
      profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * t)) ν f := by
    funext ω
    exact truncatedHeatPairing_eq_profile ϑ hN (s := s) (t := t) (δ := δ)
      x h₀ K ω (integrable_truncatedHeatPairing_integrand ϑ N s t δ x h₀ K ω hδ)
  rw [hEq]
  exact Polymer.measurable_profileP2Fun _ _ _ _ _

/-- Almost every full polymer heat pairing is its countable lattice profile. -/
theorem ae_polymer_heat_pairing_eq_profile (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    {s t δ : ℝ} (hs : 0 ≤ s) (hst : s < t) (hδ : 0 < δ) (x : Plane)
    (h₀ : Plane →ᵇ ℝ) :
    ∀ᵐ ω ∂disorderLaw,
      ∫ p, heatKernel δ (p.1 - x) * Real.exp (h₀ p.2)
        ∂(polymerMeasure ϑ N s t ω) =
      profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * t))
        (fun w => ∫ y in cell N w, heatKernel δ (y - x))
        (fun z => cellAverage N (fun y => Real.exp (h₀ y)) z) ω := by
  filter_upwards [ae_integrable_polymer_heat_pairing_integrand ϑ hN hs hst hδ x h₀]
    with ω hInt
  exact (JointConvergence.profile_cellHeat_eq_polymerMeasure_pairing
    ϑ N s t δ x h₀ ω (by omega) hInt).symm

/-- For all sufficiently large lattice scales, the heat-start integrand is spatially integrable and its pairing is positive almost surely, while the logarithm of that pairing has an Ehrhard-type law. -/
theorem isEhrhardType_log_polymer_heat_pairing (ϑ : ℝ) {s t δ : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hδ : 0 < δ) (x : Plane) (h₀ : Plane →ᵇ ℝ) :
    ∀ᶠ N : ℕ in atTop,
      (∀ᵐ ω ∂disorderLaw,
        Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x) * Real.exp (h₀ p.2))
          (polymerMeasure ϑ N s t ω) ∧
        0 < ∫ p, heatKernel δ (p.1 - x) * Real.exp (h₀ p.2)
          ∂(polymerMeasure ϑ N s t ω)) ∧
      IsEhrhardType (disorderLaw.map fun ω =>
        Real.log (∫ p, heatKernel δ (p.1 - x) * Real.exp (h₀ p.2)
          ∂(polymerMeasure ϑ N s t ω))) := by
  filter_upwards [eventually_ge_atTop 1,
    isEhrhardType_log_truncatedHeatPairing ϑ hs hst hδ x h₀] with N hN hcut
  have hNpos : 0 < N := by omega
  let A : Disorder → ℝ := fun ω =>
    ∫ p, heatKernel δ (p.1 - x) * Real.exp (h₀ p.2)
      ∂(polymerMeasure ϑ N s t ω)
  let X : ℕ → Disorder → ℝ := fun k ω =>
    Real.log (truncatedHeatPairing ϑ N s t δ x h₀ (k + 1) ω)
  let Y : Disorder → ℝ := fun ω => Real.log (A ω)
  have hAint : ∀ᵐ ω ∂disorderLaw,
      Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x) * Real.exp (h₀ p.2))
        (polymerMeasure ϑ N s t ω) :=
    ae_integrable_polymer_heat_pairing_integrand ϑ hN hs hst hδ x h₀
  have hApos (ω : Disorder) (hInt : Integrable
      (fun p : Plane × Plane => heatKernel δ (p.1 - x) * Real.exp (h₀ p.2))
        (polymerMeasure ϑ N s t ω)) : 0 < A ω := by
    have hcutpos : 0 < truncatedHeatPairing ϑ N s t δ x h₀ 1 ω :=
      (hcut 1 (by norm_num)).1 ω
    have hcutInt : Integrable
        (fun p : Plane × Plane => heatKernel δ (p.1 - x) *
          Set.indicator (Metric.closedBall (0 : Plane) 1) (fun _ => (1 : ℝ)) p.1 *
          Real.exp (h₀ p.2)) (polymerMeasure ϑ N s t ω) :=
      integrable_truncatedHeatPairing_integrand ϑ N s t δ x h₀ 1 ω hδ
    have hle : (fun p : Plane × Plane => heatKernel δ (p.1 - x) *
        Set.indicator (Metric.closedBall (0 : Plane) 1) (fun _ => (1 : ℝ)) p.1 *
        Real.exp (h₀ p.2)) ≤ᵐ[polymerMeasure ϑ N s t ω]
        fun p => heatKernel δ (p.1 - x) * Real.exp (h₀ p.2) := by
      apply Filter.Eventually.of_forall
      intro p
      by_cases hp : p.1 ∈ Metric.closedBall (0 : Plane) 1
      · simp [hp]
      · have hk : 0 ≤ heatKernel δ (p.1 - x) :=
          Critical2DKPZ.heatKernel_nonneg hδ.le _
        simpa [hp] using mul_nonneg hk (Real.exp_nonneg _)
    have hmono : truncatedHeatPairing ϑ N s t δ x h₀ 1 ω ≤ A ω := by
      change (∫ p, heatKernel δ (p.1 - x) *
        Set.indicator (Metric.closedBall (0 : Plane) 1) (fun _ => (1 : ℝ)) p.1 *
        Real.exp (h₀ p.2) ∂(polymerMeasure ϑ N s t ω)) ≤ _
      exact integral_mono_ae hcutInt hInt hle
    exact hcutpos.trans_le hmono
  constructor
  · filter_upwards [hAint] with ω hInt
    exact ⟨hInt, hApos ω hInt⟩
  · let ν : ℕ → ProbabilityMeasure ℝ := fun k =>
      ⟨disorderLaw.map (X k), inferInstance⟩
    let ν' : ProbabilityMeasure ℝ := ⟨disorderLaw.map Y, inferInstance⟩
    have hXmeas (k : ℕ) : AEMeasurable (X k) disorderLaw := by
      exact (Real.measurable_log.comp
        (measurable_truncatedHeatPairing ϑ N hNpos s t δ x h₀ (k + 1) hδ)).aemeasurable
    have hYmeas : AEMeasurable Y disorderLaw := by
      let ν₀ : Site → ℝ := fun w => ∫ y in cell N w, heatKernel δ (y - x)
      let f₀ : Site → ℝ := fun z => cellAverage N (fun y => Real.exp (h₀ y)) z
      have hprofile : Measurable (fun ω => profileP2Fun (criticalBeta ϑ N)
          (evenCeil (N * s)) (evenCeil (N * t)) ν₀ f₀ ω) :=
        Polymer.measurable_profileP2Fun _ _ _ _ _
      have hEq := ae_polymer_heat_pairing_eq_profile ϑ hN hs hst hδ x h₀
      have hAmeas : AEMeasurable A disorderLaw := by
        exact hprofile.aemeasurable.congr (by
          filter_upwards [hEq] with ω hω
          exact hω.symm)
      exact (Real.measurable_log.comp_aemeasurable hAmeas)
    have hlogTendsto : ∀ᵐ ω ∂disorderLaw,
        Tendsto (fun k => X k ω) atTop (𝓝 (Y ω)) := by
      filter_upwards [hAint] with ω hInt
      have hpos := hApos ω hInt
      have hvalue := tendsto_truncatedHeatPairing_of_integrable
        ϑ N hδ x h₀ ω hInt
      change Tendsto (fun k : ℕ => Real.log
        (truncatedHeatPairing ϑ N s t δ x h₀ ((k : ℝ) + 1) ω))
        atTop (𝓝 (Real.log (A ω)))
      exact (Real.continuousAt_log (ne_of_gt hpos)).tendsto.comp hvalue
    have hdist : TendstoInDistribution X atTop Y (fun _ : ℕ => disorderLaw) disorderLaw :=
      tendstoInDistribution_of_ae_tendsto hXmeas hYmeas hlogTendsto
    have hweak : Tendsto ν atTop (𝓝 ν') := by
      simpa only [ν, ν'] using hdist.tendsto
    have hνEhrhard (k : ℕ) : IsEhrhardType (ν k : Measure ℝ) := by
      dsimp only [ν, X]
      simpa only [ProbabilityMeasure.coe_mk] using
        (hcut (k + 1) (by positivity)).2
    have hlimit := Provider.ehrhardType_weakClosure ν ν' hweak hνEhrhard
    simpa only [ν', Y, ProbabilityMeasure.coe_mk, A] using hlimit

end Critical2DKPZ.SHF.Positivity

end
