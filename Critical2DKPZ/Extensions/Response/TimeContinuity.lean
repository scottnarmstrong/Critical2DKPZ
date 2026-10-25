/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.Response.UniformRate
public import Critical2DKPZ.Extensions.Response.SpatialShift
public import Critical2DKPZ.Extensions.Response.CutoffMeasurable
public import Critical2DKPZ.Assembly.Final
import Critical2DKPZ.SHF.TimeContinuity.DiscreteModulusAssembly
import Critical2DKPZ.SHF.Positivity.CutoffTests
import Critical2DKPZ.NonGaussian.CompactMean
import Critical2DKPZ.Assembly.RegularizedComparison
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Tactic

/-! # Time continuity of tested KPZ fields

Compact flow pairings have an L² modulus. Compact Gaussian cutoffs and the
mean-one identity extend this to heat pairings, before passing to logarithms.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BoundedContinuousFunction CompactlySupported ENNReal Topology
namespace Critical2DKPZ.Extensions.Response

/-- Real upper bounds characterize convergence of a nonnegative extended quantity to zero. -/
theorem tendsto_zero_of_real_bounds {ι : Type*} {l : Filter ι} {f : ι → ℝ≥0∞}
    (hf : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, f i ≤ ENNReal.ofReal ε) :
    Tendsto f l (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.mpr fun ε hε => ?_
  by_cases htop : ε = ⊤
  · simp only [htop, le_top, eventually_true]
  · have hp : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
    simpa only [ENNReal.ofReal_toReal htop] using hf ε.toReal hp

/-- A compact SHF pairing is almost everywhere measurable. -/
theorem aemeasurable_compact_flow (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (φ : C_c(Plane × Plane, ℝ)) :
    AEMeasurable (fun ω => ∫ p, φ p ∂Z s t ω) P := by
  have h := (SHF.Positivity.isCriticalSHF_compact_pairings_tendsto P Z hZ
    (fun _ : Fin 1 => s) (fun _ => t) (fun _ => ⟨hs, hst⟩) (fun _ => φ)).aemeasurable_limit
  exact (measurable_pi_apply 0).comp_aemeasurable h

/-- The square-integral estimate controls the L² norm, with integrability explicit. -/
theorem eLpNorm_two_le_of_sq_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {f : Ω → ℝ} (hf : AEStronglyMeasurable f P)
    (hfi : Integrable (fun ω => f ω ^ 2) P) {ε : ℝ} (hε : 0 ≤ ε)
    (hb : (∫ ω, f ω ^ 2 ∂P) ≤ ε ^ 2) : eLpNorm f 2 P ≤ ENNReal.ofReal ε := by
  have hm : MemLp f 2 P := (memLp_two_iff_integrable_sq hf).mpr hfi
  rw [hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  exact ENNReal.ofReal_le_ofReal ((Real.sqrt_le_iff).mpr ⟨hε, hb⟩)

/-- A compact flow test has a uniform L² modulus on admissible time windows. -/
theorem compact_flow_L2_modulus (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (φ : C_c(Plane × Plane, ℝ)) {τ T : ℝ} (hτ : 0 < τ) :
    ∀ ε > 0, ∃ η > 0, ∀ s t s' t' : ℝ,
      0 ≤ s → τ ≤ t - s → t ≤ T → 0 ≤ s' → τ ≤ t' - s' → t' ≤ T →
      |s - s'| + |t - t'| ≤ η →
      eLpNorm (fun ω => (∫ p, φ p ∂Z s t ω) - (∫ p, φ p ∂Z s' t' ω)) 2 P ≤ ENNReal.ofReal ε := by
  have hwords := Assembly.polymerMovingMomentLimit_of_word_limits
    SHF.Moments.pairTwoWordLimit (fun ϑ => Assembly.longWordLimits ϑ (by norm_num))
    (fun ϑ => Assembly.longWordLimits ϑ le_rfl) ϑ
  have hmod := SHF.TimeContinuity.isCriticalSHF_L2_modulus_of ϑ P Z hZ φ (T := T) hτ
    (SHF.TimeContinuity.polymerMeasure_L2_modulus_of ϑ hwords φ hτ)
  intro ε hε
  obtain ⟨η, hη, hb⟩ := hmod (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨η, hη, ?_⟩
  intro s t s' t' hs hst ht hs' hs't ht' hclose
  have hm := (aemeasurable_compact_flow ϑ P Z hZ (t := t) hs (by linarith) φ).sub
    (aemeasurable_compact_flow ϑ P Z hZ (t := t') hs' (by linarith) φ)
  have hb' := hb s t s' t' hs hst ht hs' hs't ht' hclose
  exact eLpNorm_two_le_of_sq_integral P hm.aestronglyMeasurable hb'.1 hε.le hb'.2

/-- Compact flow pairings depend continuously in L² on the positive terminal time. -/
theorem tendsto_eLpNorm_compact_flow_time (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (φ : C_c(Plane × Plane, ℝ)) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun s => eLpNorm (fun ω => (∫ p, φ p ∂Z 0 s ω) -
      (∫ p, φ p ∂Z 0 t ω)) 2 P) (𝓝 t) (𝓝 0) := by
  apply tendsto_zero_of_real_bounds
  intro ε hε
  obtain ⟨η, hη, hb⟩ := compact_flow_L2_modulus ϑ P Z hZ φ (T := t + 1)
    (half_pos ht) ε hε
  have hrad : 0 < min (t / 2) (min 1 η) := lt_min (half_pos ht) (lt_min one_pos hη)
  filter_upwards [Metric.ball_mem_nhds t hrad] with s hs
  have hdist : |s - t| < min (t / 2) (min 1 η) := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hs
  have hlow := (abs_lt.mp (hdist.trans_le (min_le_left _ _))).1
  have hupper := (abs_lt.mp (hdist.trans_le ((min_le_right _ _).trans (min_le_left _ _)))).2
  have hclose := hdist.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  apply hb 0 s 0 t le_rfl (by linarith) (by linarith) le_rfl (by linarith) (by linarith)
  simpa only [sub_zero, sub_self, abs_zero, zero_add] using hclose

/-- The terminal flat heat mass is integrable and has mean one. -/
theorem heat_end_integrable_mean_one (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (x : Plane) :
    Integrable (fun ω => ∫ p, heatKernel r (p.2 - x) ∂Z 0 t ω) P ∧
      (∫ ω, ∫ p, heatKernel r (p.2 - x) ∂Z 0 t ω ∂P) = 1 := by
  let M : Ω → Measure (Plane × Plane) := Z 0 t
  let S : Ω → Measure (Plane × Plane) := fun ω => (M ω).map Prod.swap
  let F : Measure (Plane × Plane) → ℝ := fun μ => ∫ p, heatKernel r (p.1 - x) ∂μ
  have hM : Measurable M := hZ.1 0 t le_rfl ht
  have hS : Measurable S := (Measure.measurable_map Prod.swap measurable_swap).comp hM
  have hID : IdentDistrib S M P P := ⟨hS.aemeasurable, hM.aemeasurable, cutoff_swap_law ϑ P Z hZ ht⟩
  have hFm : Measurable F := measurable_heat_mass r hr x
  have hF := hID.comp hFm
  have hfirst : Integrable (fun ω => F (M ω)) P ∧ (∫ ω, F (M ω) ∂P) = 1 := by
    simpa only [F, M, shfPairing, mul_one] using
      SmallScales.heatStart_integral_eq_one ϑ P Z hZ le_rfl ht hr x
  have heq (ω : Ω) : F (S ω) = ∫ p, heatKernel r (p.2 - x) ∂Z 0 t ω :=
    integral_map measurable_swap.aemeasurable
      (((measurable_heatKernel r).comp (measurable_fst.sub_const x)).aestronglyMeasurable)
  constructor
  · simpa only [Function.comp_def, heq] using hF.integrable_iff.mpr hfirst.1
  · have hm := hF.integral_eq.trans hfirst.2
    simpa only [Function.comp_def, heq] using hm

/-- Compactly supported approximation of a continuous function on the endpoint pair. -/
def pairCutoffTest (f : Plane × Plane → ℝ) (hf : Continuous f) (R : ℝ) :
    C_c(Plane × Plane, ℝ) where
  toFun p := f p * SHF.Tsai.ballCutoff R p.1 * SHF.Tsai.ballCutoff R p.2
  continuous_toFun := (hf.mul ((SHF.Tsai.continuous_ballCutoff R).comp continuous_fst)).mul
    ((SHF.Tsai.continuous_ballCutoff R).comp continuous_snd)
  hasCompactSupport' := by
    apply HasCompactSupport.of_support_subset_isCompact
      ((isCompact_closedBall (0 : Plane) (R + 1)).prod (isCompact_closedBall (0 : Plane) (R + 1)))
    intro p hp
    constructor
    · rw [Metric.mem_closedBall, dist_zero_right]
      by_contra hn
      have hz := SHF.Tsai.ballCutoff_eq_zero_of_le_norm (le_of_lt (lt_of_not_ge hn))
      exact hp (by change f p * SHF.Tsai.ballCutoff R p.1 * SHF.Tsai.ballCutoff R p.2 = 0; rw [hz, mul_zero, zero_mul])
    · rw [Metric.mem_closedBall, dist_zero_right]
      by_contra hn
      have hz := SHF.Tsai.ballCutoff_eq_zero_of_le_norm (le_of_lt (lt_of_not_ge hn))
      exact hp (by change f p * SHF.Tsai.ballCutoff R p.1 * SHF.Tsai.ballCutoff R p.2 = 0; rw [hz, mul_zero])

/-- A pair cutoff is bounded in absolute value by the original integrand. -/
theorem pairCutoffTest_abs_le (f : Plane × Plane → ℝ) (hf : Continuous f) (R : ℝ) (p : Plane × Plane) :
    |pairCutoffTest f hf R p| ≤ |f p| := by
  have h1 := SHF.Tsai.ballCutoff_mem_Icc R p.1
  have h2 := SHF.Tsai.ballCutoff_mem_Icc R p.2
  change |f p * SHF.Tsai.ballCutoff R p.1 * SHF.Tsai.ballCutoff R p.2| ≤ _
  rw [abs_mul, abs_mul, abs_of_nonneg h1.1, abs_of_nonneg h2.1]
  exact (mul_le_mul_of_nonneg_left h2.2 (mul_nonneg (abs_nonneg _) h1.1)).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left h1.2 (abs_nonneg (f p)))

/-- Cutoffs preserve nonnegativity. -/
theorem pairCutoffTest_nonneg {f : Plane × Plane → ℝ} (hf : Continuous f)
    (hfn : ∀ p, 0 ≤ f p) (R : ℝ) (p : Plane × Plane) : 0 ≤ pairCutoffTest f hf R p :=
  mul_nonneg (mul_nonneg (hfn p) (SHF.Tsai.ballCutoff_mem_Icc R p.1).1)
    (SHF.Tsai.ballCutoff_mem_Icc R p.2).1

/-- At a fixed point the compact approximation eventually equals its target. -/
theorem eventually_pairCutoffTest_eq (f : Plane × Plane → ℝ) (hf : Continuous f) (p : Plane × Plane) :
    ∀ᶠ R : ℝ in atTop, pairCutoffTest f hf R p = f p := by
  filter_upwards [SHF.Tsai.eventually_ballCutoff_eq_one p.1,
    SHF.Tsai.eventually_ballCutoff_eq_one p.2] with R h1 h2
  change f p * SHF.Tsai.ballCutoff R p.1 * SHF.Tsai.ballCutoff R p.2 = _
  rw [h1, h2, mul_one, mul_one]

/-- Any integrable continuous function has integrable pair cutoffs. -/
theorem integrable_pairCutoffTest {μ : Measure (Plane × Plane)} {f : Plane × Plane → ℝ}
    (hf : Continuous f) (hi : Integrable f μ) (R : ℝ) : Integrable (pairCutoffTest f hf R) μ := by
  refine hi.norm.mono' (pairCutoffTest f hf R).continuous.aestronglyMeasurable ?_
  exact Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using pairCutoffTest_abs_le f hf R p

/-- Pair cutoffs converge under integration against any measure with an integrable target. -/
theorem tendsto_integral_pairCutoffTest {μ : Measure (Plane × Plane)} {f : Plane × Plane → ℝ}
    (hf : Continuous f) (hi : Integrable f μ) :
    Tendsto (fun R => ∫ p, pairCutoffTest f hf R p ∂μ) atTop (𝓝 (∫ p, f p ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun p => |f p|)
  · exact Eventually.of_forall fun R => (pairCutoffTest f hf R).continuous.aestronglyMeasurable
  · exact Eventually.of_forall fun R => Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs] using pairCutoffTest_abs_le f hf R p
  · exact hi.abs
  · exact Eventually.of_forall fun p =>
      (tendsto_congr' (eventually_pairCutoffTest_eq f hf p)).mpr tendsto_const_nhds

/-- L² continuity of a compact pairing also gives L¹ continuity. -/
theorem tendsto_eLpNorm_compact_flow_time_one (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (φ : C_c(Plane × Plane, ℝ)) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun s => eLpNorm (fun ω => (∫ p, φ p ∂Z 0 s ω) - (∫ p, φ p ∂Z 0 t ω)) 1 P)
      (𝓝 t) (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_eLpNorm_compact_flow_time ϑ P Z hZ φ ht) (fun _ => zero_le) ?_
  exact fun _ => eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)

/-- The mean of a nonnegative compact pairing depends continuously on terminal time. -/
theorem tendsto_integral_compact_flow_time (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (φ : C_c(Plane × Plane, ℝ)) (hφ : ∀ p, 0 ≤ φ p) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun s => ∫ ω, ∫ p, φ p ∂Z 0 s ω ∂P) (𝓝 t) (𝓝 (∫ ω, ∫ p, φ p ∂Z 0 t ω ∂P)) := by
  apply tendsto_integral_of_L1' (fun ω => ∫ p, φ p ∂Z 0 t ω)
  · filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (NonGaussian.integrable_and_integral_compactPairing_eq ϑ P Z hZ le_rfl hs φ hφ).1
  · exact tendsto_eLpNorm_compact_flow_time_one ϑ P Z hZ φ ht

/-- A nonnegative continuous random-measure integral is measurable, including its
Bochner totalization outside the integrability event. -/
theorem measurable_nonnegative_flowPairing (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t : ℝ} (ht : 0 < t) (f : Plane × Plane → ℝ) (hf : Continuous f) (hfn : ∀ p, 0 ≤ f p) :
    Measurable (fun ω => ∫ p, f p ∂Z 0 t ω) := by
  have heq (μ : Measure (Plane × Plane)) : (∫ p, f p ∂μ) = (∫⁻ p, ENNReal.ofReal (f p) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hfn) hf.aestronglyMeasurable
  simp_rw [heq]
  exact ((Measure.measurable_lintegral hf.measurable.ennreal_ofReal).comp
    (hZ.1 0 t le_rfl ht)).ennreal_toReal

/-- The expected mass of flat compact heat cutoffs tends to one. -/
theorem tendsto_integral_flat_cutoff (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (x : Plane) :
    Tendsto (fun R => ∫ ω, ∫ p, pairCutoffTest
      (fun p : Plane × Plane => heatKernel r (p.2 - x))
      ((continuous_heatKernel r).comp (continuous_snd.sub continuous_const)) R p ∂Z 0 t ω ∂P)
      atTop (𝓝 1) := by
  let f : Plane × Plane → ℝ := fun p => heatKernel r (p.2 - x)
  have hf : Continuous f := (continuous_heatKernel r).comp (continuous_snd.sub continuous_const)
  have hfn (p : Plane × Plane) : 0 ≤ f p := heatKernel_nonneg hr.le _
  have hi := heat_end_integrable_mean_one ϑ P Z hZ ht hr x
  have hsp := ae_integrable_heat_end ϑ P Z hZ ht hr x
  have hc : Tendsto (fun R => ∫ ω, ∫ p, pairCutoffTest f hf R p ∂Z 0 t ω ∂P)
      atTop (𝓝 (∫ ω, ∫ p, f p ∂Z 0 t ω ∂P)) := by
    apply tendsto_integral_filter_of_dominated_convergence (bound := fun ω => ∫ p, f p ∂Z 0 t ω)
    · exact Eventually.of_forall fun R =>
        (aemeasurable_compact_flow ϑ P Z hZ le_rfl ht (pairCutoffTest f hf R)).aestronglyMeasurable
    · refine Eventually.of_forall fun R => ?_
      filter_upwards [hsp] with ω hω
      rw [Real.norm_of_nonneg (integral_nonneg (pairCutoffTest_nonneg hf hfn R))]
      apply integral_mono (integrable_pairCutoffTest hf hω R) hω
      intro p
      exact (le_abs_self _).trans ((pairCutoffTest_abs_le f hf R p).trans_eq (abs_of_nonneg (hfn p)))
    · exact hi.1
    · filter_upwards [hsp] with ω hω
      exact tendsto_integral_pairCutoffTest hf hω
  have hmean : (∫ ω, ∫ p, f p ∂Z 0 t ω ∂P) = 1 := hi.2
  rw [hmean] at hc
  exact hc

/-- The first seminorm of an integrable real function is its absolute integral. -/
theorem eLpNorm_one_eq_integral_abs {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {f : Ω → ℝ} (hf : Integrable f P) :
    eLpNorm f 1 P = ENNReal.ofReal (∫ ω, |f ω| ∂P) := by
  rw [(memLp_one_iff_integrable.mpr hf).eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
  simp only [ENNReal.toReal_one, inv_one, Real.rpow_one, Real.norm_eq_abs]

/-- A bounded nonnegative weight controls its cutoff error by the flat cutoff error. -/
theorem integral_weighted_cutoff_error {μ : Measure (Plane × Plane)} {r : ℝ}
    (hr : 0 < r) (x : Plane)
    (hint : Integrable (fun p : Plane × Plane => heatKernel r (p.2 - x)) μ)
    {g : Plane → ℝ} (hg : Continuous g) (hgn : ∀ y, 0 ≤ g y)
    {C : ℝ} (hgb : ∀ y, |g y| ≤ C) (R : ℝ) :
    let f := fun p : Plane × Plane => g p.1 * heatKernel r (p.2 - x)
    let hf := (hg.comp continuous_fst).mul ((continuous_heatKernel r).comp (continuous_snd.sub continuous_const))
    let b := fun p : Plane × Plane => heatKernel r (p.2 - x)
    let hb := (continuous_heatKernel r).comp (continuous_snd.sub continuous_const)
    0 ≤ (∫ p, f p ∂μ) - (∫ p, pairCutoffTest f hf R p ∂μ) ∧
    (∫ p, f p ∂μ) - (∫ p, pairCutoffTest f hf R p ∂μ) ≤
      C * ((∫ p, b p ∂μ) - (∫ p, pairCutoffTest b hb R p ∂μ)) := by
  dsimp only
  let b : Plane × Plane → ℝ := fun p => heatKernel r (p.2 - x)
  let f : Plane × Plane → ℝ := fun p => g p.1 * b p
  have hb : Continuous b := (continuous_heatKernel r).comp (continuous_snd.sub continuous_const)
  have hf : Continuous f := (hg.comp continuous_fst).mul hb
  have hfi := integrable_weighted_heat hr x hint hg hgb
  have hc := integrable_pairCutoffTest hf hfi R
  have hbc := integrable_pairCutoffTest hb hint R
  have hdiff (p : Plane × Plane) : 0 ≤ f p - pairCutoffTest f hf R p := by
    have hfn : 0 ≤ f p := mul_nonneg (hgn p.1) (heatKernel_nonneg hr.le _)
    exact sub_nonneg.mpr ((le_abs_self _).trans ((pairCutoffTest_abs_le f hf R p).trans_eq (abs_of_nonneg hfn)))
  constructor
  · rw [← integral_sub hfi hc]
    exact integral_nonneg hdiff
  · rw [← integral_sub hfi hc, ← integral_sub hint hbc, ← integral_const_mul]
    apply integral_mono (hfi.sub hc) ((hint.sub hbc).const_mul C)
    intro p
    have h1 := SHF.Tsai.ballCutoff_mem_Icc R p.1
    have h2 := SHF.Tsai.ballCutoff_mem_Icc R p.2
    have hk : 0 ≤ 1 - SHF.Tsai.ballCutoff R p.1 * SHF.Tsai.ballCutoff R p.2 := by
      have hh := mul_le_mul h1.2 h2.2 h2.1 zero_le_one
      linarith only [hh]
    have hgp : g p.1 ≤ C := (le_abs_self _).trans (hgb p.1)
    have hh := mul_le_mul_of_nonneg_right hgp (mul_nonneg (heatKernel_nonneg hr.le (p.2 - x)) hk)
    change g p.1 * heatKernel r (p.2 - x) -
      g p.1 * heatKernel r (p.2 - x) * SHF.Tsai.ballCutoff R p.1 * SHF.Tsai.ballCutoff R p.2 ≤
      C * (heatKernel r (p.2 - x) - heatKernel r (p.2 - x) * SHF.Tsai.ballCutoff R p.1 * SHF.Tsai.ballCutoff R p.2)
    convert hh using 1 <;> ring

/-- The L¹ cutoff error for a bounded nonnegative profile is controlled by the
missing expected flat mass. -/
theorem eLpNorm_heat_cutoff_tail_le (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (x : Plane)
    (g : Plane → ℝ) (hg : Continuous g) (hgn : ∀ y, 0 ≤ g y)
    {C : ℝ} (hgb : ∀ y, |g y| ≤ C) (R : ℝ) :
    let f := fun p : Plane × Plane => g p.1 * heatKernel r (p.2 - x)
    let hf := (hg.comp continuous_fst).mul ((continuous_heatKernel r).comp (continuous_snd.sub continuous_const))
    let b := fun p : Plane × Plane => heatKernel r (p.2 - x)
    let hb := (continuous_heatKernel r).comp (continuous_snd.sub continuous_const)
    eLpNorm (fun ω => (∫ p, f p ∂Z 0 t ω) - (∫ p, pairCutoffTest f hf R p ∂Z 0 t ω)) 1 P ≤
      ENNReal.ofReal (C * (1 - ∫ ω, ∫ p, pairCutoffTest b hb R p ∂Z 0 t ω ∂P)) := by
  dsimp only
  let b : Plane × Plane → ℝ := fun p => heatKernel r (p.2 - x)
  let f : Plane × Plane → ℝ := fun p => g p.1 * b p
  have hb : Continuous b := (continuous_heatKernel r).comp (continuous_snd.sub continuous_const)
  have hf : Continuous f := (hg.comp continuous_fst).mul hb
  have hbn (p : Plane × Plane) : 0 ≤ b p := heatKernel_nonneg hr.le _
  have hfn (p : Plane × Plane) : 0 ≤ f p := mul_nonneg (hgn p.1) (hbn p)
  let W : Ω → ℝ := fun ω => (∫ p, f p ∂Z 0 t ω) - (∫ p, pairCutoffTest f hf R p ∂Z 0 t ω)
  let B : Ω → ℝ := fun ω => (∫ p, b p ∂Z 0 t ω) - (∫ p, pairCutoffTest b hb R p ∂Z 0 t ω)
  have hbase := heat_end_integrable_mean_one ϑ P Z hZ ht hr x
  have hcut := (NonGaussian.integrable_and_integral_compactPairing_eq ϑ P Z hZ le_rfl ht
    (pairCutoffTest b hb R) (pairCutoffTest_nonneg hb hbn R)).1
  have hBi : Integrable B P := hbase.1.sub hcut
  have hWi : AEStronglyMeasurable W P :=
    ((measurable_nonnegative_flowPairing ϑ P Z hZ ht f hf hfn).aemeasurable.sub
      (aemeasurable_compact_flow ϑ P Z hZ le_rfl ht (pairCutoffTest f hf R))).aestronglyMeasurable
  have hdet : ∀ᵐ ω ∂P, 0 ≤ W ω ∧ W ω ≤ C * B ω := by
    filter_upwards [ae_integrable_heat_end ϑ P Z hZ ht hr x] with ω hω
    exact integral_weighted_cutoff_error hr x hω hg hgn hgb R
  have hWint : Integrable W P := (hBi.const_mul C).mono' hWi (hdet.mono fun ω hω => by
    rw [Real.norm_of_nonneg hω.1]
    exact hω.2)
  rw [eLpNorm_one_eq_integral_abs P hWint]
  apply ENNReal.ofReal_le_ofReal
  calc
    (∫ ω, |W ω| ∂P) = ∫ ω, W ω ∂P :=
      integral_congr_ae (hdet.mono fun ω hω => abs_of_nonneg hω.1)
    _ ≤ ∫ ω, C * B ω ∂P := integral_mono_ae hWint (hBi.const_mul C) (hdet.mono fun _ hω => hω.2)
    _ = C * (1 - ∫ ω, ∫ p, pairCutoffTest b hb R p ∂Z 0 t ω ∂P) := by
      rw [integral_const_mul, integral_sub hbase.1 hcut, hbase.2]

/-- Three-term comparison for first seminorms, with both endpoint errors in
the same orientation. -/
theorem eLpNorm_sub_le_three {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f a b g : Ω → ℝ) :
    eLpNorm (fun ω => f ω - g ω) 1 P ≤
      eLpNorm (fun ω => f ω - a ω) 1 P + eLpNorm (fun ω => a ω - b ω) 1 P +
        eLpNorm (fun ω => g ω - b ω) 1 P := by
  have heq : (fun ω => f ω - g ω) = fun ω => (f ω - a ω) + (a ω - b ω) - (g ω - b ω) := by
    funext ω
    ring
  rw [heq]
  exact (eLpNorm_sub_le (p := 1) (by norm_num)).trans
    (add_le_add (eLpNorm_add_le (p := 1) (by norm_num)) le_rfl)

/-- Heat-weighted pairings with bounded nonnegative profiles are continuous
in L¹ at every positive terminal time. -/
theorem tendsto_eLpNorm_heat_flow_time (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (x : Plane)
    (g : Plane → ℝ) (hg : Continuous g) (hgn : ∀ y, 0 ≤ g y)
    {C : ℝ} (hgb : ∀ y, |g y| ≤ C) :
    Tendsto (fun s => eLpNorm (fun ω => (∫ p, g p.1 * heatKernel r (p.2 - x) ∂Z 0 s ω) -
      (∫ p, g p.1 * heatKernel r (p.2 - x) ∂Z 0 t ω)) 1 P) (𝓝 t) (𝓝 0) := by
  let b : Plane × Plane → ℝ := fun p => heatKernel r (p.2 - x)
  let f : Plane × Plane → ℝ := fun p => g p.1 * b p
  have hb : Continuous b := (continuous_heatKernel r).comp (continuous_snd.sub continuous_const)
  have hf : Continuous f := (hg.comp continuous_fst).mul hb
  have hbn (p : Plane × Plane) : 0 ≤ b p := heatKernel_nonneg hr.le _
  let Q : ℝ → ℝ → ℝ := fun R s => ∫ ω, ∫ p, pairCutoffTest b hb R p ∂Z 0 s ω ∂P
  have hQ : Tendsto (fun R => C * (1 - Q R t)) atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub
      (tendsto_integral_flat_cutoff ϑ P Z hZ ht hr x)).const_mul C
    simpa only [sub_self, mul_zero] using h
  apply tendsto_zero_of_real_bounds
  intro ε hε
  obtain ⟨R, hR⟩ := (hQ.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < ε / 6))).exists
  have hQs : Tendsto (fun s => C * (1 - Q R s)) (𝓝 t) (𝓝 (C * (1 - Q R t))) :=
    (tendsto_const_nhds.sub (tendsto_integral_compact_flow_time ϑ P Z hZ
      (pairCutoffTest b hb R) (pairCutoffTest_nonneg hb hbn R) ht)).const_mul C
  have htail : ∀ᶠ s in 𝓝 t, C * (1 - Q R s) < ε / 3 :=
    hQs.eventually (Iio_mem_nhds (by linarith only [hR, hε]))
  have hmid : ∀ᶠ s in 𝓝 t, eLpNorm (fun ω =>
      (∫ p, pairCutoffTest f hf R p ∂Z 0 s ω) - (∫ p, pairCutoffTest f hf R p ∂Z 0 t ω)) 1 P ≤
        ENNReal.ofReal (ε / 3) :=
    ENNReal.tendsto_nhds_zero.mp (tendsto_eLpNorm_compact_flow_time_one ϑ P Z hZ (pairCutoffTest f hf R) ht)
      _ (by positivity)
  filter_upwards [htail, hmid, Ioi_mem_nhds ht] with s hs hmid hspos
  have hleft := (eLpNorm_heat_cutoff_tail_le ϑ P Z hZ hspos hr x g hg hgn hgb R).trans
    (ENNReal.ofReal_le_ofReal hs.le)
  have hright := (eLpNorm_heat_cutoff_tail_le ϑ P Z hZ ht hr x g hg hgn hgb R).trans
    (ENNReal.ofReal_le_ofReal (by linarith only [hR, hε] : C * (1 - Q R t) ≤ ε / 3))
  refine (eLpNorm_sub_le_three P _ _ _ _).trans ((add_le_add (add_le_add hleft hmid) hright).trans ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  linarith

/-- Uniform L² boundedness implies uniform integrability in L¹. -/
theorem unifIntegrable_one_of_L2_bound {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : ι → Ω → ℝ) (hf : ∀ i, AEStronglyMeasurable (f i) P)
    (C : ℝ) (hb : ∀ i, eLpNorm (f i) 2 P ≤ ENNReal.ofReal C) : UnifIntegrable f 1 P := by
  apply unifIntegrable_iff'.mpr
  intro ε hε
  have hlim := ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos
    (c := ENNReal.ofReal C) ENNReal.ofReal_ne_top (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨δ, hδ, hδb⟩ := ENNReal.nhds_zero_basis_Iic.mem_iff.mp
    (ENNReal.tendsto_nhds_zero.mp hlim ε hε)
  refine ⟨δ, hδ, ?_⟩
  intro i S _hS hPS
  have hcmp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
    (by norm_num) ((hf i).restrict (s := S))
  norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat, div_one,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, Measure.restrict_apply_univ] at hcmp
  refine hcmp.trans ((mul_le_mul_of_nonneg_right
    ((eLpNorm_restrict_le (f i) 2 P S).trans (hb i))
    (show (0 : ℝ≥0∞) ≤ P S ^ (1 / 2 : ℝ) from zero_le)).trans ?_)
  exact hδb hPS

/-- Vitali's theorem with a locally uniform L² bound, for countably generated filters. -/
theorem tendsto_L1_of_tendstoInMeasure_of_L2_bound {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {l : Filter ι} [l.IsCountablyGenerated]
    {f : ι → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ᶠ i in l, AEStronglyMeasurable (f i) P) (hg : MemLp g 2 P)
    (C : ℝ) (hb : ∀ᶠ i in l, eLpNorm (f i) 2 P ≤ ENNReal.ofReal C)
    (hfg : TendstoInMeasure P f l g) :
    Tendsto (fun i => eLpNorm (fun ω => f i ω - g ω) 1 P) l (𝓝 0) := by
  classical
  let F : ι → Ω → ℝ := fun i => if AEStronglyMeasurable (f i) P ∧
    eLpNorm (f i) 2 P ≤ ENNReal.ofReal C then f i else 0
  have hF (i : ι) : AEStronglyMeasurable (F i) P := by
    by_cases h : AEStronglyMeasurable (f i) P ∧ eLpNorm (f i) 2 P ≤ ENNReal.ofReal C
    · simpa only [F, ite_eq_left h] using h.1
    · simp only [F, ite_eq_right h]; exact aestronglyMeasurable_zero
  have hFb (i : ι) : eLpNorm (F i) 2 P ≤ ENNReal.ofReal C := by
    by_cases h : AEStronglyMeasurable (f i) P ∧ eLpNorm (f i) 2 P ≤ ENNReal.ofReal C
    · simpa only [F, ite_eq_left h] using h.2
    · simp only [F, ite_eq_right h, eLpNorm_zero, zero_le]
  have heq : ∀ᶠ i in l, F i = f i := by
    filter_upwards [hf, hb] with i hi hbi
    exact ite_eq_left ⟨hi, hbi⟩
  have hFm : TendstoInMeasure P F l g :=
    TendstoInMeasure.congr' (heq.mono fun _ h => Filter.Eventually.of_forall fun ω => congrFun h.symm ω)
      Filter.EventuallyEq.rfl hfg
  have hUI := unifIntegrable_one_of_L2_bound P F hF C hFb
  have hconv : Tendsto (fun i => eLpNorm (fun ω => F i ω - g ω) 1 P) l (𝓝 0) := by
    apply Filter.tendsto_iff_seq_tendsto.mpr
    intro u hu
    exact tendsto_Lp_finite_of_tendstoInMeasure (by norm_num) (by simp)
      (fun n => hF (u n)) (hg.mono_exponent (by norm_num)) (hUI.comp u) (hFm.comp hu)
  apply hconv.congr'
  filter_upwards [heq] with i hi
  rw [hi]

/-- Composition with the logarithm preserves convergence in probability at an
almost surely positive limit. No uniform distance from zero is assumed. -/
theorem tendstoInMeasure_log {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {l : Filter ι} [l.IsCountablyGenerated]
    {f : ι → Ω → ℝ} {g : Ω → ℝ}
    (hf : ∀ᶠ i in l, AEMeasurable (f i) P) (hg : AEMeasurable g P)
    (hpos : ∀ᵐ ω ∂P, 0 < g ω) (hfg : TendstoInMeasure P f l g) :
    TendstoInMeasure P (fun i ω => Real.log (f i ω)) l (fun ω => Real.log (g ω)) := by
  classical
  let F : ι → Ω → ℝ := fun i => if AEMeasurable (f i) P then f i else g
  have hF (i : ι) : AEMeasurable (F i) P := by
    by_cases hi : AEMeasurable (f i) P
    · simpa only [F, ite_eq_left hi] using hi
    · simpa only [F, ite_eq_right hi] using hg
  have heq : ∀ᶠ i in l, F i = f i := hf.mono fun i hi => ite_eq_left hi
  have hFm : TendstoInMeasure P F l g :=
    TendstoInMeasure.congr' (heq.mono fun _ h => Filter.Eventually.of_forall fun ω => congrFun h.symm ω)
      Filter.EventuallyEq.rfl hfg
  have hlog : TendstoInMeasure P (fun i ω => Real.log (F i ω)) l (fun ω => Real.log (g ω)) := by
    intro ε hε
    apply Filter.tendsto_iff_seq_tendsto.mpr
    intro u hu
    have hseq : TendstoInMeasure P (fun n ω => Real.log (F (u n) ω)) atTop (fun ω => Real.log (g ω)) := by
      apply (exists_seq_tendstoInMeasure_atTop_iff
        (fun n => (Real.measurable_log.comp_aemeasurable (hF (u n))).aestronglyMeasurable)).mpr
      intro ns hns
      obtain ⟨ms, hms, hae⟩ := ((hFm.comp hu).comp hns.tendsto_atTop).exists_seq_tendsto_ae
      refine ⟨ms, hms, ?_⟩
      filter_upwards [hae, hpos] with ω hω hp
      exact (Real.continuousAt_log hp.ne').tendsto.comp hω
    exact hseq ε hε
  refine TendstoInMeasure.congr' ?_ Filter.EventuallyEq.rfl hlog
  filter_upwards [heq] with i hi
  exact Filter.Eventually.of_forall fun ω => congrArg Real.log (congrFun hi ω)

/-- Uniform L² bounds for flat heat-start logarithms on bounded positive duration windows. -/
theorem heat_start_log_uniform_L2_bound (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {τ₀ τ₁ : ℝ} (hτ₀ : 0 < τ₀) :
    ∃ δ₀ > 0, ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∃ K ≥ 0, ∀ a b : ℝ,
      0 ≤ a → τ₀ ≤ b - a → b - a ≤ τ₁ → ∀ x : Plane,
      MemLp (SmallScales.heatStartLog Z a b δ x) 2 P ∧
      eLpNorm (SmallScales.heatStartLog Z a b δ x) 2 P ≤ ENNReal.ofReal K := by
  obtain ⟨C, δ₀, hδ₀, hb⟩ := SmallScales.heatStartLog_moments_le_of ϑ P Z hZ
    (Assembly.shfSymmetriesAt ϑ P Z hZ) (Assembly.heatStartLogAt_of_isCriticalSHF ϑ P Z hZ)
    (τ₁ := τ₁) hτ₀
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hδle
  let B := Real.log (Real.log δ⁻¹) + C
  refine ⟨|B| + 1, by positivity, ?_⟩
  intro a b ha hlo hhi x
  obtain ⟨hm, hm0, hv, hmb⟩ := hb a b δ ha hlo hhi hδ hδle x
  refine ⟨hm, eLpNorm_two_le_of_sq_integral P hm.aestronglyMeasurable hm.integrable_sq (by positivity) ?_⟩
  let m := ∫ ω, SmallScales.heatStartLog Z a b δ x ω ∂P
  change 0 ≤ -m at hm0
  change -2 * m ≤ B at hmb
  have hB : 0 ≤ B := by linarith only [hm0, hmb]
  have hmean : -m ≤ B / 2 := by linarith only [hmb]
  have hsquare : m ^ 2 ≤ (B / 2) ^ 2 := by
    simpa only [neg_sq] using pow_le_pow_left₀ hm0 hmean 2
  rw [variance_eq_sub hm] at hv
  change (∫ ω, SmallScales.heatStartLog Z a b δ x ω ^ 2 ∂P) - m ^ 2 ≤ -2 * m at hv
  rw [abs_of_nonneg hB]
  nlinarith only [hv, hmb, hsquare, sq_nonneg B, hB]

/-- Reversal identifies terminal and initial flat logarithmic heat masses in law. -/
theorem heat_end_log_identDistrib_start (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (x : Plane) :
    IdentDistrib (fun ω => Real.log (shfPairing Z 0 t (fun _ => 1) (fun y => heatKernel r (y - x)) ω))
      (SmallScales.heatStartLog Z 0 t r x) P P := by
  let M : Ω → Measure (Plane × Plane) := Z 0 t
  let S : Ω → Measure (Plane × Plane) := fun ω => (M ω).map Prod.swap
  let F : Measure (Plane × Plane) → ℝ := fun μ => Real.log (∫ p, heatKernel r (p.1 - x) ∂μ)
  have hM : Measurable M := hZ.1 0 t le_rfl ht
  have hS : Measurable S := (Measure.measurable_map Prod.swap measurable_swap).comp hM
  have hID : IdentDistrib S M P P := ⟨hS.aemeasurable, hM.aemeasurable, cutoff_swap_law ϑ P Z hZ ht⟩
  have hFm : Measurable F := CovarianceKernel.measurable_log_heatPairingMeasure r hr x
  have hF := hID.comp hFm
  have hend (ω : Ω) : F (S ω) = Real.log (shfPairing Z 0 t (fun _ => 1) (fun y => heatKernel r (y - x)) ω) := by
    have hi : (∫ p, heatKernel r (p.1 - x) ∂(S ω)) = ∫ p, heatKernel r (p.2 - x) ∂Z 0 t ω :=
      integral_map measurable_swap.aemeasurable
        (((measurable_heatKernel r).comp (measurable_fst.sub_const x)).aestronglyMeasurable)
    dsimp only [F]
    rw [hi]
    simp only [shfPairing, one_mul]
  have hstart (ω : Ω) : F (M ω) = SmallScales.heatStartLog Z 0 t r x ω := by
    simp only [F, M, SmallScales.heatStartLog, shfPairing, mul_one]
  convert hF using 1
  · funext ω
    exact (hend ω).symm
  · funext ω
    exact (hstart ω).symm

/-- A fixed terminal heat pairing with exponential bounded initial profile has a measurable logarithm. -/
theorem aemeasurable_heat_end_profile_log (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (h : Plane →ᵇ ℝ) (x : Plane) :
    AEMeasurable (fun ω => Real.log (shfPairing Z 0 t (fun y => Real.exp (h y))
      (fun y => heatKernel r (y - x)) ω)) P := by
  exact Real.measurable_log.comp_aemeasurable
    (measurable_nonnegative_flowPairing ϑ P Z hZ ht _
      ((Real.continuous_exp.comp (h.continuous.comp continuous_fst)).mul
        ((continuous_heatKernel r).comp (continuous_snd.sub continuous_const)))
      (fun p => mul_nonneg (Real.exp_pos _).le (heatKernel_nonneg hr.le _))).aemeasurable

/-- Strict positivity holds for all centres and bounded initial profiles on the same good event. -/
theorem ae_heat_end_profile_pos (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∀ (h : Plane →ᵇ ℝ) (x : Plane),
      0 < shfPairing Z 0 t (fun y => Real.exp (h y)) (fun y => heatKernel r (y - x)) ω := by
  filter_upwards [ae_cutoff_good ϑ P Z hZ t ht r hr] with ω hω
  have hp : 0 < ∫ p, heatKernel r p.2 ∂Z 0 t ω := by simpa only [shfPairing, one_mul] using hω.2
  intro h x
  exact pairing_pos hr hω.1 hp (Real.continuous_exp.comp h.continuous)
    (exp_profile_bound h) (fun y => Real.exp_pos _) x

/-- Changing a bounded initial profile changes the uncentred logarithm by at most its norm. -/
theorem ae_log_heat_end_profile_comparison (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (h : Plane →ᵇ ℝ) (x : Plane) :
    ∀ᵐ ω ∂P, |Real.log (shfPairing Z 0 t (fun y => Real.exp (h y))
      (fun y => heatKernel r (y - x)) ω) -
      Real.log (shfPairing Z 0 t (fun _ => 1) (fun y => heatKernel r (y - x)) ω)| ≤ ‖h‖ := by
  filter_upwards [ae_heat_end_profile_pos ϑ P Z hZ ht hr,
    ae_integrable_heat_end ϑ P Z hZ ht hr x] with ω hpos hint
  have hfin : Integrable (fun p : Plane × Plane => Real.exp ((0 : Plane →ᵇ ℝ) p.1) * heatKernel r (p.2 - x)) (Z 0 t ω) := by
    simpa only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero, one_mul] using hint
  have hc := Assembly.kpzRegularized_comparison P Z (t + r) r h 0 x ω
    (by simpa only [add_sub_cancel_right] using hpos 0 x) (by simpa only [add_sub_cancel_right] using hfin)
  have heq (a b c : ℝ) : (a - c) - (b - c) = a - b := by ring
  simpa only [kpzRegularized, add_sub_cancel_right, BoundedContinuousFunction.coe_zero,
    Pi.zero_apply, Real.exp_zero, sub_zero, heq] using hc

/-- Uniform L² logarithmic bounds in terminal orientation, for a bounded initial profile. -/
theorem heat_end_profile_log_uniform_L2_bound (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (h : Plane →ᵇ ℝ) {a b : ℝ} (ha : 0 < a) :
    ∃ δ₀ > 0, ∀ r : ℝ, 0 < r → r ≤ δ₀ → ∃ K ≥ 0, ∀ u : ℝ,
      a ≤ u → u ≤ b → ∀ x : Plane,
      MemLp (fun ω => Real.log (shfPairing Z 0 u (fun y => Real.exp (h y))
        (fun y => heatKernel r (y - x)) ω)) 2 P ∧
      eLpNorm (fun ω => Real.log (shfPairing Z 0 u (fun y => Real.exp (h y))
        (fun y => heatKernel r (y - x)) ω)) 2 P ≤ ENNReal.ofReal K := by
  obtain ⟨δ₀, hδ₀, hflat⟩ := heat_start_log_uniform_L2_bound ϑ P Z hZ (τ₁ := b) ha
  refine ⟨δ₀, hδ₀, ?_⟩
  intro r hr hrle
  obtain ⟨K, hK, hKb⟩ := hflat r hr hrle
  refine ⟨K + ‖h‖, add_nonneg hK (norm_nonneg h), ?_⟩
  intro u hau hub x
  have hu : 0 < u := ha.trans_le hau
  have hsource := hKb 0 u le_rfl (by simpa only [sub_zero] using hau) (by simpa only [sub_zero] using hub) x
  have hID := heat_end_log_identDistrib_start ϑ P Z hZ hu hr x
  let L : Ω → ℝ := fun ω => Real.log (shfPairing Z 0 u (fun y => Real.exp (h y)) (fun y => heatKernel r (y - x)) ω)
  let L₀ : Ω → ℝ := fun ω => Real.log (shfPairing Z 0 u (fun _ => 1) (fun y => heatKernel r (y - x)) ω)
  have hL₀ : MemLp L₀ 2 P := hID.memLp_iff.mpr hsource.1
  have hL₀b : eLpNorm L₀ 2 P ≤ ENNReal.ofReal K := (hID.eLpNorm_eq 2).le.trans hsource.2
  have hLm : AEMeasurable L P := aemeasurable_heat_end_profile_log ϑ P Z hZ hu hr h x
  have hcmp : ∀ᵐ ω ∂P, ‖L ω - L₀ ω‖ ≤ ‖h‖ := by
    simpa only [Real.norm_eq_abs] using ae_log_heat_end_profile_comparison ϑ P Z hZ hu hr h x
  have hdm : AEStronglyMeasurable (fun ω => L ω - L₀ ω) P := (hLm.sub hID.aemeasurable_fst).aestronglyMeasurable
  have hd : MemLp (fun ω => L ω - L₀ ω) 2 P := MemLp.of_bound hdm ‖h‖ hcmp
  have hdb : eLpNorm (fun ω => L ω - L₀ ω) 2 P ≤ ENNReal.ofReal ‖h‖ := by
    simpa only [measure_univ, ENNReal.one_rpow, one_mul] using eLpNorm_le_of_ae_bound (p := 2) hdm hcmp
  have heq : L = (fun ω => L ω - L₀ ω) + L₀ := by
    funext ω
    simp only [Pi.add_apply, sub_add_cancel]
  change MemLp L 2 P ∧ eLpNorm L 2 P ≤ ENNReal.ofReal (K + ‖h‖)
  rw [heq]
  refine ⟨hd.add hL₀, (eLpNorm_add_le (by norm_num)).trans ((add_le_add hdb hL₀b).trans_eq ?_)⟩
  rw [← ENNReal.ofReal_add (norm_nonneg h) hK, add_comm]

/-- At every positive flow time the uncentred profile logarithm is continuous in probability. -/
theorem tendstoInMeasure_log_heat_end_time (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (h : Plane →ᵇ ℝ) (x : Plane) :
    TendstoInMeasure P (fun s ω => Real.log (shfPairing Z 0 s (fun y => Real.exp (h y))
      (fun y => heatKernel r (y - x)) ω)) (𝓝 t)
      (fun ω => Real.log (shfPairing Z 0 t (fun y => Real.exp (h y)) (fun y => heatKernel r (y - x)) ω)) := by
  have hc : Continuous (fun p : Plane × Plane => Real.exp (h p.1) * heatKernel r (p.2 - x)) :=
    (Real.continuous_exp.comp (h.continuous.comp continuous_fst)).mul
      ((continuous_heatKernel r).comp (continuous_snd.sub continuous_const))
  have hn (p : Plane × Plane) : 0 ≤ Real.exp (h p.1) * heatKernel r (p.2 - x) :=
    mul_nonneg (Real.exp_pos _).le (heatKernel_nonneg hr.le _)
  have hm : ∀ᶠ s in 𝓝 t, AEMeasurable (fun ω => shfPairing Z 0 s (fun y => Real.exp (h y))
      (fun y => heatKernel r (y - x)) ω) P := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (measurable_nonnegative_flowPairing ϑ P Z hZ hs _ hc hn).aemeasurable
  have hlimit : AEMeasurable (fun ω => shfPairing Z 0 t (fun y => Real.exp (h y))
      (fun y => heatKernel r (y - x)) ω) P :=
    (measurable_nonnegative_flowPairing ϑ P Z hZ ht _ hc hn).aemeasurable
  have hpos := (ae_heat_end_profile_pos ϑ P Z hZ ht hr).mono fun ω hω => hω h x
  exact tendstoInMeasure_log P hm hlimit hpos
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0)
      (tendsto_eLpNorm_heat_flow_time ϑ P Z hZ ht hr x (fun y => Real.exp (h y))
        (Real.continuous_exp.comp h.continuous) (fun y => (Real.exp_pos _).le) (exp_profile_bound h)))

/-- The logarithmic L² bound upgrades pointwise time convergence to L¹ on the
interior of a fixed duration window. -/
theorem log_heat_end_L1_time_of_uniform_bound (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (h : Plane →ᵇ ℝ) {a b r : ℝ} (ha : 0 < a) (hr : 0 < r) (K : ℝ)
    (hbound : ∀ u : ℝ, a ≤ u → u ≤ b → ∀ x : Plane,
      MemLp (fun ω => Real.log (shfPairing Z 0 u (fun y => Real.exp (h y)) (fun y => heatKernel r (y - x)) ω)) 2 P ∧
      eLpNorm (fun ω => Real.log (shfPairing Z 0 u (fun y => Real.exp (h y)) (fun y => heatKernel r (y - x)) ω)) 2 P ≤ ENNReal.ofReal K)
    {t : ℝ} (hat : a < t) (htb : t < b) (x : Plane) :
    Tendsto (fun s => eLpNorm (fun ω => Real.log (shfPairing Z 0 s (fun y => Real.exp (h y))
      (fun y => heatKernel r (y - x)) ω) - Real.log (shfPairing Z 0 t (fun y => Real.exp (h y))
      (fun y => heatKernel r (y - x)) ω)) 1 P) (𝓝 t) (𝓝 0) := by
  have ht : 0 < t := ha.trans hat
  apply tendsto_L1_of_tendstoInMeasure_of_L2_bound P _ (hbound t hat.le htb.le x).1 K _
    (tendstoInMeasure_log_heat_end_time ϑ P Z hZ ht hr h x)
  · filter_upwards [Ioo_mem_nhds hat htb] with s hs
    exact (hbound s hs.1.le hs.2.le x).1.aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhds hat htb] with s hs
    exact (hbound s hs.1.le hs.2.le x).2

/-- Convergence in the first seminorm implies convergence of absolute integrals. -/
theorem tendsto_integral_abs_of_L1 {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {l : Filter ι} {f : ι → Ω → ℝ}
    (hf : ∀ᶠ i in l, Integrable (f i) P)
    (hc : Tendsto (fun i => eLpNorm (f i) 1 P) l (𝓝 0)) :
    Tendsto (fun i => ∫ ω, |f i ω| ∂P) l (𝓝 0) := by
  have ht := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hc
  apply ht.congr'
  filter_upwards [hf] with i hi
  change (eLpNorm (f i) 1 P).toReal = _
  rw [eLpNorm_one_eq_integral_abs P hi, ENNReal.toReal_ofReal (integral_nonneg fun ω => abs_nonneg _)]

/-- Testing logarithms against a compact smooth function preserves L¹ time continuity.
Fubini is justified by the uniform L² bound, independently of the realization. -/
theorem tested_log_heat_end_L1_time (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (h : Plane →ᵇ ℝ) (ψ : TestFn) {a b r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ u : ℝ, a ≤ u → u ≤ b → ∀ x : Plane,
      MemLp (fun ω => Real.log (shfPairing Z 0 u (fun y => Real.exp (h y)) (fun y => heatKernel r (y - x)) ω)) 2 P ∧
      eLpNorm (fun ω => Real.log (shfPairing Z 0 u (fun y => Real.exp (h y)) (fun y => heatKernel r (y - x)) ω)) 2 P ≤ ENNReal.ofReal K)
    {t : ℝ} (hat : a < t) (htb : t < b) :
    Tendsto (fun s => eLpNorm (fun ω =>
      (∫ x, ψ x * Real.log (shfPairing Z 0 s (fun y => Real.exp (h y)) (fun y => heatKernel r (y - x)) ω)) -
      (∫ x, ψ x * Real.log (shfPairing Z 0 t (fun y => Real.exp (h y)) (fun y => heatKernel r (y - x)) ω))) 1 P)
      (𝓝 t) (𝓝 0) := by
  have ht : 0 < t := ha.trans hat
  let L : ℝ → Plane → Ω → ℝ := fun s x ω => Real.log (shfPairing Z 0 s (fun y => Real.exp (h y))
    (fun y => heatKernel r (y - x)) ω)
  let F : ℝ → Plane × Ω → ℝ := fun s q => ψ q.1 * (L s q.1 q.2 - L t q.1 q.2)
  let H : ℝ → Plane → ℝ := fun s x => ∫ ω, ‖F s (x, ω)‖ ∂P
  let J : ℝ → Ω → ℝ := fun s ω => ∫ x, F s (x, ω)
  have hψ : Integrable (fun x => |ψ x|) :=
    ψ.continuous.abs.integrable_of_hasCompactSupport ψ.hasCompactSupport.abs
  have hDiffInt (s : ℝ) (hs : s ∈ Set.Icc a b) (x : Plane) :
      Integrable (fun ω => L s x ω - L t x ω) P :=
    ((hbound s hs.1 hs.2 x).1.integrable (by norm_num)).sub
      ((hbound t hat.le htb.le x).1.integrable (by norm_num))
  have hDiffBound (s : ℝ) (hs : s ∈ Set.Icc a b) (x : Plane) :
      (∫ ω, |L s x ω - L t x ω| ∂P) ≤ 2 * K := by
    have hb : eLpNorm (fun ω => L s x ω - L t x ω) 1 P ≤ ENNReal.ofReal (2 * K) := by
      refine (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
        ((eLpNorm_sub_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans ?_)
      refine (add_le_add (hbound s hs.1 hs.2 x).2 (hbound t hat.le htb.le x).2).trans_eq ?_
      rw [← ENNReal.ofReal_add hK hK]
      congr 1
      ring
    rw [eLpNorm_one_eq_integral_abs P (hDiffInt s hs x)] at hb
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 2 * K)).mp hb
  have hFm (s : ℝ) (hs : 0 < s) : AEStronglyMeasurable (F s) (volume.prod P) := by
    have hslog := aemeasurable_log_cutoffPairing_joint ϑ P Z hZ hs hr (fun y => Real.exp (h y))
      (Real.measurable_exp.comp h.continuous.measurable) (fun y => (Real.exp_pos _).le)
    have htlog := aemeasurable_log_cutoffPairing_joint ϑ P Z hZ ht hr (fun y => Real.exp (h y))
      (Real.measurable_exp.comp h.continuous.measurable) (fun y => (Real.exp_pos _).le)
    exact (ψ.continuous.measurable.comp measurable_fst).aestronglyMeasurable.mul
      (hslog.aestronglyMeasurable.sub htlog.aestronglyMeasurable)
  have hHeq (s : ℝ) (x : Plane) : H s x = |ψ x| * (∫ ω, |L s x ω - L t x ω| ∂P) := by
    simp only [H, F, norm_mul, Real.norm_eq_abs, integral_const_mul]
  have hHb (s : ℝ) (hs : s ∈ Set.Icc a b) (x : Plane) : H s x ≤ |ψ x| * (2 * K) := by
    rw [hHeq]
    exact mul_le_mul_of_nonneg_left (hDiffBound s hs x) (abs_nonneg _)
  have hHi (s : ℝ) (hs : s ∈ Set.Icc a b) : Integrable (H s) := by
    apply (hψ.mul_const (2 * K)).mono' ((hFm s (ha.trans_le hs.1)).norm.integral_prod_right')
    exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (integral_nonneg fun ω => norm_nonneg _)]
      exact hHb s hs x
  have hPi (s : ℝ) (hs : s ∈ Set.Icc a b) : Integrable (F s) (volume.prod P) := by
    apply (integrable_prod_iff (hFm s (ha.trans_le hs.1))).mpr
    exact ⟨Eventually.of_forall fun x => (hDiffInt s hs x).const_mul (ψ x), hHi s hs⟩
  have hHx (x : Plane) : Tendsto (fun s => H s x) (𝓝 t) (𝓝 0) := by
    have hc := log_heat_end_L1_time_of_uniform_bound ϑ P Z hZ h ha hr K hbound hat htb x
    have hi : ∀ᶠ s in 𝓝 t, Integrable (fun ω => L s x ω - L t x ω) P := by
      filter_upwards [Ioo_mem_nhds hat htb] with s hs
      exact hDiffInt s ⟨hs.1.le, hs.2.le⟩ x
    have hc' := (tendsto_integral_abs_of_L1 P hi hc).const_mul |ψ x|
    simpa only [hHeq, mul_zero] using hc'
  have htotal : Tendsto (fun s => ∫ x, H s x) (𝓝 t) (𝓝 0) := by
    have hc : Tendsto (fun s => ∫ x, H s x) (𝓝 t) (𝓝 (∫ _ : Plane, (0 : ℝ))) := by
      apply tendsto_integral_filter_of_dominated_convergence (bound := fun x => |ψ x| * (2 * K))
      · filter_upwards [Ioo_mem_nhds hat htb] with s hs
        exact (hHi s ⟨hs.1.le, hs.2.le⟩).aestronglyMeasurable
      · filter_upwards [Ioo_mem_nhds hat htb] with s hs
        exact Eventually.of_forall fun x => by
          rw [Real.norm_of_nonneg (integral_nonneg fun ω => norm_nonneg _)]
          exact hHb s ⟨hs.1.le, hs.2.le⟩ x
      · exact hψ.mul_const _
      · exact Eventually.of_forall hHx
    simpa only [integral_zero] using hc
  have hJb (s : ℝ) (hs : s ∈ Set.Icc a b) : eLpNorm (J s) 1 P ≤ ENNReal.ofReal (∫ x, H s x) := by
    rw [eLpNorm_one_eq_integral_abs P (hPi s hs).integral_prod_right]
    apply ENNReal.ofReal_le_ofReal
    calc
      (∫ ω, |J s ω| ∂P) ≤ ∫ ω, (∫ x, ‖F s (x, ω)‖) ∂P := by
        apply integral_mono_ae ((hPi s hs).integral_prod_right.abs) (hPi s hs).norm.integral_prod_right
        exact Eventually.of_forall fun ω => by
          simpa only [J, Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => F s (x, ω))
      _ = ∫ x, H s x := (integral_integral_swap (hPi s hs).norm).symm
  have hJ : Tendsto (fun s => eLpNorm (J s) 1 P) (𝓝 t) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa only [ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.tendsto 0 |>.comp htotal)
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [Ioo_mem_nhds hat htb] with s hs
    exact hJb s ⟨hs.1.le, hs.2.le⟩
  apply hJ.congr'
  filter_upwards [Ioi_mem_nhds ht] with s hs
  apply eLpNorm_congr_ae
  filter_upwards [ae_integrable_testFn_mul_log_cutoffPairing ϑ P Z hZ hs hr ψ,
    ae_integrable_testFn_mul_log_cutoffPairing ϑ P Z hZ ht hr ψ] with ω hi hi'
  change (∫ x, ψ x * (L s x ω - L t x ω)) = (∫ x, ψ x * L s x ω) - (∫ x, ψ x * L t x ω)
  simp only [mul_sub]
  exact integral_sub (hi h) (hi' h)

/-- The spatial centring is an integrable constant multiple of the test. -/
theorem ae_spatialCenteredPairing_eq_raw_sub_mean (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (h : Plane →ᵇ ℝ) (ψ : TestFn) :
    ∀ᵐ ω ∂P, spatialCenteredPairing P Z t r h ψ ω =
      (∫ x, ψ x * Real.log (shfPairing Z 0 t (fun y => Real.exp (h y)) (fun y => heatKernel r (y - x)) ω)) -
      (∫ x, ψ x) * (∫ ω', Real.log (shfPairing Z 0 t (fun _ => 1) (heatKernel r) ω') ∂P) := by
  filter_upwards [ae_integrable_testFn_mul_log_cutoffPairing ϑ P Z hZ ht hr ψ] with ω hi
  let c := ∫ ω', Real.log (shfPairing Z 0 t (fun _ => 1) (heatKernel r) ω') ∂P
  have hc : Integrable (fun x => ψ x * c) :=
    (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).mul_const c
  simp only [spatialCenteredPairing, mul_sub]
  rw [integral_sub (hi h) hc, integral_mul_const]

/-- Removing the common centring preserves the tested L¹ time continuity. -/
theorem spatial_centered_L1_time_of_bounds (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (h : Plane →ᵇ ℝ) (ψ : TestFn) {a b r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (K K₀ : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ u : ℝ, a ≤ u → u ≤ b → ∀ x : Plane,
      MemLp (fun ω => Real.log (shfPairing Z 0 u (fun y => Real.exp (h y)) (fun y => heatKernel r (y - x)) ω)) 2 P ∧
      eLpNorm (fun ω => Real.log (shfPairing Z 0 u (fun y => Real.exp (h y)) (fun y => heatKernel r (y - x)) ω)) 2 P ≤ ENNReal.ofReal K)
    (hbound₀ : ∀ u : ℝ, a ≤ u → u ≤ b → ∀ x : Plane,
      MemLp (fun ω => Real.log (shfPairing Z 0 u (fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) (fun y => heatKernel r (y - x)) ω)) 2 P ∧
      eLpNorm (fun ω => Real.log (shfPairing Z 0 u (fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) (fun y => heatKernel r (y - x)) ω)) 2 P ≤ ENNReal.ofReal K₀)
    {t : ℝ} (hat : a < t) (htb : t < b) :
    Tendsto (fun s => eLpNorm (fun ω => spatialCenteredPairing P Z s r h ψ ω -
      spatialCenteredPairing P Z t r h ψ ω) 1 P) (𝓝 t) (𝓝 0) := by
  have ht : 0 < t := ha.trans hat
  let A : ℝ := ∫ x, ψ x
  let c : ℝ → ℝ := fun s => ∫ ω, Real.log (shfPairing Z 0 s (fun _ => 1) (heatKernel r) ω) ∂P
  let V : ℝ → Ω → ℝ := fun s ω => ∫ x, ψ x * Real.log (shfPairing Z 0 s
    (fun y => Real.exp (h y)) (fun y => heatKernel r (y - x)) ω)
  have hV := tested_log_heat_end_L1_time ϑ P Z hZ h ψ ha hr K hK hbound hat htb
  have hcLp := log_heat_end_L1_time_of_uniform_bound ϑ P Z hZ (0 : Plane →ᵇ ℝ) ha hr K₀ hbound₀ hat htb 0
  simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero, sub_zero] at hcLp
  have hci : ∀ᶠ s in 𝓝 t, Integrable (fun ω => Real.log (shfPairing Z 0 s (fun _ => 1) (heatKernel r) ω)) P := by
    filter_upwards [Ioo_mem_nhds hat htb] with s hs
    have hi := (hbound₀ s hs.1.le hs.2.le 0).1.integrable (by norm_num)
    simpa only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero, sub_zero] using hi
  have hc : Tendsto c (𝓝 t) (𝓝 (c t)) := tendsto_integral_of_L1' _ hci hcLp
  have hc' : Tendsto (fun s => A * (c s - c t)) (𝓝 t) (𝓝 0) := by
    simpa only [sub_self, mul_zero] using (hc.sub (tendsto_const_nhds : Tendsto (fun _ : ℝ => c t) (𝓝 t) (𝓝 (c t)))).const_mul A
  have hCn : Tendsto (fun s => eLpNorm (fun _ : Ω => A * (c s - c t)) 1 P) (𝓝 t) (𝓝 0) := by
    have hn (s : ℝ) : eLpNorm (fun _ : Ω => A * (c s - c t)) 1 P = ENNReal.ofReal |A * (c s - c t)| := by
      rw [eLpNorm_const' _ (by norm_num) (by simp)]
      simp only [measure_univ, ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal_abs]
    simp_rw [hn]
    have hca : Tendsto (fun s => |A * (c s - c t)|) (𝓝 t) (𝓝 0) := by
      simpa only [abs_zero] using hc'.abs
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hca
  have hb (s : ℝ) (hs : 0 < s) :
      eLpNorm (fun ω => spatialCenteredPairing P Z s r h ψ ω - spatialCenteredPairing P Z t r h ψ ω) 1 P ≤
      eLpNorm (fun ω => V s ω - V t ω) 1 P + eLpNorm (fun _ : Ω => A * (c s - c t)) 1 P := by
    have heq : (fun ω => spatialCenteredPairing P Z s r h ψ ω - spatialCenteredPairing P Z t r h ψ ω) =ᵐ[P]
        (fun ω => (V s ω - V t ω) - A * (c s - c t)) := by
      filter_upwards [ae_spatialCenteredPairing_eq_raw_sub_mean ϑ P Z hZ hs hr h ψ,
        ae_spatialCenteredPairing_eq_raw_sub_mean ϑ P Z hZ ht hr h ψ] with ω hω hω'
      rw [hω, hω']
      change (V s ω - A * c s) - (V t ω - A * c t) = (V s ω - V t ω) - A * (c s - c t)
      ring
    rw [eLpNorm_congr_ae heq]
    exact eLpNorm_sub_le (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [add_zero] using hV.add hCn) (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact hb s hs

/-- All sufficiently small fixed regularizations are L¹-continuous in their time parameter. -/
theorem exists_regularized_L1_time_width (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (t : ℝ) (ht : 0 < t) (h : Plane →ᵇ ℝ) (ψ : TestFn) :
    ∃ δ₀ > 0, ∀ r : ℝ, 0 < r → r < δ₀ →
      Tendsto (fun s => eLpNorm (fun ω =>
        (∫ x, ψ x * kpzRegularized P Z s r h x ω) - (∫ x, ψ x * kpzRegularized P Z t r h x ω)) 1 P)
        (𝓝 t) (𝓝 0) := by
  obtain ⟨d, hd, hb⟩ := heat_end_profile_log_uniform_L2_bound ϑ P Z hZ h (b := t + 1) (half_pos ht)
  obtain ⟨d₀, hd₀, hb₀⟩ := heat_end_profile_log_uniform_L2_bound ϑ P Z hZ (0 : Plane →ᵇ ℝ)
    (b := t + 1) (half_pos ht)
  refine ⟨min d (min d₀ (t / 4)), lt_min hd (lt_min hd₀ (by positivity)), ?_⟩
  intro r hr hrd
  obtain ⟨K, hK, hKb⟩ := hb r hr (hrd.trans_le (min_le_left _ _)).le
  obtain ⟨K₀, _hK₀, hK₀b⟩ := hb₀ r hr (hrd.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hrt : r < t / 4 := hrd.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hc := spatial_centered_L1_time_of_bounds ϑ P Z hZ h ψ (half_pos ht) hr K K₀ hK hKb hK₀b
    (t := t - r) (by linarith) (by linarith)
  have hshift : Tendsto (fun s : ℝ => s - r) (𝓝 t) (𝓝 (t - r)) :=
    (continuous_id.sub continuous_const).tendsto t
  simpa only [Function.comp_def, spatialCenteredPairing_eq_integral_kpzRegularized, sub_add_cancel] using hc.comp hshift

/-- Tested values of any critical KPZ version are L¹-continuous at positive times. -/
theorem tendsto_eLpNorm_H_time (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) (h : Plane →ᵇ ℝ) (ψ : TestFn) :
    Tendsto (fun s => eLpNorm (fun ω => H s h ω ψ - H t h ω ψ) 1 P) (𝓝 t) (𝓝 0) := by
  apply tendsto_zero_of_real_bounds
  intro ε hε
  obtain ⟨d, hd, hrate⟩ := kpzRegularized_uniform_L2_rate ϑ P Z hZ H hH h ψ
    (t₀ := t / 2) (t₁ := t + 1) (half_pos ht) (by linarith) (ε / 3) (by positivity)
  obtain ⟨d₀, hd₀, hcont⟩ := exists_regularized_L1_time_width ϑ P Z hZ t ht h ψ
  let r : ℝ := min d d₀ / 2
  have hr : 0 < r := half_pos (lt_min hd hd₀)
  have hrd : r < d := (half_lt_self (lt_min hd hd₀)).trans_le (min_le_left _ _)
  have hrd₀ : r < d₀ := (half_lt_self (lt_min hd hd₀)).trans_le (min_le_right _ _)
  have happrox (u : ℝ) (hlo : t / 2 ≤ u) (hhi : u ≤ t + 1) :
      eLpNorm (fun ω => H u h ω ψ - (∫ x, ψ x * kpzRegularized P Z u r h x ω)) 1 P ≤ ENNReal.ofReal (ε / 3) := by
    calc
      _ = eLpNorm (fun ω => (∫ x, ψ x * kpzRegularized P Z u r h x ω) - H u h ω ψ) 1 P :=
        eLpNorm_sub_comm _ _ _ _
      _ ≤ eLpNorm (fun ω => (∫ x, ψ x * kpzRegularized P Z u r h x ω) - H u h ω ψ) 2 P :=
        eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
      _ ≤ _ := hrate r hr hrd u hlo hhi
  have hmid : ∀ᶠ s in 𝓝 t, eLpNorm (fun ω =>
      (∫ x, ψ x * kpzRegularized P Z s r h x ω) - (∫ x, ψ x * kpzRegularized P Z t r h x ω)) 1 P ≤
        ENNReal.ofReal (ε / 3) :=
    ENNReal.tendsto_nhds_zero.mp (hcont r hr hrd₀) _ (by positivity)
  filter_upwards [hmid, Ioo_mem_nhds (half_lt_self ht) (lt_add_one t)] with s hmid hs
  refine (eLpNorm_sub_le_three P (fun ω => H s h ω ψ)
    (fun ω => ∫ x, ψ x * kpzRegularized P Z s r h x ω)
    (fun ω => ∫ x, ψ x * kpzRegularized P Z t r h x ω) (fun ω => H t h ω ψ)).trans
    ((add_le_add (add_le_add (happrox s hs.1.le hs.2.le) hmid) (happrox t (by linarith) (by linarith))).trans ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  linarith


end Critical2DKPZ.Extensions.Response
