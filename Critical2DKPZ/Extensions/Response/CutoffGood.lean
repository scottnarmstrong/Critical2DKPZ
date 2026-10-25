/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.TestFn
public import Critical2DKPZ.CovarianceKernel.PointwiseMoments
public import Critical2DKPZ.SHF.Positivity.HeatPairingEhrhard
public import Critical2DKPZ.SHF.Symmetries.LatticeReversal
import Mathlib.Tactic

/-! # Good events for terminally smoothed heat-flow pairings

Heat-start properties are transported using equality in law of the endpoint
swapped measure. Gaussian domination then gives all spatial centres on one event.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped BoundedContinuousFunction ENNReal Topology
namespace Critical2DKPZ.Extensions.Response

/-- Gaussian shift domination. Proof adapted from the private lemma in
`Assembly.Comparison`; the uniform constant is independent of `y`. -/
theorem heatKernel_shift_le {δ : ℝ} (hδ : 0 < δ) (x y : Plane) {R : ℝ}
    (hR : ‖x‖ ≤ R) :
    heatKernel δ (y - x) ≤ 2 * Real.exp (R ^ 2 / (2 * δ)) * heatKernel (2 * δ) y := by
  have hn : ‖y‖ ^ 2 ≤ 2 * ‖y - x‖ ^ 2 + 2 * ‖x‖ ^ 2 := by
    have h1 : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by simpa using norm_add_le (y - x) x
    have h2 : ‖y‖ ^ 2 ≤ (‖y - x‖ + ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖y - x‖ - ‖x‖)]
  have hR2 : ‖x‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hR 2
  have hexp : Real.exp (-‖y - x‖ ^ 2 / (2 * δ)) ≤
      Real.exp (R ^ 2 / (2 * δ)) * Real.exp (-‖y‖ ^ 2 / (2 * (2 * δ))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have e1 : -‖y - x‖ ^ 2 / (2 * δ) = -(‖y - x‖ ^ 2) * (1 / (2 * δ)) := by ring
    have e2 : R ^ 2 / (2 * δ) + -‖y‖ ^ 2 / (2 * (2 * δ)) =
        (R ^ 2 - ‖y‖ ^ 2 / 2) * (1 / (2 * δ)) := by field_simp; ring
    rw [e1, e2]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    nlinarith
  have hc : (2 * Real.pi * δ)⁻¹ = 2 * (2 * Real.pi * (2 * δ))⁻¹ := by
    field_simp
  unfold heatKernel
  calc (2 * Real.pi * δ)⁻¹ * Real.exp (-‖y - x‖ ^ 2 / (2 * δ))
      ≤ (2 * Real.pi * δ)⁻¹ *
        (Real.exp (R ^ 2 / (2 * δ)) * Real.exp (-‖y‖ ^ 2 / (2 * (2 * δ)))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by rw [hc]; ring


/-- Endpoint swapping preserves the law of a fixed positive-time SHF measure. -/
theorem cutoff_swap_law (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t : ℝ} (ht : 0 < t) :
    P.map (fun ω => (Z 0 t ω).map Prod.swap) = P.map (Z 0 t) := by
  exact CovarianceKernel.shfInterval_map_swap_law_of ϑ P Z hZ
    (SHF.Symmetries.isCriticalSHF_reverse_fdd ϑ P Z hZ) ht

/-- The uncentred nonnegative heat-start integral is a measurable function of a measure. -/
theorem measurable_heat_mass (r : ℝ) (hr : 0 < r) (x : Plane) :
    Measurable (fun μ : Measure (Plane × Plane) =>
      ∫ p, heatKernel r (p.1 - x) ∂μ) := by
  have hm : Measurable (fun μ : Measure (Plane × Plane) =>
      ∫⁻ p, ENNReal.ofReal (heatKernel r (p.1 - x)) ∂μ) :=
    Measure.measurable_lintegral
    (ENNReal.measurable_ofReal.comp
      ((measurable_heatKernel r).comp (measurable_fst.sub_const x)))
  have heq (μ : Measure (Plane × Plane)) :
      (∫ p, heatKernel r (p.1 - x) ∂μ) =
        (∫⁻ p, ENNReal.ofReal (heatKernel r (p.1 - x)) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun p => heatKernel_nonneg hr.le (p.1 - x))
      (((measurable_heatKernel r).comp (measurable_fst.sub_const x)).aestronglyMeasurable)
  simp_rw [heq]
  exact hm.ennreal_toReal

/-- A fixed terminal heat kernel is integrable against the flow almost surely. -/
theorem ae_integrable_heat_end (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (x : Plane) :
    ∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane => heatKernel r (p.2 - x)) (Z 0 t ω) := by
  have hk : Measurable (fun p : Plane × Plane => heatKernel r (p.1 - x)) :=
    (measurable_heatKernel r).comp (measurable_fst.sub_const x)
  have hE : MeasurableSet {μ : Measure (Plane × Plane) |
      Integrable (fun p => heatKernel r (p.1 - x)) μ} := by
    have heq : {μ : Measure (Plane × Plane) |
        Integrable (fun p => heatKernel r (p.1 - x)) μ} =
        {μ | ∫⁻ p, ‖heatKernel r (p.1 - x)‖ₑ ∂μ < ⊤} := by
      ext μ
      simp only [Set.mem_ofPred_eq, Integrable, HasFiniteIntegral,
        and_iff_right hk.aestronglyMeasurable]
    rw [heq]
    exact measurableSet_lt (Measure.measurable_lintegral hk.enorm) measurable_const
  have hmeas := hZ.1 0 t le_rfl ht
  have hsource := SHF.Positivity.isCriticalSHF_ae_integrable_heat_start
    ϑ P Z hZ le_rfl ht hr x
  have hsourceLaw := (ae_map_iff hmeas.aemeasurable hE).2 hsource
  rw [← cutoff_swap_law ϑ P Z hZ ht] at hsourceLaw
  have hswap := ae_of_ae_map
    ((Measure.measurable_map Prod.swap measurable_swap).comp hmeas).aemeasurable hsourceLaw
  filter_upwards [hswap] with ω hω
  exact (integrable_map_measure hk.aestronglyMeasurable measurable_swap.aemeasurable).mp hω

/-- The terminal flat heat pairing has strictly positive mass almost surely. -/
theorem ae_heat_end_pos (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    ∀ᵐ ω ∂P, 0 < shfPairing Z 0 t (fun _ => 1) (heatKernel r) ω := by
  let F : Measure (Plane × Plane) → ℝ := fun μ => ∫ p, heatKernel r p.1 ∂μ
  have hF : Measurable F := by simpa [F] using measurable_heat_mass r hr 0
  have hpos : ∀ᵐ ω ∂P, 0 < F (Z 0 t ω) := by
    simpa [F, shfPairing] using
      (SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType
        ϑ P Z hZ 0 t r 0 0 le_rfl ht hr).1
  have hmeas := hZ.1 0 t le_rfl ht
  have hlaw := cutoff_swap_law ϑ P Z hZ ht
  have hposLaw : ∀ᵐ μ ∂P.map (Z 0 t), 0 < F μ :=
    (ae_map_iff hmeas.aemeasurable (hF measurableSet_Ioi)).2 hpos
  rw [← hlaw] at hposLaw
  have hswap := ae_of_ae_map
    ((Measure.measurable_map Prod.swap measurable_swap).comp hmeas).aemeasurable hposLaw
  filter_upwards [hswap] with ω hω
  have hmap := integral_map (μ := Z 0 t ω) measurable_swap.aemeasurable
    (((measurable_heatKernel r).comp measurable_fst).aestronglyMeasurable)
  dsimp [F] at hω
  have heq : (∫ p, heatKernel r p.1 ∂((Z 0 t ω).map Prod.swap)) =
      ∫ p, heatKernel r p.2 ∂(Z 0 t ω) := hmap
  rw [heq] at hω
  simpa only [shfPairing, one_mul] using hω

/-- A single full-probability event controls every spatial centre and positive mass. -/
theorem ae_cutoff_good (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (t : ℝ) (ht : 0 < t) (r : ℝ) (hr : 0 < r) :
    ∀ᵐ ω ∂P, (∀ x : Plane,
      Integrable (fun p : Plane × Plane => heatKernel r (p.2 - x)) (Z 0 t ω)) ∧
      0 < shfPairing Z 0 t (fun _ => 1) (heatKernel r) ω := by
  filter_upwards [ae_integrable_heat_end ϑ P Z hZ ht (by positivity : 0 < 2 * r) 0,
    ae_heat_end_pos ϑ P Z hZ ht hr] with ω hint hpos
  refine ⟨fun x => ?_, hpos⟩
  have hint' : Integrable (fun p : Plane × Plane => heatKernel (2 * r) p.2) (Z 0 t ω) := by
    simpa only [sub_zero] using hint
  refine (hint'.const_mul (2 * Real.exp (‖x‖ ^ 2 / (2 * r)))).mono'
    (((measurable_heatKernel r).comp (measurable_snd.sub_const x)).aestronglyMeasurable)
    (Eventually.of_forall fun p => ?_)
  rw [Real.norm_of_nonneg (heatKernel_nonneg hr.le _)]
  exact heatKernel_shift_le hr x p.2 le_rfl

/-- A bounded continuous weight preserves integrability of any terminal heat kernel. -/
theorem integrable_weighted_heat {μ : Measure (Plane × Plane)} {r : ℝ}
    (hr : 0 < r) (x : Plane)
    (hint : Integrable (fun p : Plane × Plane => heatKernel r (p.2 - x)) μ)
    {g : Plane → ℝ} (hg : Continuous g) {C : ℝ} (hgb : ∀ y, |g y| ≤ C) :
    Integrable (fun p : Plane × Plane => g p.1 * heatKernel r (p.2 - x)) μ := by
  refine (hint.const_mul C).mono'
    ((hg.comp continuous_fst).mul
      ((continuous_heatKernel r).comp (continuous_snd.sub continuous_const))).aestronglyMeasurable
    (Eventually.of_forall fun p => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (heatKernel_nonneg hr.le _)]
  exact mul_le_mul_of_nonneg_right (hgb p.1) (heatKernel_nonneg hr.le _)

/-- A doubled-width Gaussian majorant controls every shift at the original width. -/
theorem integrable_heat_shift {μ : Measure (Plane × Plane)} {r : ℝ}
    (hr : 0 < r)
    (hint : Integrable (fun p : Plane × Plane => heatKernel (2 * r) p.2) μ) (x : Plane) :
    Integrable (fun p : Plane × Plane => heatKernel r (p.2 - x)) μ := by
  refine (hint.const_mul (2 * Real.exp (‖x‖ ^ 2 / (2 * r)))).mono'
    (((measurable_heatKernel r).comp (measurable_snd.sub_const x)).aestronglyMeasurable)
    (Eventually.of_forall fun p => ?_)
  rw [Real.norm_of_nonneg (heatKernel_nonneg hr.le _)]
  exact heatKernel_shift_le hr x p.2 le_rfl

/-- Spatial continuity from the note's doubled-width heat integrability condition.
The bound on `g` permits signed bounded continuous weights. -/
theorem continuous_pairing_x {μ : Measure (Plane × Plane)} {r : ℝ}
    (hr : 0 < r)
    (hint : Integrable (fun p : Plane × Plane => heatKernel (2 * r) p.2) μ)
    {g : Plane → ℝ} (hg : Continuous g) {C : ℝ} (hgb : ∀ y, |g y| ≤ C) :
    Continuous (fun x : Plane => ∫ p, g p.1 * heatKernel r (p.2 - x) ∂μ) := by
  have hC : 0 ≤ C := (abs_nonneg (g 0)).trans (hgb 0)
  rw [continuous_iff_continuousAt]
  intro x₀
  have hc : ContinuousOn (fun x : Plane => ∫ p, g p.1 * heatKernel r (p.2 - x) ∂μ)
      (Metric.closedBall 0 (‖x₀‖ + 1)) := by
    refine continuousOn_of_dominated
      (bound := fun p => (C * (2 * Real.exp ((‖x₀‖ + 1) ^ 2 / (2 * r)))) *
        heatKernel (2 * r) p.2) ?_ ?_ ?_ ?_
    · intro x _
      exact ((hg.comp continuous_fst).mul
        ((continuous_heatKernel r).comp (continuous_snd.sub continuous_const))).aestronglyMeasurable
    · intro x hx
      refine Eventually.of_forall fun p => ?_
      have hx' : ‖x‖ ≤ ‖x₀‖ + 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
      rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (heatKernel_nonneg hr.le _)]
      calc
        |g p.1| * heatKernel r (p.2 - x) ≤ C * heatKernel r (p.2 - x) :=
          mul_le_mul_of_nonneg_right (hgb p.1) (heatKernel_nonneg hr.le _)
        _ ≤ C * (2 * Real.exp ((‖x₀‖ + 1) ^ 2 / (2 * r)) * heatKernel (2 * r) p.2) :=
          mul_le_mul_of_nonneg_left (heatKernel_shift_le hr x p.2 hx') hC
        _ = _ := by ring
    · exact hint.const_mul _
    · exact Eventually.of_forall fun p =>
        (continuous_const.mul ((continuous_heatKernel r).comp
          (continuous_const.sub continuous_id))).continuousOn
  refine hc.continuousAt (Filter.mem_of_superset (Metric.ball_mem_nhds x₀ one_pos) ?_)
  intro y hy
  have hdist : ‖y - x₀‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
  have hnorm : ‖y‖ ≤ ‖y - x₀‖ + ‖x₀‖ := by simpa only [sub_add_cancel] using norm_add_le (y - x₀) x₀
  simp only [Metric.mem_closedBall, dist_zero_right]
  linarith only [hdist, hnorm]

/-- A strictly positive bounded weight has a positive pairing against any nonzero measure
on which the terminal heat kernels are integrable. Boundedness is necessary because
nonintegrable Bochner integrals are totalized to zero. -/
theorem pairing_pos {μ : Measure (Plane × Plane)} {r : ℝ}
    (hr : 0 < r)
    (hint : ∀ x, Integrable (fun p : Plane × Plane => heatKernel r (p.2 - x)) μ)
    (hμ : 0 < ∫ p, heatKernel r p.2 ∂μ)
    {g : Plane → ℝ} (hg : Continuous g) {C : ℝ} (hgb : ∀ y, |g y| ≤ C)
    (hpos : ∀ y, 0 < g y) (x : Plane) :
    0 < ∫ p, g p.1 * heatKernel r (p.2 - x) ∂μ := by
  have hne : μ ≠ 0 := by
    intro hzero
    simp only [hzero, integral_zero_measure, lt_self_iff_false] at hμ
  have hi := integrable_weighted_heat hr x (hint x) hg hgb
  have hnn : 0 ≤ (fun p : Plane × Plane => g p.1 * heatKernel r (p.2 - x)) :=
    fun p => mul_nonneg (hpos p.1).le (heatKernel_nonneg hr.le _)
  rw [integral_pos_iff_support_of_nonneg hnn hi]
  have hs : Function.support (fun p : Plane × Plane => g p.1 * heatKernel r (p.2 - x)) = Set.univ := by
    ext p
    simp only [Function.mem_support, mul_ne_zero_iff, Set.mem_univ, iff_true]
    exact ⟨(hpos p.1).ne', (heatKernel_pos hr _).ne'⟩
  rw [hs]
  exact Measure.measure_univ_pos.mpr hne

/-- The logarithmic pairing against a smooth compactly supported test is integrable. -/
theorem integrable_testFn_mul_log_pairing {μ : Measure (Plane × Plane)} {r : ℝ}
    (hr : 0 < r)
    (hint : Integrable (fun p : Plane × Plane => heatKernel (2 * r) p.2) μ)
    (hμ : 0 < ∫ p, heatKernel r p.2 ∂μ)
    {g : Plane → ℝ} (hg : Continuous g) {C : ℝ} (hgb : ∀ y, |g y| ≤ C)
    (hpos : ∀ y, 0 < g y) (ψ : TestFn) :
    Integrable (fun x => ψ x * Real.log (∫ p, g p.1 * heatKernel r (p.2 - x) ∂μ)) := by
  have hc := (continuous_pairing_x hr hint hg hgb).log
    (fun x => (pairing_pos hr (integrable_heat_shift hr hint) hμ hg hgb hpos x).ne')
  exact (ψ.continuous.mul hc).integrable_of_hasCompactSupport (ψ.hasCompactSupport.mul_right)

/-- Uniform bound for the exponential initial profile. -/
theorem exp_profile_bound (h : Plane →ᵇ ℝ) (y : Plane) :
    |Real.exp (h y)| ≤ Real.exp ‖h‖ := by
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr ((Real.le_norm_self _).trans (h.norm_coe_le_norm y))

end Critical2DKPZ.Extensions.Response
