/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Assembly.RegularizedComparison
public import Critical2DKPZ.LocalSobolev.Inputs
public import Critical2DKPZ.SHF.Symmetries.LatticeReversal
import Mathlib.Tactic

/-! # Comparison for the critical KPZ process (the KPZ comparison principle) -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BoundedContinuousFunction Topology

universe u

namespace Critical2DKPZ.Assembly

open Critical2DKPZ.LocalSobolev Critical2DKPZ.SHF.Limit

/-- Pointwise comparison of a shifted heat kernel with the heat kernel at doubled time:
`g_δ(y - x) ≤ 2 e^{R²/(2δ)} g_{2δ}(y)` whenever `|x| ≤ R`. -/
private theorem heatKernel_shift_le {δ : ℝ} (hδ : 0 < δ) (x y : Plane) {R : ℝ}
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

/-- The pairing integrand `e^{h(x)} g_δ(y - z)`, as a function on the plane pair, is continuous. -/
private theorem continuous_pairingIntegrand (h : Plane →ᵇ ℝ) (δ : ℝ) (z : Plane) :
    Continuous (fun p : Plane × Plane => Real.exp (h p.1) * heatKernel δ (p.2 - z)) :=
  (Real.continuous_exp.comp (h.continuous.comp continuous_fst)).mul
    ((continuous_heatKernel δ).comp (continuous_snd.sub continuous_const))

/-- If `e^{h} ⊗ g_{2δ}` is integrable then so is every shift `e^{h} ⊗ g_δ(· - x)`. -/
private theorem integrable_shift {μ : Measure (Plane × Plane)} (h : Plane →ᵇ ℝ) {δ : ℝ}
    (hδ : 0 < δ)
    (hint : Integrable (fun p : Plane × Plane => Real.exp (h p.1) * heatKernel (2 * δ) p.2) μ)
    (x : Plane) :
    Integrable (fun p : Plane × Plane => Real.exp (h p.1) * heatKernel δ (p.2 - x)) μ := by
  refine (hint.const_mul (2 * Real.exp (‖x‖ ^ 2 / (2 * δ)))).mono'
    (continuous_pairingIntegrand h δ x).aestronglyMeasurable
    (Eventually.of_forall fun p => ?_)
  have h0 : 0 ≤ Real.exp (h p.1) * heatKernel δ (p.2 - x) :=
    mul_nonneg (Real.exp_pos _).le (heatKernel_nonneg hδ.le _)
  rw [Real.norm_of_nonneg h0]
  calc Real.exp (h p.1) * heatKernel δ (p.2 - x)
      ≤ Real.exp (h p.1) * (2 * Real.exp (‖x‖ ^ 2 / (2 * δ)) * heatKernel (2 * δ) p.2) :=
        mul_le_mul_of_nonneg_left (heatKernel_shift_le hδ x p.2 le_rfl) (Real.exp_pos _).le
    _ = _ := by ring

/-- The pairing of `e^{h}` with `g_δ(· - x)` is continuous in the centre `x`. -/
private theorem continuous_pairing_shift {μ : Measure (Plane × Plane)} (h : Plane →ᵇ ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hint : Integrable (fun p : Plane × Plane => Real.exp (h p.1) * heatKernel (2 * δ) p.2) μ) :
    Continuous (fun x : Plane =>
      ∫ p, Real.exp (h p.1) * heatKernel δ (p.2 - x) ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro x0
  have hc : ContinuousOn (fun x : Plane =>
      ∫ p, Real.exp (h p.1) * heatKernel δ (p.2 - x) ∂μ) (Metric.closedBall 0 (‖x0‖ + 1)) := by
    refine continuousOn_of_dominated
      (bound := fun p => 2 * Real.exp ((‖x0‖ + 1) ^ 2 / (2 * δ)) *
        (Real.exp (h p.1) * heatKernel (2 * δ) p.2)) ?_ ?_ ?_ ?_
    · intro x _
      exact (continuous_pairingIntegrand h δ x).aestronglyMeasurable
    · intro x hx
      refine Eventually.of_forall fun p => ?_
      have hx' : ‖x‖ ≤ ‖x0‖ + 1 := by simpa using hx
      have h0 : 0 ≤ Real.exp (h p.1) * heatKernel δ (p.2 - x) :=
        mul_nonneg (Real.exp_pos _).le (heatKernel_nonneg hδ.le _)
      rw [Real.norm_of_nonneg h0]
      calc Real.exp (h p.1) * heatKernel δ (p.2 - x)
          ≤ Real.exp (h p.1) *
            (2 * Real.exp ((‖x0‖ + 1) ^ 2 / (2 * δ)) * heatKernel (2 * δ) p.2) :=
            mul_le_mul_of_nonneg_left (heatKernel_shift_le hδ x p.2 hx') (Real.exp_pos _).le
        _ = _ := by ring
    · exact hint.const_mul _
    · refine Eventually.of_forall fun p => ?_
      exact (continuous_const.mul ((continuous_heatKernel δ).comp
        (continuous_const.sub continuous_id))).continuousOn
  refine hc.continuousAt (Filter.mem_of_superset (Metric.ball_mem_nhds x0 one_pos) ?_)
  intro y hy
  have : ‖y - x0‖ < 1 := by simpa [dist_eq_norm] using hy
  have h1 : ‖y‖ ≤ ‖y - x0‖ + ‖x0‖ := by simpa using norm_add_le (y - x0) x0
  simp only [Metric.mem_closedBall, dist_zero_right]
  linarith

/-- A nonzero measure with integrable doubled pairing has strictly positive heat pairings. -/
private theorem pairing_pos {μ : Measure (Plane × Plane)} (h : Plane →ᵇ ℝ) {δ : ℝ}
    (hδ : 0 < δ)
    (hint : Integrable (fun p : Plane × Plane => Real.exp (h p.1) * heatKernel (2 * δ) p.2) μ)
    (hμ : μ ≠ 0) (x : Plane) :
    0 < ∫ p, Real.exp (h p.1) * heatKernel δ (p.2 - x) ∂μ := by
  have hi := integrable_shift h hδ hint x
  have hnn : 0 ≤ fun p : Plane × Plane => Real.exp (h p.1) * heatKernel δ (p.2 - x) :=
    fun p => mul_nonneg (Real.exp_pos _).le (heatKernel_nonneg hδ.le _)
  rw [integral_pos_iff_support_of_nonneg hnn hi]
  have hs : Function.support
      (fun p : Plane × Plane => Real.exp (h p.1) * heatKernel δ (p.2 - x)) = Set.univ := by
    ext p
    simp [Function.mem_support, (Real.exp_pos _).ne', (heatKernel_pos hδ _).ne']
  rw [hs]
  exact Measure.measure_univ_pos.2 hμ

/-- The regularized field is continuous in the spatial variable, on the good event. -/
private theorem continuous_field {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t δ : ℝ) (hδ : 0 < δ) (h : Plane →ᵇ ℝ) (ω : Ω)
    (hint : Integrable (fun p : Plane × Plane =>
      Real.exp (h p.1) * heatKernel (2 * δ) p.2) (Z 0 (t - δ) ω))
    (hne : Z 0 (t - δ) ω ≠ 0) :
    Continuous (fun x => kpzRegularized P Z t δ h x ω) := by
  unfold kpzRegularized
  refine Continuous.sub ?_ continuous_const
  exact Continuous.log (continuous_pairing_shift h hδ hint)
    (fun x => (pairing_pos h hδ hint hne x).ne')

/-- Deterministic comparison of the tested regularized fields on the good event. -/
private theorem tested_comparison {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t δ : ℝ) (hδ : 0 < δ) (h₀ h₀' : Plane →ᵇ ℝ)
    (ψ : TestFn) (ω : Ω)
    (hint₀ : Integrable (fun p : Plane × Plane =>
      Real.exp (h₀ p.1) * heatKernel (2 * δ) p.2) (Z 0 (t - δ) ω))
    (hint₀' : Integrable (fun p : Plane × Plane =>
      Real.exp (h₀' p.1) * heatKernel (2 * δ) p.2) (Z 0 (t - δ) ω))
    (hne : Z 0 (t - δ) ω ≠ 0) :
    |(∫ x, ψ x * kpzRegularized P Z t δ h₀ x ω) -
        ∫ x, ψ x * kpzRegularized P Z t δ h₀' x ω| ≤
      (∫ x, |ψ x|) * ‖h₀ - h₀'‖ := by
  have hI : ∀ (h : Plane →ᵇ ℝ), Integrable (fun p : Plane × Plane =>
      Real.exp (h p.1) * heatKernel (2 * δ) p.2) (Z 0 (t - δ) ω) →
      Integrable (fun x => ψ x * kpzRegularized P Z t δ h x ω) := by
    intro h hh
    have hc := continuous_field P Z t δ hδ h ω hh hne
    exact (ψ.continuous.mul hc).integrable_of_hasCompactSupport
      (ψ.hasCompactSupport.mul_right)
  have hψ : Integrable (fun x => |ψ x|) :=
    ψ.continuous.abs.integrable_of_hasCompactSupport ψ.hasCompactSupport.abs
  rw [← integral_sub (hI h₀ hint₀) (hI h₀' hint₀')]
  have hpos : 0 < ∫ p, Real.exp (h₀' p.1) * heatKernel δ (p.2 - 0) ∂(Z 0 (t - δ) ω) :=
    pairing_pos h₀' hδ hint₀' hne 0
  calc |∫ x, (ψ x * kpzRegularized P Z t δ h₀ x ω - ψ x * kpzRegularized P Z t δ h₀' x ω)|
      = ‖∫ x, (ψ x * kpzRegularized P Z t δ h₀ x ω - ψ x * kpzRegularized P Z t δ h₀' x ω)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, |ψ x| * ‖h₀ - h₀'‖ := by
        refine norm_integral_le_of_norm_le (hψ.mul_const _) (Eventually.of_forall fun x => ?_)
        have hx := kpzRegularized_comparison P Z t δ h₀ h₀' x ω
          (pairing_pos h₀' hδ hint₀' hne x) (integrable_shift h₀' hδ hint₀' x)
        rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    _ = (∫ x, |ψ x|) * ‖h₀ - h₀'‖ := integral_mul_const _ _

/-- Integrability of a fixed measurable function is a measurable property of the measure. -/
private theorem measurableSet_integrable {α : Type*} [MeasurableSpace α] {f : α → ℝ}
    (hf : Measurable f) : MeasurableSet {μ : Measure α | Integrable f μ} := by
  have : {μ : Measure α | Integrable f μ} = {μ | ∫⁻ a, ‖f a‖ₑ ∂μ < ⊤} := by
    ext μ
    simp only [Set.mem_ofPred_eq, Integrable, HasFiniteIntegral,
      and_iff_right hf.aestronglyMeasurable]
  rw [this]
  exact measurableSet_lt (Measure.measurable_lintegral hf.enorm) measurable_const

/-- The exponential of a bounded continuous function, as a bounded continuous function. -/
private def expBCF (h : Plane →ᵇ ℝ) : Plane →ᵇ ℝ :=
  ⟨⟨fun y => Real.exp (h y), Real.continuous_exp.comp h.continuous⟩,
    ⟨Real.exp ‖h‖, fun x y => by
      have hx : Real.exp (h x) ≤ Real.exp ‖h‖ :=
        Real.exp_le_exp.mpr ((Real.le_norm_self _).trans (h.norm_coe_le_norm x))
      have hy : Real.exp (h y) ≤ Real.exp ‖h‖ :=
        Real.exp_le_exp.mpr ((Real.le_norm_self _).trans (h.norm_coe_le_norm y))
      have hx0 := Real.exp_pos (h x)
      have hy0 := Real.exp_pos (h y)
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith⟩⟩

/-- Almost surely the doubled-heat pairing of `e^{h}` is integrable (heat on the second
coordinate), and the measure `Z 0 (t - δ)` is nonzero. -/
private theorem good_ae (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hHeatBoundedPairingInput : HeatBoundedPairingAt ϑ P Z)
    (t δ : ℝ) (hδ : 0 < δ) (hδt : δ < t) (h : Plane →ᵇ ℝ) :
    ∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane =>
        Real.exp (h p.1) * heatKernel (2 * δ) p.2) (Z 0 (t - δ) ω) ∧ Z 0 (t - δ) ω ≠ 0 := by
  have hT : 0 < t - δ := by linarith
  refine Filter.Eventually.and ?_ ?_
  · -- integrability, by reversal
    have h25 := (hHeatBoundedPairingInput (s := 0) (t := t - δ) (δ := 2 * δ) le_rfl hT (by linarith) 0
      (expBCF h)).1
    have hrev := SHF.Symmetries.isCriticalSHF_reverse_fdd ϑ P Z hZ (t - δ) 1 (fun _ => 0)
      (fun _ => t - δ) (fun _ => ⟨le_rfl, hT, le_rfl⟩)
    simp only [sub_self, sub_zero] at hrev
    let S : Set (Fin 1 → Measure (Plane × Plane)) := {m | Integrable
      (fun p : Plane × Plane => heatKernel (2 * δ) (p.1 - 0) * (expBCF h) p.2) (m 0)}
    have hfm : Measurable (fun p : Plane × Plane =>
        heatKernel (2 * δ) (p.1 - 0) * (expBCF h) p.2) :=
      ((continuous_heatKernel _).comp (continuous_fst.sub continuous_const)).measurable.mul
        ((expBCF h).continuous.comp continuous_snd).measurable
    have hS : MeasurableSet S := by
      have : S = (fun m : Fin 1 → Measure (Plane × Plane) => m 0) ⁻¹'
          {μ | Integrable (fun p : Plane × Plane =>
            heatKernel (2 * δ) (p.1 - 0) * (expBCF h) p.2) μ} := rfl
      rw [this]
      exact (measurable_pi_apply 0) (measurableSet_integrable hfm)
    have hFm : Measurable (fun ω (i : Fin 1) => (Z 0 (t - δ) ω).map Prod.swap) :=
      measurable_pi_iff.2 fun _ =>
        (Measure.measurable_map Prod.swap measurable_swap).comp (hZ.1 0 (t - δ) le_rfl hT)
    have hGm : Measurable (fun ω (i : Fin 1) => Z 0 (t - δ) ω) :=
      measurable_pi_iff.2 fun _ => hZ.1 0 (t - δ) le_rfl hT
    have hG : ∀ᵐ m ∂(P.map (fun ω (i : Fin 1) => Z 0 (t - δ) ω)), m ∈ S :=
      (ae_map_iff hGm.aemeasurable hS).2 h25
    rw [← hrev] at hG
    have hF := (ae_map_iff hFm.aemeasurable hS).1 hG
    filter_upwards [hF] with ω hω
    have hω' : Integrable (fun p : Plane × Plane =>
        heatKernel (2 * δ) (p.1 - 0) * (expBCF h) p.2) ((Z 0 (t - δ) ω).map Prod.swap) := hω
    rw [integrable_map_measure hfm.aestronglyMeasurable measurable_swap.aemeasurable] at hω'
    refine hω'.congr (Eventually.of_forall fun p => ?_)
    simp [expBCF, mul_comm, Function.comp]
  · filter_upwards [(hsym.2.2.2.2.2.2 0 (t - δ) δ 0 h le_rfl hT hδ).1] with ω hω hzero
    rw [shfPairing, hzero] at hω
    simp at hω

/-- The grid `δₙ = t / (n + 2)` lies in `(0, t)` and tends to `0⁺`. -/
private theorem grid_tendsto (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => t / ((n : ℝ) + 2)) atTop (nhdsWithin 0 (Set.Ioi 0)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
  · exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  · exact div_pos ht (by positivity)

/-- Regularized and limiting KPZ test pairings differ by at most the initial-data
sup norm times the test’s L¹ norm, under SHF symmetry and heat-pairing hypotheses.
The regularized test pairings are almost surely integrable by `good_ae`. -/
theorem criticalKPZ_comparison_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hHeatBoundedPairingInput : HeatBoundedPairingAt ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) (h₀ h₀' : Plane →ᵇ ℝ) (hL : ∃ L, LipschitzWith L h₀)
    (hL' : ∃ L, LipschitzWith L h₀') (ψ : TestFn) :
    (∀ δ, 0 < δ → δ < t → ∀ᵐ ω ∂P,
      |(∫ x, ψ x * kpzRegularized P Z t δ h₀ x ω) - ∫ x, ψ x * kpzRegularized P Z t δ h₀' x ω| ≤
        (∫ x, |ψ x|) * ‖h₀ - h₀'‖) ∧
    ∀ᵐ ω ∂P, |H t h₀ ω ψ - H t h₀' ω ψ| ≤ (∫ x, |ψ x|) * ‖h₀ - h₀'‖ := by
  -- The comparison holds without the additional Lipschitz hypotheses.
  have _ := hL
  have _ := hL'
  have hfirst : ∀ δ, 0 < δ → δ < t → ∀ᵐ ω ∂P,
      |(∫ x, ψ x * kpzRegularized P Z t δ h₀ x ω) -
        ∫ x, ψ x * kpzRegularized P Z t δ h₀' x ω| ≤ (∫ x, |ψ x|) * ‖h₀ - h₀'‖ := by
    intro δ hδ hδt
    filter_upwards [good_ae ϑ P Z hZ hsym hHeatBoundedPairingInput t δ hδ hδt h₀,
      good_ae ϑ P Z hZ hsym hHeatBoundedPairingInput t δ hδ hδt h₀'] with ω hω hω'
    exact tested_comparison P Z t δ hδ h₀ h₀' ψ ω hω.1 hω'.1 hω.2
  refine ⟨hfirst, ?_⟩
  set u : ℕ → ℝ := fun n => t / ((n : ℝ) + 2) with hu
  have hu0 : ∀ n, 0 < u n := fun n => div_pos ht (by positivity)
  have hut : ∀ n, u n < t := fun n => by
    rw [hu]
    exact div_lt_self ht (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hgrid := grid_tendsto t ht
  have hseq : ∀ h : Plane →ᵇ ℝ, TendstoInMeasure P
      (fun (n : ℕ) ω => ∫ x, ψ x * kpzRegularized P Z t (u n) h x ω) atTop
      (fun ω => H t h ω ψ) := fun h ε hε => (hH t ht h ψ ε hε).comp hgrid
  obtain ⟨ns, hns, hae⟩ := (hseq h₀).exists_seq_tendsto_ae
  have hseq' : TendstoInMeasure P
      (fun (n : ℕ) ω => ∫ x, ψ x * kpzRegularized P Z t (u (ns n)) h₀' x ω) atTop
      (fun ω => H t h₀' ω ψ) := fun ε hε => (hseq h₀' ε hε).comp hns.tendsto_atTop
  obtain ⟨ms, hms, hae'⟩ := hseq'.exists_seq_tendsto_ae
  have hbound : ∀ᵐ ω ∂P, ∀ n, |(∫ x, ψ x * kpzRegularized P Z t (u (ns (ms n))) h₀ x ω) -
      ∫ x, ψ x * kpzRegularized P Z t (u (ns (ms n))) h₀' x ω| ≤
        (∫ x, |ψ x|) * ‖h₀ - h₀'‖ :=
    ae_all_iff.2 fun n => hfirst _ (hu0 _) (hut _)
  filter_upwards [hae, hae', hbound] with ω h1 h2 h3
  have h1' := h1.comp hms.tendsto_atTop
  exact le_of_tendsto ((h1'.sub h2).abs) (Eventually.of_forall h3)

end Critical2DKPZ.Assembly
