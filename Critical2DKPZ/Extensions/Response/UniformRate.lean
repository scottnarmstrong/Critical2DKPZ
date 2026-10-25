/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.Common.Canonical
public import Critical2DKPZ.Assembly.RootInputs
import Critical2DKPZ.JointConvergence.KPZRegularizedReverseLaw
import Critical2DKPZ.JointConvergence.ThmToyJointLimit
import Critical2DKPZ.SHF.Symmetries.LatticeReversal
import Mathlib.Probability.IdentDistrib
import Mathlib.Tactic

/-! # Uniform forward L² approximation on positive compact time intervals

Two widths must be transported jointly through reversal. Their difference has
an invariant L² norm; the fixed-time L² limit then identifies the forward field.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BoundedContinuousFunction ENNReal Topology
namespace Critical2DKPZ.Extensions.Response

/-- A reversed tested regularization is measurable at every admissible width,
including reversed starting time zero. -/
theorem aemeasurable_tested_reversed (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {u T δ : ℝ} (hu : 0 ≤ u) (hδ : 0 < δ) (hδT : δ < T - u)
    (h : Plane →ᵇ ℝ) (ψ : TestFn) :
    AEMeasurable (fun ω => ∫ x, ψ x * kpzRegularizedReversed P Z u T δ h x ω) P := by
  let μ : Ω → Measure (Plane × Plane) := fun ω => Z (u + δ) T ω
  have hμ : Measurable μ := hZ.1 (u + δ) T (by linarith) (by linarith)
  have hlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
    filter_upwards [hZ.2.1 (u + δ) T (by linarith) (by linarith)] with ω hω
    exact hω.1
  exact JointConvergence.aemeasurable_integral_log_heatPairing P μ hμ hlocal δ
    (∫ ω', Real.log (shfPairing Z (u + δ) T
      (fun y => heatKernel δ y) (fun _ => 1) ω') ∂P)
    hδ (fun y => Real.exp (h y)) ψ
    (Real.measurable_exp.comp h.continuous.measurable)
    (fun y => (Real.exp_pos _).le) ψ.continuous.measurable

/-- Equality in law of two widths preserves the norm of their difference. -/
theorem eLpNorm_regularized_sub_eq_reversed (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {s T δ δ' : ℝ} (hsT : s ≤ T) (hδ : 0 < δ) (hδs : δ < s)
    (hδ' : 0 < δ') (hδ's : δ' < s) (h : Plane →ᵇ ℝ) (ψ : TestFn) :
    eLpNorm (fun ω => (∫ x, ψ x * kpzRegularized P Z s δ h x ω) -
      (∫ x, ψ x * kpzRegularized P Z s δ' h x ω)) 2 P =
    eLpNorm (fun ω => (∫ x, ψ x * kpzRegularizedReversed P Z (T - s) T δ h x ω) -
      (∫ x, ψ x * kpzRegularizedReversed P Z (T - s) T δ' h x ω)) 2 P := by
  let d : Fin 2 → ℝ := ![δ, δ']
  have hd (i : Fin 2) : 0 < d i ∧ d i < s ∧ s ≤ T := by
    fin_cases i
    · exact ⟨hδ, hδs, hsT⟩
    · exact ⟨hδ', hδ's, hsT⟩
  have hF : AEMeasurable (fun ω (i : Fin 2) => ∫ x, ψ x * kpzRegularized P Z s (d i) h x ω) P :=
    aemeasurable_pi_iff.mpr fun i =>
      JointConvergence.aemeasurable_integral_kpzRegularized ϑ P Z hZ s (d i) (hd i).2.1 (hd i).1 h ψ
  have hR : AEMeasurable (fun ω (i : Fin 2) => ∫ x, ψ x * kpzRegularizedReversed P Z (T - s) T (d i) h x ω) P :=
    aemeasurable_pi_iff.mpr fun i => aemeasurable_tested_reversed ϑ P Z hZ
      (sub_nonneg.mpr hsT) (hd i).1 (by linarith [(hd i).2.1]) h ψ
  have hID : IdentDistrib
      (fun ω (i : Fin 2) => ∫ x, ψ x * kpzRegularized P Z s (d i) h x ω)
      (fun ω (i : Fin 2) => ∫ x, ψ x * kpzRegularizedReversed P Z (T - s) T (d i) h x ω) P P :=
    ⟨hF, hR, JointConvergence.kpzRegularized_reverse_law_of ϑ P Z hZ T
      (SHF.Symmetries.isCriticalSHF_reverse_fdd ϑ P Z hZ T)
      2 (fun _ => s) d (fun _ => h) (fun _ => ψ) hd⟩
  exact (hID.comp ((measurable_pi_apply 0).sub (measurable_pi_apply 1))).eLpNorm_eq 2

/-- The logarithmic rate tends to zero at any fixed positive time scale. -/
theorem tendsto_log_rate (a C : ℝ) (ha : 0 < a) :
    Tendsto (fun δ : ℝ => C * |Real.log (δ / a)| ^ (-(1 : ℝ) / 40))
      (𝓝[>] 0) (𝓝 0) := by
  have hratio : Tendsto (fun δ : ℝ => δ / a) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [id_eq, zero_div] using
        ((tendsto_id : Tendsto (fun δ : ℝ => δ) (𝓝 (0 : ℝ)) (𝓝 0)).mono_left
          nhdsWithin_le_nhds).div_const a
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact div_pos hδ ha
  have hlog := tendsto_abs_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hratio)
  have hpow := (tendsto_rpow_neg_atTop (y := (1 : ℝ) / 40) (by norm_num)).comp hlog
  simpa only [Function.comp_def, neg_div, mul_zero] using hpow.const_mul C

/-- The inverse logarithmic rate is largest at the lower time endpoint. -/
theorem log_rate_le_at_lower {a s δ : ℝ} (ha : 0 < a) (has : a ≤ s)
    (hδ : 0 < δ) (hδa : δ < a) :
    |Real.log (δ / s)| ^ (-(1 : ℝ) / 40) ≤ |Real.log (δ / a)| ^ (-(1 : ℝ) / 40) := by
  have hs : 0 < s := ha.trans_le has
  have hlogA : Real.log (δ / a) < 0 := Real.log_neg (div_pos hδ ha) ((div_lt_one ha).mpr hδa)
  have hlogS : Real.log (δ / s) < 0 := Real.log_neg (div_pos hδ hs)
    ((div_lt_one hs).mpr (hδa.trans_le has))
  have hlog : |Real.log (δ / a)| ≤ |Real.log (δ / s)| := by
    rw [abs_of_neg hlogA, abs_of_neg hlogS]
    exact neg_le_neg (Real.log_le_log (div_pos hδ hs)
      (div_le_div_of_nonneg_left hδ.le ha has))
  exact Real.rpow_le_rpow_of_nonpos (abs_pos.mpr hlogA.ne) hlog (by norm_num)

/-- The forward regularizations approximate any critical KPZ version uniformly
on a compact interval of positive times. -/
theorem kpzRegularized_uniform_L2_rate (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (h : Plane →ᵇ ℝ) (ψ : TestFn) {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₀ ≤ t₁) :
    ∀ ε > 0, ∃ δ₁ > 0, ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∀ s : ℝ, t₀ ≤ s → s ≤ t₁ →
      eLpNorm (fun ω => (∫ x, ψ x * kpzRegularized P Z s δ h x ω) - H s h ω ψ) 2 P ≤ ENNReal.ofReal ε := by
  obtain ⟨X, _hXm, hRate, _⟩ := Assembly.toyJointAt_of_isCriticalSHF ϑ P Z hZ t₁ (ht₀.trans_le ht₁)
  obtain ⟨C, d, hd, hbound⟩ := hRate h ψ t₀ ht₀ ht₁
  let C₀ := max C 0
  have hC₀ : 0 ≤ C₀ := le_max_right _ _
  intro ε hε
  have hevent : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      C₀ * |Real.log (δ / t₀)| ^ (-(1 : ℝ) / 40) < ε / 4 :=
    (tendsto_log_rate t₀ C₀ ht₀).eventually (Iio_mem_nhds (by linarith))
  obtain ⟨d', hd', hd'bound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  let D := min d (min t₀ d')
  have hD : 0 < D := lt_min hd (lt_min ht₀ hd')
  have hsmall (δ : ℝ) (hδ : 0 < δ) (hδD : δ < D) (s : ℝ) (has : t₀ ≤ s) (hsT : s ≤ t₁) :
      eLpNorm (fun ω => (∫ x, ψ x * kpzRegularizedReversed P Z (t₁ - s) t₁ δ h x ω) -
        X (t₁ - s) h ψ ω) 2 P ≤ ENNReal.ofReal (ε / 4) := by
    have hδd : δ < d := hδD.trans_le (min_le_left _ _)
    have hδa : δ < t₀ := hδD.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hδd' : δ < d' := hδD.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hb := hbound δ hδ hδd (t₁ - s) (sub_nonneg.mpr hsT) (by linarith)
    have hscale : t₁ - (t₁ - s) = s := by ring
    rw [hscale] at hb
    refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
    calc
      C * |Real.log (δ / s)| ^ (-(1 : ℝ) / 40) ≤
          C₀ * |Real.log (δ / s)| ^ (-(1 : ℝ) / 40) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _)
      _ ≤ C₀ * |Real.log (δ / t₀)| ^ (-(1 : ℝ) / 40) :=
        mul_le_mul_of_nonneg_left (log_rate_le_at_lower ht₀ has hδ hδa) hC₀
      _ ≤ ε / 4 := (hd'bound ⟨hδ, hδd'⟩).le
  refine ⟨D, hD, ?_⟩
  intro δ hδ hδD s has hsT
  have hs : 0 < s := ht₀.trans_le has
  have hconv := Common.tendsto_eLpNorm_kpzRegularized_isCriticalKPZ
    ϑ P Z hZ H hH s hs h ψ 2 (by norm_num) (by simp)
  have hevent' : ∀ᶠ δ' : ℝ in 𝓝[>] 0,
      eLpNorm (fun ω => (∫ x, ψ x * kpzRegularized P Z s δ' h x ω) - H s h ω ψ) 2 P <
        ENNReal.ofReal (ε / 2) := hconv.eventually (Iio_mem_nhds (by positivity))
  have hDmem : ∀ᶠ δ' : ℝ in 𝓝[>] 0, δ' < D :=
    nhdsWithin_le_nhds (Iio_mem_nhds hD)
  have hposmem : ∀ᶠ δ' : ℝ in 𝓝[>] 0, 0 < δ' := self_mem_nhdsWithin
  obtain ⟨δ', hδ', hδ'D, hnorm⟩ :=
    (hposmem.and (hDmem.and hevent')).exists
  have hδs : δ < s := hδD.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans has))
  have hδ's : δ' < s := hδ'D.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans has))
  have hdiff : eLpNorm (fun ω => (∫ x, ψ x * kpzRegularized P Z s δ h x ω) -
      (∫ x, ψ x * kpzRegularized P Z s δ' h x ω)) 2 P ≤
        ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) := by
    rw [eLpNorm_regularized_sub_eq_reversed ϑ P Z hZ hsT hδ hδs hδ' hδ's h ψ]
    have heq (ω : Ω) :
        (∫ x, ψ x * kpzRegularizedReversed P Z (t₁ - s) t₁ δ h x ω) -
        (∫ x, ψ x * kpzRegularizedReversed P Z (t₁ - s) t₁ δ' h x ω) =
        ((∫ x, ψ x * kpzRegularizedReversed P Z (t₁ - s) t₁ δ h x ω) - X (t₁ - s) h ψ ω) -
        ((∫ x, ψ x * kpzRegularizedReversed P Z (t₁ - s) t₁ δ' h x ω) - X (t₁ - s) h ψ ω) := by ring
    simp_rw [heq]
    exact (eLpNorm_sub_le (by norm_num)).trans
      (add_le_add (hsmall δ hδ hδD s has hsT) (hsmall δ' hδ' hδ'D s has hsT))
  have heq (ω : Ω) :
      (∫ x, ψ x * kpzRegularized P Z s δ h x ω) - H s h ω ψ =
      ((∫ x, ψ x * kpzRegularized P Z s δ h x ω) - (∫ x, ψ x * kpzRegularized P Z s δ' h x ω)) +
      ((∫ x, ψ x * kpzRegularized P Z s δ' h x ω) - H s h ω ψ) := by ring
  simp_rw [heq]
  refine (eLpNorm_add_le (by norm_num)).trans ((add_le_add hdiff hnorm.le).trans ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  linarith

end Critical2DKPZ.Extensions.Response
