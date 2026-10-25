/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Positivity.CompactConvergence
public import Critical2DKPZ.SHF.Positivity.LawFatou
public import Critical2DKPZ.Definitions.ShfPairing
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Tactic

/-! # Integrability of heat-start pairings under a critical SHF -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported ENNReal Topology

namespace Critical2DKPZ.SHF.Positivity

private theorem integrable_cC_of_locallyFinite {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] [T2Space α] (μ : Measure α)
    (hμ : IsLocallyFiniteMeasure μ) (f : C_c(α, ℝ)) : Integrable (f : α → ℝ) μ := by
  have hK : IsCompact (tsupport (f : α → ℝ)) := f.hasCompactSupport
  have hfinite : IsFiniteMeasureOnCompacts μ :=
    @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure α _ _ _ hμ
  have hKfinite : μ (tsupport (f : α → ℝ)) < ∞ := hfinite.lt_top_of_isCompact hK
  have hOn := f.continuous_toFun.continuousOn.integrableOn_of_subset_isCompact
    hK hK.measurableSet Set.Subset.rfl hKfinite.ne
  exact (integrableOn_iff_integrable_of_support_subset
    (subset_tsupport (f : α → ℝ))).mp hOn

private theorem polymer_heatCutoff_pairing_integrable (ϑ : ℝ) (N : ℕ) (s t δ : ℝ)
    (x : Plane) (R : ℝ) :
    Integrable (fun ω : Disorder =>
      ∫ p, heatCutoffTest δ x R p ∂(polymerMeasure ϑ N s t ω)) disorderLaw := by
  have hprod := SHF.Moments.integrable_pairing_rescaledP2P ϑ N s t
    (heatCutoffTest δ x R).continuous_toFun
    (heatCutoffTest δ x R).hasCompactSupport'
  have hswap := hprod.swap
  have hCden : Integrable (fun ω : Disorder =>
      ∫ p, heatCutoffTest δ x R p * rescaledP2P ϑ N s t p ω ∂volume) disorderLaw :=
    hswap.integral_prod_left
  apply hCden.congr
  filter_upwards [] with ω
  exact (integral_polymerMeasure ϑ N s t ω (heatCutoffTest δ x R)).symm

private theorem polymer_heatCutoff_pairing_mean_le_one (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    {s t δ : ℝ} (hδ : 0 < δ) (x : Plane) (R : ℝ) :
    Integrable (fun ω : Disorder =>
      ∫ p, heatCutoffTest δ x R p ∂(polymerMeasure ϑ N s t ω)) disorderLaw ∧
    ∫ ω, ∫ p, heatCutoffTest δ x R p ∂(polymerMeasure ϑ N s t ω) ∂disorderLaw ≤ 1 := by
  have hCint := polymer_heatCutoff_pairing_integrable ϑ N s t δ x R
  have hA := integral_polymer_heat_start_pairing_eq_one ϑ hN s t δ hδ x
  have hpair : ∀ᵐ ω ∂disorderLaw,
      (∫ p, heatCutoffTest δ x R p ∂(polymerMeasure ϑ N s t ω)) ≤
        ∫ p, heatKernel δ (p.1 - x) ∂(polymerMeasure ϑ N s t ω) := by
    filter_upwards [ae_integrable_polymer_heat_start ϑ hN s t δ hδ x] with ω hAω
    have hCω : Integrable (fun p : Plane × Plane => heatCutoffTest δ x R p)
        (polymerMeasure ϑ N s t ω) := by
      apply hAω.mono'
        (heatCutoffTest δ x R).continuous_toFun.measurable.aestronglyMeasurable
      filter_upwards [] with p
      have h1 := ballCutoff_mem_Icc R p.1
      have h2 := ballCutoff_mem_Icc R p.2
      have hk := heatKernel_nonneg hδ.le (p.1 - x)
      change ‖heatCutoffTest δ x R p‖ ≤ heatKernel δ (p.1 - x)
      rw [Real.norm_eq_abs]
      dsimp [heatCutoffTest]
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg hk h1.1) h2.1)]
      calc
        heatKernel δ (p.1 - x) * ballCutoff R p.1 * ballCutoff R p.2 ≤
            heatKernel δ (p.1 - x) * ballCutoff R p.1 * 1 :=
          mul_le_mul_of_nonneg_left h2.2 (mul_nonneg hk h1.1)
        _ = heatKernel δ (p.1 - x) * ballCutoff R p.1 := by ring
        _ ≤ heatKernel δ (p.1 - x) * 1 := mul_le_mul_of_nonneg_left h1.2 hk
        _ = heatKernel δ (p.1 - x) := by ring
    have hle (p : Plane × Plane) : heatCutoffTest δ x R p ≤ heatKernel δ (p.1 - x) := by
      have h1 := ballCutoff_mem_Icc R p.1
      have h2 := ballCutoff_mem_Icc R p.2
      have hk := heatKernel_nonneg hδ.le (p.1 - x)
      dsimp [heatCutoffTest]
      calc
        heatKernel δ (p.1 - x) * ballCutoff R p.1 * ballCutoff R p.2 ≤
            heatKernel δ (p.1 - x) * ballCutoff R p.1 * 1 :=
          mul_le_mul_of_nonneg_left h2.2 (mul_nonneg hk h1.1)
        _ = heatKernel δ (p.1 - x) * ballCutoff R p.1 := by ring
        _ ≤ heatKernel δ (p.1 - x) * 1 := mul_le_mul_of_nonneg_left h1.2 hk
        _ = heatKernel δ (p.1 - x) := by ring
    exact integral_mono hCω hAω hle
  have hmean := integral_mono_ae hCint hA.1 hpair
  refine ⟨hCint, ?_⟩
  calc
    (∫ ω, ∫ p, heatCutoffTest δ x R p ∂(polymerMeasure ϑ N s t ω) ∂disorderLaw) ≤
        ∫ ω, ∫ p, heatKernel δ (p.1 - x) ∂(polymerMeasure ϑ N s t ω) ∂disorderLaw := hmean
    _ = 1 := hA.2

private theorem polymer_heatCutoff_pairing_lintegral_le_one (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    {s t δ : ℝ} (hδ : 0 < δ) (x : Plane) (R : ℝ) :
    ∫⁻ ω, ENNReal.ofReal
      (∫ p, heatCutoffTest δ x R p ∂(polymerMeasure ϑ N s t ω)) ∂disorderLaw ≤ 1 := by
  have hmean := @polymer_heatCutoff_pairing_mean_le_one ϑ N hN s t δ hδ x R
  have hnonneg : 0 ≤ ∫ ω, ∫ p, heatCutoffTest δ x R p
      ∂(polymerMeasure ϑ N s t ω) ∂disorderLaw :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω =>
      integral_nonneg_of_ae (Filter.Eventually.of_forall fun p => by
        have h1 := ballCutoff_mem_Icc R p.1
        have h2 := ballCutoff_mem_Icc R p.2
        exact mul_nonneg (mul_nonneg (heatKernel_nonneg hδ.le _) h1.1) h2.1))
  rw [← ofReal_integral_eq_lintegral_ofReal hmean.1
    (Filter.Eventually.of_forall fun ω => integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun p => by
        have h1 := ballCutoff_mem_Icc R p.1
        have h2 := ballCutoff_mem_Icc R p.2
        exact mul_nonneg (mul_nonneg (heatKernel_nonneg hδ.le _) h1.1) h2.1))]
  simpa using ENNReal.ofReal_le_ofReal hmean.2

/-- Every compact cutoff of the limiting heat-start has annealed mass at most one. -/
private theorem isCriticalSHF_heatCutoff_lintegral_le_one (ϑ : ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {s t δ : ℝ} (hs : 0 ≤ s) (hst : s < t) (hδ : 0 < δ) (x : Plane) (R : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (∫ p, heatCutoffTest δ x R p ∂(Z s t ω)) ∂P ≤ 1 := by
  have hfatou := isCriticalSHF_lintegral_pairing_le_liminf ϑ P Z hZ hs hst
    (heatCutoffTest δ x R) (fun p => by
      have h1 := ballCutoff_mem_Icc R p.1
      have h2 := ballCutoff_mem_Icc R p.2
      exact mul_nonneg (mul_nonneg (heatKernel_nonneg hδ.le _) h1.1) h2.1)
  have hpoly : ∀ᶠ N : ℕ in atTop, ∫⁻ ω, ENNReal.ofReal
      (∫ p, heatCutoffTest δ x R p ∂(polymerMeasure ϑ N s t ω)) ∂disorderLaw ≤ 1 := by
    filter_upwards [Filter.eventually_atTop.2 ⟨1, fun N hN => hN⟩] with N hN
    exact @polymer_heatCutoff_pairing_lintegral_le_one ϑ N hN s t δ hδ x R
  calc
    _ ≤ atTop.liminf (fun N : ℕ => ∫⁻ ω, ENNReal.ofReal
        (∫ p, heatCutoffTest δ x R p ∂(polymerMeasure ϑ N s t ω)) ∂disorderLaw) := hfatou
    _ ≤ 1 := by
      refine liminf_le_of_le (by isBoundedDefault) (fun b hb => ?_)
      obtain ⟨N, hNb⟩ := (hb.and hpoly).exists
      exact hNb.1.trans hNb.2

/-- The heat-start mass of every critical SHF is integrable in disorder and has mean at most one. -/
private theorem isCriticalSHF_heat_start_lintegral_bound (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) {s t δ : ℝ} (hs : 0 ≤ s) (hst : s < t) (hδ : 0 < δ)
    (x : Plane) :
    ∫⁻ ω, ∫⁻ p, ENNReal.ofReal (heatKernel δ (p.1 - x)) ∂(Z s t ω) ∂P ≤ 1 := by
  let A : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ p, ENNReal.ofReal (heatKernel δ (p.1 - x)) ∂(Z s t ω)
  let s₁ : Fin 1 → ℝ := fun _ => s
  let t₁ : Fin 1 → ℝ := fun _ => t
  have htimes : ∀ i : Fin 1, 0 ≤ s₁ i ∧ s₁ i < t₁ i := by
    intro i
    exact ⟨hs, hst⟩
  have hlocal := hZ.2.1 s t hs hst
  have hheatMeas : Measurable (fun p : Plane × Plane =>
      ENNReal.ofReal (heatKernel δ (p.1 - x))) := by
    exact ENNReal.measurable_ofReal.comp
      ((measurable_heatKernel δ).comp (measurable_fst.sub_const x))
  have hAmeas : Measurable A := by
    dsimp [A]
    exact (Measure.measurable_lintegral hheatMeas).comp (hZ.1 s t hs hst)
  let hseq : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ENNReal.ofReal (∫ p, heatCutoffTest δ x (n : ℝ) p ∂(Z s t ω))
  let hφn : ℕ → Fin 1 → C_c(Plane × Plane, ℝ) := fun n _ =>
    heatCutoffTest δ x (n : ℝ)
  have hdist (n : ℕ) : TendstoInDistribution
      (fun N ω i => ∫ p, hφn n i p ∂(polymerMeasure ϑ N (s₁ i) (t₁ i) ω)) atTop
      (fun ω i => ∫ p, hφn n i p ∂(Z (s₁ i) (t₁ i) ω))
      (fun _ => disorderLaw) P :=
    isCriticalSHF_compact_pairings_tendsto P Z hZ s₁ t₁ htimes (hφn n)
  have hseqMeas (n : ℕ) : AEMeasurable (hseq n) P := by
    have hread := (hdist n).continuous_comp
      (g := fun v : Fin 1 → ℝ => v 0) (by fun_prop)
    have hscalar : TendstoInDistribution
        (fun N ω => ∫ p, heatCutoffTest δ x (n : ℝ) p
          ∂(polymerMeasure ϑ N s t ω)) atTop
        (fun ω => ∫ p, heatCutoffTest δ x (n : ℝ) p ∂(Z s t ω))
        (fun _ => disorderLaw) P := by
      dsimp only [Function.comp, hφn, s₁, t₁] at hread
      exact hread
    change AEMeasurable (fun ω => ENNReal.ofReal
      (∫ p, heatCutoffTest δ x (n : ℝ) p ∂(Z s t ω))) P
    exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable hscalar.aemeasurable_limit
  have hstep : ∀ n, ∀ᵐ ω ∂P, hseq n ω ≤ hseq (n + 1) ω := by
    intro n
    filter_upwards [hlocal] with ω hω
    have hIn (m : ℕ) : Integrable
        (fun p : Plane × Plane => heatCutoffTest δ x (m : ℝ) p) (Z s t ω) := by
      exact integrable_cC_of_locallyFinite (Z s t ω) hω.1 (heatCutoffTest δ x (m : ℝ))
    have htest (p : Plane × Plane) :
        heatCutoffTest δ x (n : ℝ) p ≤ heatCutoffTest δ x ((n + 1 : ℕ) : ℝ) p := by
      have hn : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
      have hc1 := ballCutoff_mono_radius hn p.1
      have hc2 := ballCutoff_mono_radius hn p.2
      have hk := heatKernel_nonneg hδ.le (p.1 - x)
      change heatKernel δ (p.1 - x) * ballCutoff (n : ℝ) p.1 * ballCutoff (n : ℝ) p.2 ≤ _
      calc
        heatKernel δ (p.1 - x) * ballCutoff (n : ℝ) p.1 * ballCutoff (n : ℝ) p.2 =
            heatKernel δ (p.1 - x) * (ballCutoff (n : ℝ) p.1 * ballCutoff (n : ℝ) p.2) := by ring
        _ ≤ heatKernel δ (p.1 - x) *
              (ballCutoff ((n + 1 : ℕ) : ℝ) p.1 * ballCutoff (n : ℝ) p.2) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hc1 (ballCutoff_mem_Icc (n : ℝ) p.2).1) hk
        _ = heatKernel δ (p.1 - x) * ballCutoff ((n + 1 : ℕ) : ℝ) p.1 *
              ballCutoff (n : ℝ) p.2 := by ring
        _ = heatKernel δ (p.1 - x) *
              (ballCutoff ((n + 1 : ℕ) : ℝ) p.1 * ballCutoff (n : ℝ) p.2) := by ring
        _ ≤ heatKernel δ (p.1 - x) *
              (ballCutoff ((n + 1 : ℕ) : ℝ) p.1 * ballCutoff ((n + 1 : ℕ) : ℝ) p.2) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hc2
                (ballCutoff_mem_Icc ((n + 1 : ℕ) : ℝ) p.1).1) hk
        _ = heatKernel δ (p.1 - x) * ballCutoff ((n + 1 : ℕ) : ℝ) p.1 *
              ballCutoff ((n + 1 : ℕ) : ℝ) p.2 := by ring
    have hreal := integral_mono (hIn n) (hIn (n + 1)) htest
    change ENNReal.ofReal (∫ p, heatCutoffTest δ x (n : ℝ) p ∂(Z s t ω)) ≤
      ENNReal.ofReal (∫ p, heatCutoffTest δ x ((n + 1 : ℕ) : ℝ) p ∂(Z s t ω))
    exact ENNReal.ofReal_le_ofReal hreal
  have hseqMono : ∀ᵐ ω ∂P, Monotone (fun n => hseq n ω) := by
    filter_upwards [ae_all_iff.2 hstep] with ω hω
    exact monotone_nat_of_le_succ hω
  have hinner : ∀ᵐ ω ∂P, (⨆ n : ℕ, hseq n ω) = A ω := by
    filter_upwards [hlocal] with ω hω
    have hIn (n : ℕ) : Integrable
        (fun p : Plane × Plane => heatCutoffTest δ x (n : ℝ) p) (Z s t ω) := by
      exact integrable_cC_of_locallyFinite (Z s t ω) hω.1 (heatCutoffTest δ x (n : ℝ))
    have hnonneg (n : ℕ) : 0 ≤ᵐ[Z s t ω]
        (fun p : Plane × Plane => heatCutoffTest δ x (n : ℝ) p) :=
      Filter.Eventually.of_forall fun p => by
        have h1 := ballCutoff_mem_Icc (n : ℝ) p.1
        have h2 := ballCutoff_mem_Icc (n : ℝ) p.2
        exact mul_nonneg (mul_nonneg (heatKernel_nonneg hδ.le _) h1.1) h2.1
    have htestmono : Monotone (fun n : ℕ => fun p : Plane × Plane =>
        ENNReal.ofReal (heatCutoffTest δ x (n : ℝ) p)) := by
      intro n m hnm p
      have hn : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      have hc1 := ballCutoff_mono_radius hn p.1
      have hc2 := ballCutoff_mono_radius hn p.2
      have h1 := ballCutoff_mem_Icc (n : ℝ) p.1
      have h2 := ballCutoff_mem_Icc (n : ℝ) p.2
      have hk := heatKernel_nonneg hδ.le (p.1 - x)
      apply ENNReal.ofReal_le_ofReal
      change heatKernel δ (p.1 - x) * ballCutoff (n : ℝ) p.1 * ballCutoff (n : ℝ) p.2 ≤ _
      calc
        heatKernel δ (p.1 - x) * ballCutoff (n : ℝ) p.1 * ballCutoff (n : ℝ) p.2 =
            heatKernel δ (p.1 - x) * (ballCutoff (n : ℝ) p.1 * ballCutoff (n : ℝ) p.2) := by ring
        _ ≤ heatKernel δ (p.1 - x) * (ballCutoff (m : ℝ) p.1 * ballCutoff (n : ℝ) p.2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc1 h2.1) hk
        _ = heatKernel δ (p.1 - x) * ballCutoff (m : ℝ) p.1 * ballCutoff (n : ℝ) p.2 := by ring
        _ = heatKernel δ (p.1 - x) * (ballCutoff (m : ℝ) p.1 * ballCutoff (n : ℝ) p.2) := by ring
        _ ≤ heatKernel δ (p.1 - x) * (ballCutoff (m : ℝ) p.1 * ballCutoff (m : ℝ) p.2) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hc2 (ballCutoff_mem_Icc (m : ℝ) p.1).1) hk
        _ = heatKernel δ (p.1 - x) * ballCutoff (m : ℝ) p.1 * ballCutoff (m : ℝ) p.2 := by ring
    have hpoint (p : Plane × Plane) :
        (⨆ n : ℕ, ENNReal.ofReal (heatCutoffTest δ x (n : ℝ) p)) =
          ENNReal.ofReal (heatKernel δ (p.1 - x)) := by
      have hlim : Tendsto (fun n : ℕ => heatCutoffTest δ x (n : ℝ) p) atTop
          (𝓝 (heatKernel δ (p.1 - x))) := by
        have h1 : Tendsto (fun n : ℕ => ballCutoff (n : ℝ) p.1) atTop (𝓝 1) := by
          convert (tendsto_ballCutoff p.1).comp tendsto_natCast_atTop_atTop using 1
          all_goals rfl
        have h2 : Tendsto (fun n : ℕ => ballCutoff (n : ℝ) p.2) atTop (𝓝 1) := by
          convert (tendsto_ballCutoff p.2).comp tendsto_natCast_atTop_atTop using 1
          all_goals rfl
        change Tendsto (fun n : ℕ => heatKernel δ (p.1 - x) *
          ballCutoff (n : ℝ) p.1 * ballCutoff (n : ℝ) p.2) atTop
          (𝓝 (heatKernel δ (p.1 - x)))
        simpa only [mul_one] using (tendsto_const_nhds.mul h1).mul h2
      have hlim' : Tendsto (fun n : ℕ =>
          ENNReal.ofReal (heatCutoffTest δ x (n : ℝ) p)) atTop
          (𝓝 (ENNReal.ofReal (heatKernel δ (p.1 - x)))) :=
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim
      apply iSup_eq_of_forall_le_of_forall_lt_exists_gt
      · intro n
        have h1 := ballCutoff_mem_Icc (n : ℝ) p.1
        have h2 := ballCutoff_mem_Icc (n : ℝ) p.2
        exact ENNReal.ofReal_le_ofReal (by
          dsimp [heatCutoffTest]
          calc
            heatKernel δ (p.1 - x) * ballCutoff (n : ℝ) p.1 * ballCutoff (n : ℝ) p.2 ≤
                heatKernel δ (p.1 - x) * 1 * 1 := by
                  have hprod : ballCutoff (n : ℝ) p.1 * ballCutoff (n : ℝ) p.2 ≤ 1 := by
                    calc
                      _ ≤ 1 * 1 := mul_le_mul h1.2 h2.2 h2.1 (by norm_num)
                      _ = 1 := by ring
                  calc
                    _ = heatKernel δ (p.1 - x) *
                        (ballCutoff (n : ℝ) p.1 * ballCutoff (n : ℝ) p.2) := by ring
                    _ ≤ heatKernel δ (p.1 - x) * 1 :=
                      mul_le_mul_of_nonneg_left hprod (heatKernel_nonneg hδ.le _)
                    _ = heatKernel δ (p.1 - x) * 1 * 1 := by ring
            _ = heatKernel δ (p.1 - x) := by ring)
      · intro w hw
        obtain ⟨n, hn⟩ := (hlim'.eventually (isOpen_Ioi.mem_nhds hw)).exists
        exact ⟨n, hn⟩
    have hinnerMCT : ∫⁻ p, ⨆ n : ℕ, ENNReal.ofReal
        (heatCutoffTest δ x (n : ℝ) p) ∂(Z s t ω) =
        ⨆ n : ℕ, ∫⁻ p, ENNReal.ofReal (heatCutoffTest δ x (n : ℝ) p) ∂(Z s t ω) :=
      lintegral_iSup (fun n => ENNReal.measurable_ofReal.comp
        (heatCutoffTest δ x (n : ℝ)).continuous_toFun.measurable) htestmono
    have hterm (n : ℕ) : ∫⁻ p, ENNReal.ofReal
        (heatCutoffTest δ x (n : ℝ) p) ∂(Z s t ω) = hseq n ω := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hIn n) (hnonneg n)]
    have hsup : (⨆ n : ℕ, hseq n ω) = ⨆ n : ℕ,
        ∫⁻ p, ENNReal.ofReal (heatCutoffTest δ x (n : ℝ) p) ∂(Z s t ω) := by
      apply iSup_congr
      intro n
      exact (hterm n).symm
    calc
      (⨆ n : ℕ, hseq n ω) = ⨆ n : ℕ, ∫⁻ p, ENNReal.ofReal
          (heatCutoffTest δ x (n : ℝ) p) ∂(Z s t ω) := hsup
      _ = ∫⁻ p, ⨆ n : ℕ, ENNReal.ofReal
          (heatCutoffTest δ x (n : ℝ) p) ∂(Z s t ω) := hinnerMCT.symm
      _ = A ω := by
            dsimp [A]
            apply lintegral_congr_ae
            exact Filter.Eventually.of_forall hpoint
  have houterMCT : ∫⁻ ω, ⨆ n : ℕ, hseq n ω ∂P = ⨆ n, ∫⁻ ω, hseq n ω ∂P :=
    lintegral_iSup' hseqMeas hseqMono
  have hbound : ∫⁻ ω, A ω ∂P ≤ 1 := by
    calc
      _ = ∫⁻ ω, ⨆ n : ℕ, hseq n ω ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hinner] with ω hω using hω.symm
      _ = ⨆ n, ∫⁻ ω, hseq n ω ∂P := houterMCT
      _ ≤ 1 := iSup_le fun n => by
        change ∫⁻ ω, ENNReal.ofReal
          (∫ p, heatCutoffTest δ x (n : ℝ) p ∂(Z s t ω)) ∂P ≤ 1
        exact isCriticalSHF_heatCutoff_lintegral_le_one
          ϑ P Z hZ hs hst hδ x (n : ℝ)
  simpa [A] using hbound

private theorem integrable_heatKernel_of_lintegral_finite
    (μ : Measure (Plane × Plane)) (δ : ℝ) (x : Plane) (hδ : 0 < δ)
    (hfin : ∫⁻ p : Plane × Plane, ENNReal.ofReal (heatKernel δ (p.1 - x)) ∂μ < ∞) :
    Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x)) μ := by
  exact (lintegral_ofReal_ne_top_iff_integrable
    (((measurable_heatKernel δ).comp (measurable_fst.sub_const x)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun p => heatKernel_nonneg hδ.le (p.1 - x))).1 hfin.ne

private theorem integral_eq_toReal_lintegral_of_nonneg {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hInt : Integrable f μ)
    (hnonneg : 0 ≤ᵐ[μ] f) :
    (∫ a, f a ∂μ) = (∫⁻ a, ENNReal.ofReal (f a) ∂μ).toReal := by
  have hlin := ofReal_integral_eq_lintegral_ofReal hInt hnonneg
  have hreal := congrArg ENNReal.toReal hlin
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hnonneg)] at hreal
  exact hreal

/-- The heat-start mass of every critical SHF is integrable in disorder and has mean at most one. -/
theorem isCriticalSHF_heat_start_integrable_bound (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) {s t δ : ℝ} (hs : 0 ≤ s) (hst : s < t) (hδ : 0 < δ)
    (x : Plane) :
    Integrable (fun ω => ∫ p, heatKernel δ (p.1 - x) ∂(Z s t ω)) P ∧
    ∫ ω, ∫ p, heatKernel δ (p.1 - x) ∂(Z s t ω) ∂P ≤ 1 := by
  let A : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ p, ENNReal.ofReal (heatKernel δ (p.1 - x)) ∂(Z s t ω)
  have hAmeas : Measurable A := by
    dsimp [A]
    exact (Measure.measurable_lintegral
      (ENNReal.measurable_ofReal.comp ((measurable_heatKernel δ).comp
        (measurable_fst.sub_const x)))).comp (hZ.1 s t hs hst)
  have hbound := isCriticalSHF_heat_start_lintegral_bound ϑ P Z hZ hs hst hδ x
  have hAintTop : (∫⁻ ω, A ω ∂P) ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hbound ENNReal.one_lt_top)
  have hfinite : ∀ᵐ ω ∂P, A ω < ∞ := ae_lt_top hAmeas hAintTop
  have hAtoReal : Integrable (fun ω => (A ω).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hAmeas.aemeasurable hAintTop
  have hpairEq : (fun ω => ∫ p, heatKernel δ (p.1 - x) ∂(Z s t ω)) =ᵐ[P]
      fun ω => (A ω).toReal := by
    filter_upwards [hfinite] with ω hωfin
    have hfinω : ∫⁻ p, ENNReal.ofReal (heatKernel δ (p.1 - x)) ∂(Z s t ω) < ∞ := by
      simpa [A] using hωfin
    have hInt : Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x))
        (Z s t ω) := integrable_heatKernel_of_lintegral_finite
          (Z s t ω) δ x hδ hfinω
    have hnonneg : 0 ≤ᵐ[Z s t ω] fun p : Plane × Plane => heatKernel δ (p.1 - x) :=
      Filter.Eventually.of_forall fun p => heatKernel_nonneg hδ.le _
    have hreal := integral_eq_toReal_lintegral_of_nonneg
      (Z s t ω) (fun p : Plane × Plane => heatKernel δ (p.1 - x)) hInt hnonneg
    simpa [A] using hreal
  constructor
  · exact hAtoReal.congr hpairEq.symm
  · calc
      (∫ ω, ∫ p, heatKernel δ (p.1 - x) ∂(Z s t ω) ∂P) =
          ∫ ω, (A ω).toReal ∂P := integral_congr_ae hpairEq
      _ ≤ 1 := by
        have htoReal := integral_toReal hAmeas.aemeasurable hfinite
        rw [htoReal]
        exact ENNReal.toReal_mono ENNReal.one_ne_top hbound

/-- At fixed admissible time and heat parameters, the heat kernel is integrable against the SHF pair measure almost surely, and its pairing has finite expectation by `isCriticalSHF_heat_start_integrable_bound`. -/
theorem isCriticalSHF_ae_integrable_heat_start (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) {s t δ : ℝ} (hs : 0 ≤ s) (hst : s < t) (hδ : 0 < δ)
    (x : Plane) :
    ∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x)) (Z s t ω) := by
  let A : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ p, ENNReal.ofReal (heatKernel δ (p.1 - x)) ∂(Z s t ω)
  have hAmeas : Measurable A := by
    dsimp [A]
    exact (Measure.measurable_lintegral
      (ENNReal.measurable_ofReal.comp ((measurable_heatKernel δ).comp
        (measurable_fst.sub_const x)))).comp (hZ.1 s t hs hst)
  have hbound := isCriticalSHF_heat_start_lintegral_bound ϑ P Z hZ hs hst hδ x
  have hfinite : ∀ᵐ ω ∂P, A ω < ∞ :=
    ae_lt_top hAmeas (ne_of_lt (lt_of_le_of_lt hbound ENNReal.one_lt_top))
  filter_upwards [hfinite] with ω hω
  apply integrable_heatKernel_of_lintegral_finite (Z s t ω) δ x hδ
  simpa [A] using hω

end Critical2DKPZ.SHF.Positivity

end
