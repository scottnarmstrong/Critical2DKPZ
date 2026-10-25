/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Positivity.HeatStartMean
public import Critical2DKPZ.SHF.Tsai.Cutoff
public import Critical2DKPZ.SHF.Moments.PairingFubini
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! # Compact heat-start cutoff tests -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported Topology

namespace Critical2DKPZ.SHF.Positivity

/-- Compactly supported approximation to a heat-start, unit-terminal pairing. -/
def heatCutoffTest (δ : ℝ) (x : Plane) (R : ℝ) : C_c(Plane × Plane, ℝ) where
  toFun p := heatKernel δ (p.1 - x) * ballCutoff R p.1 * ballCutoff R p.2
  continuous_toFun := by
    exact (((continuous_heatKernel δ).comp (continuous_fst.sub continuous_const)).mul
      ((continuous_ballCutoff R).comp continuous_fst)).mul
        ((continuous_ballCutoff R).comp continuous_snd)
  hasCompactSupport' := by
    apply HasCompactSupport.of_support_subset_isCompact
      ((isCompact_closedBall (0 : Plane) (R + 1)).prod
        (isCompact_closedBall (0 : Plane) (R + 1)))
    intro p hp
    constructor
    · rw [Metric.mem_closedBall, dist_zero_right]
      by_contra hn
      have hzero : ballCutoff R p.1 = 0 :=
        ballCutoff_eq_zero_of_le_norm (le_of_lt (lt_of_not_ge hn))
      apply hp
      change heatKernel δ (p.1 - x) * ballCutoff R p.1 * ballCutoff R p.2 = 0
      simp [hzero]
    · rw [Metric.mem_closedBall, dist_zero_right]
      by_contra hn
      have hzero : ballCutoff R p.2 = 0 :=
        ballCutoff_eq_zero_of_le_norm (le_of_lt (lt_of_not_ge hn))
      apply hp
      change heatKernel δ (p.1 - x) * ballCutoff R p.1 * ballCutoff R p.2 = 0
      simp [hzero]

/-- The spatial ball cutoff increases with its radius. -/
theorem ballCutoff_mono_radius {R S : ℝ} (hRS : R ≤ S) (y : Plane) :
    ballCutoff R y ≤ ballCutoff S y := by
  unfold ballCutoff
  gcongr

private theorem integrable_limitHeatStartKernel {s t δ : ℝ} (hst : s < t) (hδ : 0 < δ)
    (x : Plane) :
    Integrable (fun p : Plane × Plane =>
      heatKernel δ (p.1 - x) * heatKernel (t - s) (p.2 - p.1)) := by
  let F : Plane × Plane → ℝ := fun p =>
    heatKernel δ (p.1 - x) * heatKernel (t - s) (p.2 - p.1)
  have hcont : Continuous F := by
    dsimp [F]
    exact (continuous_heatKernel δ).comp (continuous_fst.sub continuous_const) |>.mul
      ((continuous_heatKernel (t - s)).comp (continuous_snd.sub continuous_fst))
  have hsm : AEStronglyMeasurable F (volume.prod volume) := hcont.measurable.aestronglyMeasurable
  rw [Measure.volume_eq_prod]
  apply (integrable_prod_iff hsm).2
  constructor
  · exact Filter.Eventually.of_forall fun y => by
      have hker : Integrable (fun z : Plane => heatKernel (t - s) (z - y)) volume :=
        (integrable_heatKernel (sub_pos.mpr hst)).comp_sub_right y
      simpa [F, mul_comm] using hker.const_mul (heatKernel δ (y - x))
  · have hsection (y : Plane) :
        (∫ z, ‖F (y, z)‖ ∂volume) = heatKernel δ (y - x) := by
      have hstart : 0 ≤ heatKernel δ (y - x) := heatKernel_nonneg hδ.le _
      have hend : ∀ z, 0 ≤ heatKernel (t - s) (z - y) :=
        fun z => heatKernel_nonneg (sub_nonneg.mpr hst.le) _
      simp_rw [F, Real.norm_eq_abs, abs_mul, abs_of_nonneg hstart,
        abs_of_nonneg (hend _)]
      rw [integral_const_mul, integral_heatKernel_sub (sub_pos.mpr hst) y]
      simp
    have hf : Integrable (fun y : Plane => heatKernel δ (y - x)) volume :=
      (integrable_heatKernel hδ).comp_sub_right x
    change Integrable (fun y : Plane => ∫ z, ‖F (y, z)‖ ∂volume) volume
    simpa only [hsection] using hf

private theorem integral_limitHeatStartKernel_eq_one {s t δ : ℝ} (hst : s < t)
    (hδ : 0 < δ) (x : Plane) :
    (∫ p : Plane × Plane,
      heatKernel δ (p.1 - x) * heatKernel (t - s) (p.2 - p.1)) = 1 := by
  have hF := integrable_limitHeatStartKernel hst hδ x
  rw [Measure.volume_eq_prod, integral_prod _ hF]
  calc
    (∫ y, ∫ z, heatKernel δ (y - x) * heatKernel (t - s) (z - y) ∂volume ∂volume)
        = ∫ y, heatKernel δ (y - x) ∂volume := by
          apply integral_congr_ae
          filter_upwards [] with y
          rw [integral_const_mul, integral_heatKernel_sub (sub_pos.mpr hst) y, mul_one]
    _ = 1 := integral_heatKernel_sub hδ x

private theorem tendsto_limitHeatCutoffIntegral {s t δ : ℝ} (hst : s < t)
    (hδ : 0 < δ) (x : Plane) :
    Tendsto (fun R : ℝ => ∫ p : Plane × Plane,
      heatCutoffTest δ x R p * heatKernel (t - s) (p.2 - p.1)) atTop (𝓝 1) := by
  let F : Plane × Plane → ℝ := fun p =>
    heatKernel δ (p.1 - x) * heatKernel (t - s) (p.2 - p.1)
  let Fcut : ℝ → Plane × Plane → ℝ := fun R p =>
    F p * ballCutoff R p.1 * ballCutoff R p.2
  have hFint : Integrable F := integrable_limitHeatStartKernel hst hδ x
  have hmeas : ∀ R, AEStronglyMeasurable (Fcut R) volume := by
    intro R
    exact ((continuous_heatKernel δ).comp (continuous_fst.sub continuous_const) |>.mul
      ((continuous_heatKernel (t - s)).comp (continuous_snd.sub continuous_fst)) |>.mul
        ((continuous_ballCutoff R).comp continuous_fst) |>.mul
          ((continuous_ballCutoff R).comp continuous_snd)).measurable.aestronglyMeasurable
  have hbound : ∀ R, ∀ᵐ p ∂volume, ‖Fcut R p‖ ≤ F p := by
    intro R
    filter_upwards [] with p
    have hF0 : 0 ≤ F p := mul_nonneg
      (heatKernel_nonneg hδ.le _) (heatKernel_nonneg (sub_nonneg.mpr hst.le) _)
    have hcut1 := ballCutoff_mem_Icc R p.1
    have hcut2 := ballCutoff_mem_Icc R p.2
    have hnonneg : 0 ≤ Fcut R p := by
      dsimp [Fcut]
      exact mul_nonneg (mul_nonneg hF0 hcut1.1) hcut2.1
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    dsimp [Fcut]
    calc
      F p * ballCutoff R p.1 * ballCutoff R p.2 ≤
          F p * ballCutoff R p.1 * 1 := by
            exact mul_le_mul_of_nonneg_left hcut2.2
              (mul_nonneg hF0 hcut1.1)
      _ = F p * ballCutoff R p.1 := by ring
      _ ≤ F p * 1 := mul_le_mul_of_nonneg_left hcut1.2 hF0
      _ = F p := by ring
  have hlim : ∀ p, Tendsto (fun R : ℝ => Fcut R p) atTop (𝓝 (F p)) := by
    intro p
    have h1 := tendsto_ballCutoff p.1
    have h2 := tendsto_ballCutoff p.2
    simpa [Fcut] using (tendsto_const_nhds.mul h1).mul h2
  have hconv := tendsto_integral_filter_of_dominated_convergence
    (bound := F) (Filter.Eventually.of_forall hmeas)
    (Filter.Eventually.of_forall fun R => hbound R) hFint
    (Filter.Eventually.of_forall hlim)
  have hfull := integral_limitHeatStartKernel_eq_one hst hδ x
  have hconv' : Tendsto (fun R : ℝ => ∫ p : Plane × Plane,
      heatCutoffTest δ x R p * heatKernel (t - s) (p.2 - p.1)) atTop (𝓝 (∫ p, F p)) := by
    convert hconv using 1
    · funext R
      apply integral_congr_ae
      filter_upwards [] with p
      dsimp [heatCutoffTest, Fcut, F]
      ring
  rw [hfull] at hconv'
  exact hconv'

private theorem integral_polymer_heatCutoffTail_eq {ϑ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    {s t δ : ℝ} (hδ : 0 < δ) (x : Plane) (R : ℝ) :
    (∫ ω, ∫ p, heatKernel δ (p.1 - x) *
      (1 - ballCutoff R p.1 * ballCutoff R p.2)
        ∂(polymerMeasure ϑ N s t ω) ∂disorderLaw) =
      1 - ∫ ω, ∫ p, heatKernel δ (p.1 - x) * ballCutoff R p.1 * ballCutoff R p.2
        ∂(polymerMeasure ϑ N s t ω) ∂disorderLaw := by
  let A : Disorder → ℝ := fun ω =>
    ∫ p, heatKernel δ (p.1 - x) ∂(polymerMeasure ϑ N s t ω)
  let C : Disorder → ℝ := fun ω =>
    ∫ p, heatCutoffTest δ x R p ∂(polymerMeasure ϑ N s t ω)
  have hTotal := integral_polymer_heat_start_pairing_eq_one ϑ hN s t δ hδ x
  have hCint : Integrable C disorderLaw := by
    have hprod := SHF.Moments.integrable_pairing_rescaledP2P ϑ N s t
      (heatCutoffTest δ x R).continuous_toFun
      (heatCutoffTest δ x R).hasCompactSupport'
    have hswap := hprod.swap
    have hCden : Integrable (fun ω : Disorder =>
        ∫ p, heatCutoffTest δ x R p * rescaledP2P ϑ N s t p ω ∂volume) disorderLaw := by
      exact hswap.integral_prod_left
    apply hCden.congr
    filter_upwards [] with ω
    exact (integral_polymerMeasure ϑ N s t ω (heatCutoffTest δ x R)).symm
  have hinner :
      (fun ω => ∫ p, heatKernel δ (p.1 - x) *
        (1 - ballCutoff R p.1 * ballCutoff R p.2)
          ∂(polymerMeasure ϑ N s t ω) : Disorder → ℝ) =ᵐ[disorderLaw]
      (fun ω => A ω - C ω) := by
    filter_upwards [ae_integrable_polymer_heat_start ϑ hN s t δ hδ x] with ω hA
    have hcut : Integrable (fun p : Plane × Plane => heatCutoffTest δ x R p)
        (polymerMeasure ϑ N s t ω) := by
      apply hA.mono'
        (heatCutoffTest δ x R).continuous_toFun.measurable.aestronglyMeasurable
      filter_upwards [] with p
      have hstart := ballCutoff_mem_Icc R p.1
      have hend := ballCutoff_mem_Icc R p.2
      have hkernel : 0 ≤ heatKernel δ (p.1 - x) := heatKernel_nonneg hδ.le _
      change ‖heatCutoffTest δ x R p‖ ≤ heatKernel δ (p.1 - x)
      rw [Real.norm_eq_abs]
      dsimp [heatCutoffTest]
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg hkernel hstart.1) hend.1)]
      calc
        heatKernel δ (p.1 - x) * ballCutoff R p.1 * ballCutoff R p.2 ≤
            heatKernel δ (p.1 - x) * ballCutoff R p.1 * 1 :=
              mul_le_mul_of_nonneg_left hend.2 (mul_nonneg hkernel hstart.1)
        _ = heatKernel δ (p.1 - x) * ballCutoff R p.1 := by ring
        _ ≤ heatKernel δ (p.1 - x) * 1 := mul_le_mul_of_nonneg_left hstart.2 hkernel
        _ = heatKernel δ (p.1 - x) := by ring
    have htail : Integrable (fun p : Plane × Plane =>
        heatKernel δ (p.1 - x) *
          (1 - ballCutoff R p.1 * ballCutoff R p.2)) (polymerMeasure ϑ N s t ω) := by
      have htailCont : Continuous (fun p : Plane × Plane =>
          heatKernel δ (p.1 - x) *
            (1 - ballCutoff R p.1 * ballCutoff R p.2)) := by
        exact ((continuous_heatKernel δ).comp (continuous_fst.sub continuous_const)).mul
          ((continuous_const : Continuous (fun _ : Plane × Plane => (1 : ℝ))).sub
            (((continuous_ballCutoff R).comp continuous_fst).mul
              ((continuous_ballCutoff R).comp continuous_snd)))
      apply hA.mono'
        htailCont.measurable.aestronglyMeasurable
      filter_upwards [] with p
      have hstart := ballCutoff_mem_Icc R p.1
      have hend := ballCutoff_mem_Icc R p.2
      have hkernel : 0 ≤ heatKernel δ (p.1 - x) := heatKernel_nonneg hδ.le _
      have hprod : 0 ≤ ballCutoff R p.1 * ballCutoff R p.2 ∧
          ballCutoff R p.1 * ballCutoff R p.2 ≤ 1 := by
        constructor
        · exact mul_nonneg hstart.1 hend.1
        · calc
            ballCutoff R p.1 * ballCutoff R p.2 ≤ ballCutoff R p.1 * 1 :=
                mul_le_mul_of_nonneg_left hend.2 hstart.1
            _ ≤ 1 := by simpa only [mul_one] using hstart.2
      have hfac : 0 ≤ 1 - ballCutoff R p.1 * ballCutoff R p.2 ∧
          1 - ballCutoff R p.1 * ballCutoff R p.2 ≤ 1 := by constructor <;> linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hkernel hfac.1)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hfac.2 hkernel
    have hfun : (fun p : Plane × Plane => heatKernel δ (p.1 - x) *
        (1 - ballCutoff R p.1 * ballCutoff R p.2)) =
        (fun p => heatKernel δ (p.1 - x)) - (fun p => heatCutoffTest δ x R p) := by
      funext p
      dsimp [heatCutoffTest]
      ring
    dsimp [A, C]
    rw [hfun]
    exact integral_sub hA hcut
  calc
    (∫ ω, ∫ p, heatKernel δ (p.1 - x) *
        (1 - ballCutoff R p.1 * ballCutoff R p.2)
          ∂(polymerMeasure ϑ N s t ω) ∂disorderLaw)
        = ∫ ω, A ω - C ω ∂disorderLaw := integral_congr_ae hinner
    _ = (∫ ω, A ω ∂disorderLaw) - ∫ ω, C ω ∂disorderLaw := integral_sub hTotal.1 hCint
    _ = 1 - ∫ ω, ∫ p, heatCutoffTest δ x R p ∂(polymerMeasure ϑ N s t ω) ∂disorderLaw := by
      rw [hTotal.2]

/-- The large-scale limsup of the first-moment heat-start cutoff error tends to zero as the cutoff radius grows. -/
theorem integral_polymer_heat_pairing_cutoff_le (ϑ : ℝ) {s t δ : ℝ} (hs : 0 ≤ s)
    (hst : s < t) (hδ : 0 < δ) (x : Plane) :
    ∀ ε > 0, ∃ R₀ : ℝ, ∀ R ≥ R₀, ∀ᶠ N : ℕ in atTop,
      ∫ ω, ∫ p, heatKernel δ (p.1 - x) * (1 - ballCutoff R p.1 * ballCutoff R p.2)
        ∂(polymerMeasure ϑ N s t ω) ∂disorderLaw ≤ ε := by
  intro ε hε
  have hlimit := tendsto_limitHeatCutoffIntegral hst hδ x
  obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.1
    (Metric.tendsto_nhds.1 hlimit (ε / 3) (by positivity))
  refine ⟨R₀, ?_⟩
  intro R hR
  have hL : |(∫ p : Plane × Plane,
      heatCutoffTest δ x R p * heatKernel (t - s) (p.2 - p.1)) - 1| < ε / 3 := by
    simpa only [Real.dist_eq, abs_sub_comm] using hR₀ R hR
  have hmean := integral_polymerMeasure_mean ϑ hs hst (heatCutoffTest δ x R)
  have hclose : ∀ᶠ N : ℕ in atTop, |(∫ ω, ∫ p,
      heatCutoffTest δ x R p ∂(polymerMeasure ϑ N s t ω) ∂disorderLaw) -
        (∫ p : Plane × Plane,
          heatCutoffTest δ x R p * heatKernel (t - s) (p.2 - p.1))| < ε / 3 := by
    exact Metric.tendsto_nhds.1 hmean (ε / 3) (by positivity)
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun N hN => hN⟩, hclose] with N hN hclose
  have htail := @integral_polymer_heatCutoffTail_eq ϑ N hN s t δ hδ x R
  have hCeq : (∫ ω, ∫ p, heatCutoffTest δ x R p
      ∂(polymerMeasure ϑ N s t ω) ∂disorderLaw) =
      ∫ ω, ∫ p, heatKernel δ (p.1 - x) * ballCutoff R p.1 * ballCutoff R p.2
        ∂(polymerMeasure ϑ N s t ω) ∂disorderLaw := by
    apply integral_congr_ae
    filter_upwards [] with ω
    apply integral_congr_ae
    filter_upwards [] with p
    rfl
  rw [hCeq.symm] at htail
  rw [htail]
  have hclose' := abs_lt.mp hclose
  have hL' := abs_lt.mp hL
  linarith [hclose'.1, hL'.1, hε]

end Critical2DKPZ.SHF.Positivity

end
