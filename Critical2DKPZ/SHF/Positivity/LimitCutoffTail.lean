/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Positivity.FatouContinuousPairing
public import Critical2DKPZ.SHF.Positivity.CutoffTests
public import Critical2DKPZ.SHF.Positivity.HeatStartLimit
public import Critical2DKPZ.SHF.Positivity.BoundedCutoff
public import Critical2DKPZ.SHF.Limit.Measurability
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

/-! # First-moment cutoff tails for limiting heat-start pairings -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai
open scoped BoundedContinuousFunction ENNReal Topology

namespace Critical2DKPZ.SHF.Positivity

/-- The nonnegative remainder after cutting off both coordinates of a heat-start pairing. -/
def heatPairingCutoffTail (δ : ℝ) (x : Plane) (R : ℝ) : Plane × Plane → ℝ :=
  fun p => heatKernel δ (p.1 - x) * (1 - ballCutoff R p.1 * ballCutoff R p.2)

private theorem continuous_heatPairingCutoffTail {δ : ℝ} (x : Plane) (R : ℝ) :
    Continuous (heatPairingCutoffTail δ x R) := by
  exact ((continuous_heatKernel δ).comp (continuous_fst.sub continuous_const)).mul
    ((continuous_const : Continuous (fun _ : Plane × Plane => (1 : ℝ))).sub
      (((continuous_ballCutoff R).comp continuous_fst).mul
        ((continuous_ballCutoff R).comp continuous_snd)))

private theorem heatPairingCutoffTail_nonneg {δ : ℝ} (hδ : 0 < δ) (x : Plane) (R : ℝ)
    (p : Plane × Plane) : 0 ≤ heatPairingCutoffTail δ x R p := by
  have h1 := ballCutoff_mem_Icc R p.1
  have h2 := ballCutoff_mem_Icc R p.2
  have hprod : 0 ≤ ballCutoff R p.1 * ballCutoff R p.2 ∧
      ballCutoff R p.1 * ballCutoff R p.2 ≤ 1 := by
    constructor
    · exact mul_nonneg h1.1 h2.1
    · calc
        ballCutoff R p.1 * ballCutoff R p.2 ≤ ballCutoff R p.1 * 1 :=
          mul_le_mul_of_nonneg_left h2.2 h1.1
        _ ≤ 1 := by simpa using h1.2
  simp only [heatPairingCutoffTail]
  exact mul_nonneg (heatKernel_nonneg hδ.le _) (by linarith)

private theorem heatPairingCutoffTail_le_heatKernel {δ : ℝ} (hδ : 0 < δ)
    (x : Plane) (R : ℝ) (p : Plane × Plane) :
    heatPairingCutoffTail δ x R p ≤ heatKernel δ (p.1 - x) := by
  have h1 := ballCutoff_mem_Icc R p.1
  have h2 := ballCutoff_mem_Icc R p.2
  have hprod : ballCutoff R p.1 * ballCutoff R p.2 ≤ 1 := by
    calc
      ballCutoff R p.1 * ballCutoff R p.2 ≤ ballCutoff R p.1 * 1 :=
        mul_le_mul_of_nonneg_left h2.2 h1.1
      _ ≤ 1 := by simpa using h1.2
  dsimp [heatPairingCutoffTail]
  have hk := heatKernel_nonneg hδ.le (p.1 - x)
  have hprod0 : 0 ≤ ballCutoff R p.1 * ballCutoff R p.2 :=
    mul_nonneg (ballCutoff_mem_Icc R p.1).1 (ballCutoff_mem_Icc R p.2).1
  calc
    heatKernel δ (p.1 - x) * (1 - ballCutoff R p.1 * ballCutoff R p.2) ≤
        heatKernel δ (p.1 - x) * 1 :=
        mul_le_mul_of_nonneg_left
        (by linarith : 1 - ballCutoff R p.1 * ballCutoff R p.2 ≤ 1) hk
    _ = heatKernel δ (p.1 - x) := by ring

private theorem integrable_heatPairingCutoffTail_of_heat {δ : ℝ} (hδ : 0 < δ)
    (x : Plane) (R : ℝ) (μ : Measure (Plane × Plane))
    (hK : Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x)) μ) :
    Integrable (heatPairingCutoffTail δ x R) μ := by
  apply hK.mono' (continuous_heatPairingCutoffTail x R).measurable.aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (heatPairingCutoffTail_nonneg hδ x R p)]
  exact heatPairingCutoffTail_le_heatKernel hδ x R p

private theorem polymerMeasure_zero' (ϑ : ℝ) (s t : ℝ) (ω : Disorder) :
    polymerMeasure ϑ 0 s t ω = 0 := by
  rw [polymerMeasure]
  ext A hA
  simp [rescaledP2P]

private theorem ae_integrable_heatPairingCutoffTail_SHF (ϑ : ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {s t δ : ℝ} (hs : 0 ≤ s) (hst : s < t) (hδ : 0 < δ) (x : Plane) (R : ℝ) :
    ∀ᵐ ω ∂P, Integrable (heatPairingCutoffTail δ x R) (Z s t ω) := by
  filter_upwards [isCriticalSHF_ae_integrable_heat_start ϑ P Z hZ hs hst hδ x] with ω hω
  exact integrable_heatPairingCutoffTail_of_heat hδ x R (Z s t ω) hω

private theorem ae_integrable_heatPairingCutoffTail_polymer (ϑ : ℝ)
    (N : ℕ) {s t δ : ℝ} (hδ : 0 < δ) (x : Plane) (R : ℝ) :
    ∀ᵐ ω ∂disorderLaw,
      Integrable (heatPairingCutoffTail δ x R) (polymerMeasure ϑ N s t ω) := by
  by_cases hN : N = 0
  · subst N
    filter_upwards [] with ω
    rw [polymerMeasure_zero']
    exact integrable_zero_measure
  · have hN' : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
    filter_upwards [ae_integrable_polymer_heat_start ϑ hN' s t δ hδ x] with ω hω
    exact integrable_heatPairingCutoffTail_of_heat hδ x R (polymerMeasure ϑ N s t ω) hω

/-- Integrability in disorder of a cutoff-tail pairing follows by domination by the full heat-start
mass. -/
theorem integrable_random_heatPairingCutoffTail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure (Plane × Plane)) (hμ : Measurable μ)
    {δ : ℝ} (hδ : 0 < δ) (x : Plane) (R : ℝ)
    (hKae : ∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x)) (μ ω))
    (hKint : Integrable (fun ω => ∫ p, heatKernel δ (p.1 - x) ∂(μ ω)) P) :
    Integrable (fun ω => ∫ p, heatPairingCutoffTail δ x R p ∂(μ ω)) P := by
  have htailAE : ∀ᵐ ω ∂P, Integrable (heatPairingCutoffTail δ x R) (μ ω) :=
    hKae.mono fun ω hω => integrable_heatPairingCutoffTail_of_heat hδ x R (μ ω) hω
  have hmeas := aemeasurable_integral_of_measurable_measure P μ hμ
    (heatPairingCutoffTail δ x R) (continuous_heatPairingCutoffTail x R).measurable htailAE
  have hbound : ∀ᵐ ω ∂P,
      ‖∫ p, heatPairingCutoffTail δ x R p ∂(μ ω)‖ ≤
        ∫ p, heatKernel δ (p.1 - x) ∂(μ ω) := by
    filter_upwards [hKae] with ω hω
    have htail := integrable_heatPairingCutoffTail_of_heat hδ x R (μ ω) hω
    have hnonneg : 0 ≤ ∫ p, heatPairingCutoffTail δ x R p ∂(μ ω) :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall fun p =>
        heatPairingCutoffTail_nonneg hδ x R p)
    have hle := integral_mono htail hω (fun p =>
      heatPairingCutoffTail_le_heatKernel hδ x R p)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hle
  apply hKint.mono' hmeas.aestronglyMeasurable
  filter_upwards [hbound] with ω hω
  exact hω

private theorem integrable_polymer_heatPairingCutoffTail (ϑ : ℝ) (N : ℕ)
    {s t δ : ℝ} (hδ : 0 < δ) (x : Plane) (R : ℝ) :
    Integrable (fun ω => ∫ p, heatPairingCutoffTail δ x R p
      ∂(polymerMeasure ϑ N s t ω)) disorderLaw := by
  by_cases hN : N = 0
  · subst N
    have hzero (ω : Disorder) : polymerMeasure ϑ 0 s t ω = 0 := polymerMeasure_zero' _ _ _ _
    have heq : (fun ω => ∫ p, heatPairingCutoffTail δ x R p
        ∂(polymerMeasure ϑ 0 s t ω)) = fun _ => 0 := by
      funext ω
      rw [hzero]
      simp
    rw [heq]
    exact integrable_const _
  · have hN' : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
    exact integrable_random_heatPairingCutoffTail disorderLaw
      (polymerMeasure ϑ N s t) (measurable_polymerMeasure ϑ N s t)
      hδ x R (ae_integrable_polymer_heat_start ϑ hN' s t δ hδ x)
      (integral_polymer_heat_start_pairing_eq_one ϑ hN' s t δ hδ x).1

/-- For a critical SHF, the integral of the heat-pairing cutoff tail against `Z s t ω` is an
integrable function of the disorder `ω`. -/
theorem isCriticalSHF_heat_cutoff_tail_integrable (ϑ : ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {s t δ : ℝ} (hs : 0 ≤ s) (hst : s < t) (hδ : 0 < δ) (x : Plane) (R : ℝ) :
    Integrable (fun ω => ∫ p, heatPairingCutoffTail δ x R p ∂(Z s t ω)) P := by
  exact integrable_random_heatPairingCutoffTail P (Z s t) (hZ.1 s t hs hst)
    hδ x R (isCriticalSHF_ae_integrable_heat_start ϑ P Z hZ hs hst hδ x)
    (isCriticalSHF_heat_start_integrable_bound ϑ P Z hZ hs hst hδ x).1

/-- The limiting SHF inherits the first-moment cutoff tail bound from the polymers by Fatou in law.
The cutoff-tail integrability companion is `isCriticalSHF_heat_cutoff_tail_integrable`. -/
theorem isCriticalSHF_heat_pairing_cutoff_le (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {s t δ : ℝ} (hs : 0 ≤ s) (hst : s < t) (hδ : 0 < δ) (x : Plane) :
    ∀ ε > 0, ∃ R₀ : ℝ, ∀ R ≥ R₀,
      ∫ ω, ∫ p, heatPairingCutoffTail δ x R p ∂(Z s t ω) ∂P ≤ ε := by
  intro ε hε
  obtain ⟨R₀, hpolyTail⟩ := integral_polymer_heat_pairing_cutoff_le ϑ hs hst hδ x
    (ε / 2) (by linarith)
  refine ⟨R₀, ?_⟩
  intro R hR
  have hZint := ae_integrable_heatPairingCutoffTail_SHF ϑ P Z hZ hs hst hδ x R
  have hpolyInt (N : ℕ) := ae_integrable_heatPairingCutoffTail_polymer ϑ N
    (s := s) (t := t) hδ x R
  have hFatou := isCriticalSHF_integrable_lintegral_pairing_le_liminf ϑ P Z hZ hs hst
    (heatPairingCutoffTail δ x R) (continuous_heatPairingCutoffTail x R)
    (heatPairingCutoffTail_nonneg hδ x R) hZint hpolyInt
  have hZouter := isCriticalSHF_heat_cutoff_tail_integrable ϑ P Z hZ hs hst hδ x R
  have htailZnonneg : 0 ≤ᵐ[P] fun ω =>
      ∫ p, heatPairingCutoffTail δ x R p ∂(Z s t ω) := by
    filter_upwards [] with ω
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun p =>
      heatPairingCutoffTail_nonneg hδ x R p)
  have hZlin : ENNReal.ofReal
      (∫ ω, ∫ p, heatPairingCutoffTail δ x R p ∂(Z s t ω) ∂P) =
      ∫⁻ ω, ENNReal.ofReal
        (∫ p, heatPairingCutoffTail δ x R p ∂(Z s t ω)) ∂P :=
    ofReal_integral_eq_lintegral_ofReal hZouter htailZnonneg
  have hpolyLin (N : ℕ) : ENNReal.ofReal
      (∫ ω, ∫ p, heatPairingCutoffTail δ x R p
        ∂(polymerMeasure ϑ N s t ω) ∂disorderLaw) =
      ∫⁻ ω, ENNReal.ofReal
        (∫ p, heatPairingCutoffTail δ x R p
          ∂(polymerMeasure ϑ N s t ω)) ∂disorderLaw := by
    have hInt := integrable_polymer_heatPairingCutoffTail ϑ N
      (s := s) (t := t) hδ x R
    have hnonneg : 0 ≤ᵐ[disorderLaw] fun ω =>
        ∫ p, heatPairingCutoffTail δ x R p
          ∂(polymerMeasure ϑ N s t ω) := by
      filter_upwards [] with ω
      exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun p =>
        heatPairingCutoffTail_nonneg hδ x R p)
    exact ofReal_integral_eq_lintegral_ofReal hInt hnonneg
  have hbound : ∀ᶠ N : ℕ in atTop, ∫⁻ ω, ENNReal.ofReal
      (∫ p, heatPairingCutoffTail δ x R p
        ∂(polymerMeasure ϑ N s t ω)) ∂disorderLaw ≤ ENNReal.ofReal (ε / 2) := by
    filter_upwards [hpolyTail R hR] with N hN
    rw [← hpolyLin N]
    exact ENNReal.ofReal_le_ofReal hN
  have hlim : atTop.liminf (fun N : ℕ => ∫⁻ ω, ENNReal.ofReal
      (∫ p, heatPairingCutoffTail δ x R p
        ∂(polymerMeasure ϑ N s t ω)) ∂disorderLaw) ≤ ENNReal.ofReal (ε / 2) := by
    refine liminf_le_of_le (by isBoundedDefault) (fun b hb => ?_)
    obtain ⟨N, hN⟩ := (hb.and hbound).exists
    exact hN.1.trans hN.2
  have hfinal := hFatou.trans hlim
  rw [← hZlin] at hfinal
  have hreal : ∫ ω, ∫ p, heatPairingCutoffTail δ x R p ∂(Z s t ω) ∂P ≤ ε / 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hfinal
  linarith

private def heatBoundedTerminalCutoffRemainder (δ : ℝ) (x : Plane)
    (g : Plane →ᵇ ℝ) (R : ℝ) : Plane × Plane → ℝ := fun p =>
  heatKernel δ (p.1 - x) * g p.2 * (1 - ballCutoff R p.1 * ballCutoff R p.2)

/-- The integral error from a compact cutoff is bounded by the terminal sup norm times the
nonnegative two-coordinate heat-start tail. -/
theorem abs_integral_heatBoundedTerminal_cutoff_error_le
    (μ : Measure (Plane × Plane)) {δ : ℝ} (hδ : 0 < δ) (x : Plane)
    (g : Plane →ᵇ ℝ) (R : ℝ)
    (hK : Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x)) μ) :
    |(∫ p, heatKernel δ (p.1 - x) * g p.2 ∂μ) -
      ∫ p, heatBoundedTerminalCutoffTest δ x g R p ∂μ| ≤
        ‖g‖ * ∫ p, heatPairingCutoffTail δ x R p ∂μ := by
  have hFull := integrable_heatKernel_mul_boundedTerminal μ hδ x g hK
  have hCut := integrable_heatBoundedTerminalCutoffTest μ hδ x g R hK
  have hTail := integrable_heatPairingCutoffTail_of_heat hδ x R μ hK
  have hrem : Integrable (heatBoundedTerminalCutoffRemainder δ x g R) μ := by
    apply (hK.const_mul ‖g‖).mono'
      (((continuous_heatKernel δ).comp (continuous_fst.sub continuous_const)).mul
        (g.continuous.comp continuous_snd) |>.mul
          ((continuous_const : Continuous (fun _ : Plane × Plane => (1 : ℝ))).sub
            (((continuous_ballCutoff R).comp continuous_fst).mul
              ((continuous_ballCutoff R).comp continuous_snd))) |>.measurable.aestronglyMeasurable)
    filter_upwards [] with p
    have hk := heatKernel_nonneg hδ.le (p.1 - x)
    have h1 := ballCutoff_mem_Icc R p.1
    have h2 := ballCutoff_mem_Icc R p.2
    have hprod : 0 ≤ ballCutoff R p.1 * ballCutoff R p.2 ∧
        ballCutoff R p.1 * ballCutoff R p.2 ≤ 1 := by
      constructor
      · exact mul_nonneg h1.1 h2.1
      · calc
          ballCutoff R p.1 * ballCutoff R p.2 ≤ ballCutoff R p.1 * 1 :=
            mul_le_mul_of_nonneg_left h2.2 h1.1
          _ ≤ 1 := by simpa using h1.2
    have hfac : 0 ≤ 1 - ballCutoff R p.1 * ballCutoff R p.2 ∧
        1 - ballCutoff R p.1 * ballCutoff R p.2 ≤ 1 := by constructor <;> linarith
    change |heatKernel δ (p.1 - x) * g p.2 *
      (1 - ballCutoff R p.1 * ballCutoff R p.2)| ≤ _
    rw [abs_mul, abs_mul, abs_of_nonneg hk, abs_of_nonneg hfac.1]
    calc
      heatKernel δ (p.1 - x) * |g p.2| *
          (1 - ballCutoff R p.1 * ballCutoff R p.2) ≤
        heatKernel δ (p.1 - x) * ‖g‖ *
          (1 - ballCutoff R p.1 * ballCutoff R p.2) := by
            calc
              _ ≤ (heatKernel δ (p.1 - x) * ‖g‖) *
                  (1 - ballCutoff R p.1 * ballCutoff R p.2) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (g.norm_coe_le_norm p.2) hk) hfac.1
              _ = _ := by ring
      _ = ‖g‖ * heatPairingCutoffTail δ x R p := by
        dsimp [heatPairingCutoffTail]
        ring
      _ ≤ ‖g‖ * heatKernel δ (p.1 - x) :=
        mul_le_mul_of_nonneg_left (heatPairingCutoffTail_le_heatKernel hδ x R p)
          (norm_nonneg _)
  have hdiff : (fun p : Plane × Plane => heatKernel δ (p.1 - x) * g p.2 -
      heatBoundedTerminalCutoffTest δ x g R p) =
      heatBoundedTerminalCutoffRemainder δ x g R := by
    funext p
    change heatKernel δ (p.1 - x) * g p.2 -
      (heatKernel δ (p.1 - x) * g p.2 * ballCutoff R p.1 * ballCutoff R p.2) =
      heatKernel δ (p.1 - x) * g p.2 *
        (1 - ballCutoff R p.1 * ballCutoff R p.2)
    ring
  have hremInt : Integrable
      (fun p : Plane × Plane => heatKernel δ (p.1 - x) * g p.2 -
        heatBoundedTerminalCutoffTest δ x g R p) μ := hFull.sub hCut
  have hEq : (∫ p, heatKernel δ (p.1 - x) * g p.2 ∂μ) -
      ∫ p, heatBoundedTerminalCutoffTest δ x g R p ∂μ =
      ∫ p, heatBoundedTerminalCutoffRemainder δ x g R p ∂μ := by
    rw [← integral_sub hFull hCut]
    exact integral_congr_ae (Filter.Eventually.of_forall fun p => congrFun hdiff p)
  calc
    |(∫ p, heatKernel δ (p.1 - x) * g p.2 ∂μ) -
      ∫ p, heatBoundedTerminalCutoffTest δ x g R p ∂μ| =
      ‖∫ p, heatBoundedTerminalCutoffRemainder δ x g R p ∂μ‖ := by
        rw [hEq, Real.norm_eq_abs]
    _ ≤ ∫ p, ‖heatBoundedTerminalCutoffRemainder δ x g R p‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ p, ‖g‖ * heatPairingCutoffTail δ x R p ∂μ := by
      apply integral_mono hrem.norm (hTail.const_mul ‖g‖)
      intro p
      have hk := heatKernel_nonneg hδ.le (p.1 - x)
      have h1 := ballCutoff_mem_Icc R p.1
      have h2 := ballCutoff_mem_Icc R p.2
      have hfac : 0 ≤ 1 - ballCutoff R p.1 * ballCutoff R p.2 := by
        have hprod0 := mul_nonneg h1.1 h2.1
        have hprod1 : ballCutoff R p.1 * ballCutoff R p.2 ≤ 1 := by
          calc
            ballCutoff R p.1 * ballCutoff R p.2 ≤ ballCutoff R p.1 * 1 :=
              mul_le_mul_of_nonneg_left h2.2 h1.1
            _ ≤ 1 := by simpa using h1.2
        linarith
      change ‖heatKernel δ (p.1 - x) * g p.2 *
        (1 - ballCutoff R p.1 * ballCutoff R p.2)‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg hk, abs_of_nonneg hfac]
      calc
        heatKernel δ (p.1 - x) * |g p.2| *
            (1 - ballCutoff R p.1 * ballCutoff R p.2) ≤
          heatKernel δ (p.1 - x) * ‖g‖ *
            (1 - ballCutoff R p.1 * ballCutoff R p.2) := by
              calc
                _ ≤ (heatKernel δ (p.1 - x) * ‖g‖) *
                    (1 - ballCutoff R p.1 * ballCutoff R p.2) :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left (g.norm_coe_le_norm p.2) hk) hfac
                _ = _ := by ring
        _ = ‖g‖ * heatPairingCutoffTail δ x R p := by
          dsimp [heatPairingCutoffTail]
          ring
    _ = ‖g‖ * ∫ p, heatPairingCutoffTail δ x R p ∂μ := integral_const_mul _ _

end Critical2DKPZ.SHF.Positivity

end
