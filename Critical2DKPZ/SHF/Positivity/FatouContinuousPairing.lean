/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Positivity.LawFatou
public import Critical2DKPZ.SHF.Positivity.MeasurablePairing
public import Critical2DKPZ.SHF.Positivity.CompactConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Tactic

/-! # Fatou in law for integrable nonnegative continuous pairings -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported ENNReal Topology

namespace Critical2DKPZ.SHF.Positivity

private def continuousCutoffTest (f : Plane × Plane → ℝ) (hf : Continuous f) (R : ℝ) :
    C_c(Plane × Plane, ℝ) where
  toFun p := f p * ballCutoff R p.1 * ballCutoff R p.2
  continuous_toFun := hf.mul ((continuous_ballCutoff R).comp continuous_fst) |>.mul
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
      change f p * ballCutoff R p.1 * ballCutoff R p.2 = 0
      simp [hzero]
    · rw [Metric.mem_closedBall, dist_zero_right]
      by_contra hn
      have hzero : ballCutoff R p.2 = 0 :=
        ballCutoff_eq_zero_of_le_norm (le_of_lt (lt_of_not_ge hn))
      apply hp
      change f p * ballCutoff R p.1 * ballCutoff R p.2 = 0
      simp [hzero]

private theorem continuousCutoffTest_nonneg (f : Plane × Plane → ℝ) (hf : Continuous f)
    (hf0 : ∀ p, 0 ≤ f p) (R : ℝ) (p : Plane × Plane) :
    0 ≤ continuousCutoffTest f hf R p := by
  have h1 := ballCutoff_mem_Icc R p.1
  have h2 := ballCutoff_mem_Icc R p.2
  exact mul_nonneg (mul_nonneg (hf0 p) h1.1) h2.1

private theorem continuousCutoffTest_le (f : Plane × Plane → ℝ) (hf : Continuous f)
    (hf0 : ∀ p, 0 ≤ f p) (R : ℝ) (p : Plane × Plane) :
    continuousCutoffTest f hf R p ≤ f p := by
  have h1 := ballCutoff_mem_Icc R p.1
  have h2 := ballCutoff_mem_Icc R p.2
  have hprod : ballCutoff R p.1 * ballCutoff R p.2 ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul h1.2 h2.2 h2.1 (by norm_num)
      _ = 1 := by ring
  change f p * ballCutoff R p.1 * ballCutoff R p.2 ≤ f p
  calc
    _ = f p * (ballCutoff R p.1 * ballCutoff R p.2) := by ring
    _ ≤ f p * 1 := mul_le_mul_of_nonneg_left hprod (hf0 p)
    _ = f p := by ring

private theorem continuousCutoffTest_mono (f : Plane × Plane → ℝ) (hf : Continuous f)
    (hf0 : ∀ p, 0 ≤ f p)
    {R S : ℝ} (hRS : R ≤ S) (p : Plane × Plane) :
    continuousCutoffTest f hf R p ≤ continuousCutoffTest f hf S p := by
  have hc1 := ballCutoff_mono_radius hRS p.1
  have hc2 := ballCutoff_mono_radius hRS p.2
  have hn1 := ballCutoff_mem_Icc R p.1
  have hn2 := ballCutoff_mem_Icc R p.2
  have hprod : ballCutoff R p.1 * ballCutoff R p.2 ≤
      ballCutoff S p.1 * ballCutoff S p.2 :=
    mul_le_mul hc1 hc2 hn2.1 (ballCutoff_mem_Icc S p.1).1
  change f p * ballCutoff R p.1 * ballCutoff R p.2 ≤ _
  calc
    _ = f p * (ballCutoff R p.1 * ballCutoff R p.2) := by ring
    _ ≤ f p * (ballCutoff S p.1 * ballCutoff S p.2) :=
      mul_le_mul_of_nonneg_left hprod (hf0 p)
    _ = f p * ballCutoff S p.1 * ballCutoff S p.2 := by ring

/-- Fatou in law extends from compact tests to a nonnegative continuous pairing when that pairing
is integrable almost surely on both the SHF and polymer sides. -/
theorem isCriticalSHF_integrable_lintegral_pairing_le_liminf
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (f : Plane × Plane → ℝ) (hf : Continuous f)
    (hf0 : ∀ p, 0 ≤ f p)
    (hZint : ∀ᵐ ω ∂P, Integrable f (Z s t ω))
    (hpolyInt : ∀ N, ∀ᵐ ω ∂disorderLaw, Integrable f (polymerMeasure ϑ N s t ω)) :
    ∫⁻ ω, ENNReal.ofReal (∫ p, f p ∂(Z s t ω)) ∂P ≤
      liminf (fun N : ℕ => ∫⁻ ω, ENNReal.ofReal
        (∫ p, f p ∂(polymerMeasure ϑ N s t ω)) ∂disorderLaw) atTop := by
  let A : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (∫ p, f p ∂(Z s t ω))
  let a : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ENNReal.ofReal (∫ p, continuousCutoffTest f hf (n : ℝ) p ∂(Z s t ω))
  have hcutInt (n : ℕ) : ∀ᵐ ω ∂P,
      Integrable (fun p : Plane × Plane => continuousCutoffTest f hf (n : ℝ) p)
        (Z s t ω) := by
    filter_upwards [hZint] with ω hω
    apply hω.mono'
      (continuousCutoffTest f hf (n : ℝ)).continuous_toFun.measurable.aestronglyMeasurable
    filter_upwards [] with p
    have h1 := ballCutoff_mem_Icc (n : ℝ) p.1
    have h2 := ballCutoff_mem_Icc (n : ℝ) p.2
    change ‖f p * ballCutoff (n : ℝ) p.1 * ballCutoff (n : ℝ) p.2‖ ≤ f p
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hf0 p) h1.1) h2.1)]
    exact continuousCutoffTest_le f hf hf0 (n : ℝ) p
  have haemeas (n : ℕ) : AEMeasurable (a n) P := by
    have hm := aemeasurable_integral_of_measurable_measure P (Z s t)
      (hZ.1 s t hs hst) (fun p => continuousCutoffTest f hf (n : ℝ) p)
      (continuousCutoffTest f hf (n : ℝ)).continuous_toFun.measurable (hcutInt n)
    change AEMeasurable (fun ω => ENNReal.ofReal
      (∫ p, continuousCutoffTest f hf (n : ℝ) p ∂(Z s t ω))) P
    exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable hm
  have hcutMono : Monotone (fun n : ℕ => fun p : Plane × Plane =>
      ENNReal.ofReal (continuousCutoffTest f hf (n : ℝ) p)) := by
    intro n m hnm p
    apply ENNReal.ofReal_le_ofReal
    exact continuousCutoffTest_mono f hf hf0 (by exact_mod_cast hnm) p
  have hstep : ∀ n, ∀ᵐ ω ∂P, a n ω ≤ a (n + 1) ω := by
    intro n
    filter_upwards [hZint] with ω hω
    have hIn (m : ℕ) : Integrable
        (fun p : Plane × Plane => continuousCutoffTest f hf (m : ℝ) p) (Z s t ω) := by
      apply hω.mono'
        (continuousCutoffTest f hf (m : ℝ)).continuous_toFun.measurable.aestronglyMeasurable
      filter_upwards [] with p
      have h1 := ballCutoff_mem_Icc (m : ℝ) p.1
      have h2 := ballCutoff_mem_Icc (m : ℝ) p.2
      change ‖f p * ballCutoff (m : ℝ) p.1 * ballCutoff (m : ℝ) p.2‖ ≤ f p
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hf0 p) h1.1) h2.1)]
      exact continuousCutoffTest_le f hf hf0 (m : ℝ) p
    have hreal := integral_mono (hIn n) (hIn (n + 1)) (fun p => by
      exact continuousCutoffTest_mono f hf hf0 (by exact_mod_cast (Nat.le_succ n)) p)
    change ENNReal.ofReal (∫ p, continuousCutoffTest f hf (n : ℝ) p ∂Z s t ω) ≤
      ENNReal.ofReal (∫ p, continuousCutoffTest f hf ((n + 1 : ℕ) : ℝ) p ∂Z s t ω)
    exact ENNReal.ofReal_le_ofReal hreal
  have haMono : ∀ᵐ ω ∂P, Monotone (fun n => a n ω) := by
    filter_upwards [ae_all_iff.2 hstep] with ω hω
    exact monotone_nat_of_le_succ hω
  have hinner : ∀ᵐ ω ∂P, (⨆ n : ℕ, a n ω) = A ω := by
    filter_upwards [hZint] with ω hω
    have hIn (n : ℕ) : Integrable
        (fun p : Plane × Plane => continuousCutoffTest f hf (n : ℝ) p) (Z s t ω) := by
      apply hω.mono'
        (continuousCutoffTest f hf (n : ℝ)).continuous_toFun.measurable.aestronglyMeasurable
      filter_upwards [] with p
      have h1 := ballCutoff_mem_Icc (n : ℝ) p.1
      have h2 := ballCutoff_mem_Icc (n : ℝ) p.2
      change ‖f p * ballCutoff (n : ℝ) p.1 * ballCutoff (n : ℝ) p.2‖ ≤ f p
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hf0 p) h1.1) h2.1)]
      exact continuousCutoffTest_le f hf hf0 (n : ℝ) p
    have hnonneg (n : ℕ) : 0 ≤ᵐ[Z s t ω]
        (fun p : Plane × Plane => continuousCutoffTest f hf (n : ℝ) p) :=
      Filter.Eventually.of_forall fun p => continuousCutoffTest_nonneg f hf hf0 (n : ℝ) p
    have hpoint (p : Plane × Plane) :
        (⨆ n : ℕ, ENNReal.ofReal (continuousCutoffTest f hf (n : ℝ) p)) =
          ENNReal.ofReal (f p) := by
      have h1 : Tendsto (fun n : ℕ => ballCutoff (n : ℝ) p.1) atTop (𝓝 1) := by
        convert (tendsto_ballCutoff p.1).comp tendsto_natCast_atTop_atTop using 1
        all_goals rfl
      have h2 : Tendsto (fun n : ℕ => ballCutoff (n : ℝ) p.2) atTop (𝓝 1) := by
        convert (tendsto_ballCutoff p.2).comp tendsto_natCast_atTop_atTop using 1
        all_goals rfl
      have hlim : Tendsto (fun n : ℕ => continuousCutoffTest f hf (n : ℝ) p)
          atTop (𝓝 (f p)) := by
        change Tendsto (fun n : ℕ => f p * ballCutoff (n : ℝ) p.1 *
          ballCutoff (n : ℝ) p.2) atTop (𝓝 (f p))
        simpa only [mul_one] using (tendsto_const_nhds.mul h1).mul h2
      have hlim' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim
      apply iSup_eq_of_forall_le_of_forall_lt_exists_gt
      · intro n
        apply ENNReal.ofReal_le_ofReal
        exact continuousCutoffTest_le f hf hf0 (n : ℝ) p
      · intro w hw
        obtain ⟨n, hn⟩ := (hlim'.eventually (isOpen_Ioi.mem_nhds hw)).exists
        exact ⟨n, hn⟩
    have hMCT : ∫⁻ p, ⨆ n : ℕ, ENNReal.ofReal
        (continuousCutoffTest f hf (n : ℝ) p) ∂(Z s t ω) =
        ⨆ n : ℕ, ∫⁻ p, ENNReal.ofReal (continuousCutoffTest f hf (n : ℝ) p)
          ∂(Z s t ω) :=
      lintegral_iSup (fun n => ENNReal.measurable_ofReal.comp
        (continuousCutoffTest f hf (n : ℝ)).continuous_toFun.measurable) hcutMono
    have hterm (n : ℕ) : ∫⁻ p, ENNReal.ofReal
        (continuousCutoffTest f hf (n : ℝ) p) ∂(Z s t ω) = a n ω := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hIn n) (hnonneg n)]
    have hsup : (⨆ n : ℕ, a n ω) = ⨆ n : ℕ, ∫⁻ p, ENNReal.ofReal
        (continuousCutoffTest f hf (n : ℝ) p) ∂(Z s t ω) := by
      apply iSup_congr
      intro n
      exact (hterm n).symm
    calc
      (⨆ n : ℕ, a n ω) = ⨆ n : ℕ, ∫⁻ p, ENNReal.ofReal
          (continuousCutoffTest f hf (n : ℝ) p) ∂(Z s t ω) := hsup
      _ = ∫⁻ p, ⨆ n : ℕ, ENNReal.ofReal
          (continuousCutoffTest f hf (n : ℝ) p) ∂(Z s t ω) := hMCT.symm
      _ = A ω := by
        dsimp [A]
        calc
          (∫⁻ p, ⨆ n : ℕ, ENNReal.ofReal
              (continuousCutoffTest f hf (n : ℝ) p) ∂(Z s t ω)) =
              ∫⁻ p, ENNReal.ofReal (f p) ∂(Z s t ω) := by
                apply lintegral_congr_ae
                exact Filter.Eventually.of_forall hpoint
          _ = ENNReal.ofReal (∫ p, f p ∂(Z s t ω)) := by
            exact (ofReal_integral_eq_lintegral_ofReal hω
              (Filter.Eventually.of_forall hf0)).symm
  have houter : ∫⁻ ω, ⨆ n : ℕ, a n ω ∂P = ⨆ n : ℕ, ∫⁻ ω, a n ω ∂P :=
    lintegral_iSup' haemeas haMono
  have hleft : ∫⁻ ω, A ω ∂P = ⨆ n : ℕ, ∫⁻ ω, a n ω ∂P := by
    calc
      _ = ∫⁻ ω, ⨆ n : ℕ, a n ω ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hinner] with ω hω
        exact hω.symm
      _ = ⨆ n : ℕ, ∫⁻ ω, a n ω ∂P := houter
  have hcompact (n : ℕ) : ∫⁻ ω, a n ω ∂P ≤
      liminf (fun N : ℕ => ∫⁻ ω, ENNReal.ofReal
        (∫ p, continuousCutoffTest f hf (n : ℝ) p
          ∂(polymerMeasure ϑ N s t ω)) ∂disorderLaw) atTop :=
    isCriticalSHF_lintegral_pairing_le_liminf ϑ P Z hZ hs hst
      (continuousCutoffTest f hf (n : ℝ))
      (fun p => continuousCutoffTest_nonneg f hf hf0 (n : ℝ) p)
  have hpoly (n N : ℕ) : ∫⁻ ω, ENNReal.ofReal
      (∫ p, continuousCutoffTest f hf (n : ℝ) p
        ∂(polymerMeasure ϑ N s t ω)) ∂disorderLaw ≤
      ∫⁻ ω, ENNReal.ofReal (∫ p, f p ∂(polymerMeasure ϑ N s t ω)) ∂disorderLaw := by
    apply lintegral_mono_ae
    filter_upwards [hpolyInt N] with ω hω
    have hcut : Integrable (fun p : Plane × Plane => continuousCutoffTest f hf (n : ℝ) p)
        (polymerMeasure ϑ N s t ω) := by
      apply hω.mono'
        (continuousCutoffTest f hf (n : ℝ)).continuous_toFun.measurable.aestronglyMeasurable
      filter_upwards [] with p
      have h1 := ballCutoff_mem_Icc (n : ℝ) p.1
      have h2 := ballCutoff_mem_Icc (n : ℝ) p.2
      change ‖f p * ballCutoff (n : ℝ) p.1 * ballCutoff (n : ℝ) p.2‖ ≤ f p
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hf0 p) h1.1) h2.1)]
      exact continuousCutoffTest_le f hf hf0 (n : ℝ) p
    have hreal := integral_mono hcut hω (fun p =>
      continuousCutoffTest_le f hf hf0 (n : ℝ) p)
    exact ENNReal.ofReal_le_ofReal hreal
  have hliminf : (⨆ n : ℕ, liminf (fun N : ℕ => ∫⁻ ω,
      ENNReal.ofReal (∫ p, continuousCutoffTest f hf (n : ℝ) p
        ∂(polymerMeasure ϑ N s t ω)) ∂disorderLaw) atTop) ≤
      liminf (fun N : ℕ => ∫⁻ ω, ENNReal.ofReal
        (∫ p, f p ∂(polymerMeasure ϑ N s t ω)) ∂disorderLaw) atTop := by
    apply iSup_le
    intro n
    exact liminf_le_liminf (Filter.Eventually.of_forall fun N => hpoly n N)
      (by isBoundedDefault) (by isBoundedDefault)
  calc
    _ = ⨆ n : ℕ, ∫⁻ ω, a n ω ∂P := hleft
    _ ≤ ⨆ n : ℕ, liminf (fun N : ℕ => ∫⁻ ω,
        ENNReal.ofReal (∫ p, continuousCutoffTest f hf (n : ℝ) p
          ∂(polymerMeasure ϑ N s t ω)) ∂disorderLaw) atTop := by
      apply iSup_le
      intro n
      exact (hcompact n).trans (le_iSup (fun j : ℕ => liminf (fun N : ℕ => ∫⁻ ω,
        ENNReal.ofReal (∫ p, continuousCutoffTest f hf (j : ℝ) p
          ∂(polymerMeasure ϑ N s t ω)) ∂disorderLaw) atTop) n)
    _ ≤ liminf (fun N : ℕ => ∫⁻ ω, ENNReal.ofReal
        (∫ p, f p ∂(polymerMeasure ϑ N s t ω)) ∂disorderLaw) atTop := hliminf

end Critical2DKPZ.SHF.Positivity

end
