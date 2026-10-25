/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.MollifiedHeatConnectorConvergence
import Mathlib.Tactic

/-! Mollification of a fixed-slab connector converges to its continuum counterpart. -/

@[expose] public section

open MeasureTheory
open Filter
open ProbabilityTheory
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.SHF.Tsai
open scoped Topology CompactlySupported

namespace Critical2DKPZ.SHF.Flow

/-- A uniform pointwise connector error gives the corresponding finite-measure pairing error. -/
private theorem abs_kernelProductPairing_sub_le
    (μ ν : Measure (Plane × Plane)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ κ₂ : Plane → Plane → ℝ)
    (hκm : Measurable (fun p : Plane × Plane => κ p.1 p.2))
    (hκ₂m : Measurable (fun p : Plane × Plane => κ₂ p.1 p.2))
    (Φ : C_c(Plane × Plane, ℝ)) (Cκ Cκ₂ M δ : ℝ)
    (hM : 0 ≤ M) (hΦ : ∀ p, |Φ p| ≤ M)
    (hκ : ∀ x y, |κ x y| ≤ Cκ) (hκ₂ : ∀ x y, |κ₂ x y| ≤ Cκ₂)
    (hclose : ∀ x y, |κ x y - κ₂ x y| ≤ δ) :
    |kernelProductPairing μ κ ν Φ - kernelProductPairing μ κ₂ ν Φ| ≤
      M * δ * (μ.real Set.univ * ν.real Set.univ) := by
  let μν : Measure ((Plane × Plane) × (Plane × Plane)) := μ.prod ν
  let Fκ : ((Plane × Plane) × (Plane × Plane)) → ℝ := fun q =>
    Φ (q.1.1, q.2.2) * κ q.1.2 q.2.1
  let Fκ₂ : ((Plane × Plane) × (Plane × Plane)) → ℝ := fun q =>
    Φ (q.1.1, q.2.2) * κ₂ q.1.2 q.2.1
  have houter : Measurable (fun q : (Plane × Plane) × (Plane × Plane) =>
      (q.1.1, q.2.2)) := by fun_prop
  have hmiddle : Measurable (fun q : (Plane × Plane) × (Plane × Plane) =>
      (q.1.2, q.2.1)) := by fun_prop
  have hFκm : Measurable Fκ := by
    dsimp [Fκ]
    exact (Φ.measurable.comp houter).mul (hκm.comp hmiddle)
  have hFκ₂m : Measurable Fκ₂ := by
    dsimp [Fκ₂]
    exact (Φ.measurable.comp houter).mul (hκ₂m.comp hmiddle)
  have hFκbound (q : (Plane × Plane) × (Plane × Plane)) : |Fκ q| ≤ M * Cκ := by
    dsimp [Fκ]
    rw [abs_mul]
    exact mul_le_mul (hΦ _) (hκ _ _) (abs_nonneg _) hM
  have hFκ₂bound (q : (Plane × Plane) × (Plane × Plane)) : |Fκ₂ q| ≤ M * Cκ₂ := by
    dsimp [Fκ₂]
    rw [abs_mul]
    exact mul_le_mul (hΦ _) (hκ₂ _ _) (abs_nonneg _) hM
  have hFκint : Integrable Fκ μν :=
    Integrable.of_bound hFκm.aestronglyMeasurable (M * Cκ)
      (Filter.Eventually.of_forall hFκbound)
  have hFκ₂int : Integrable Fκ₂ μν :=
    Integrable.of_bound hFκ₂m.aestronglyMeasurable (M * Cκ₂)
      (Filter.Eventually.of_forall hFκ₂bound)
  have hpair : kernelProductPairing μ κ ν Φ - kernelProductPairing μ κ₂ ν Φ =
      ∫ q, Φ (q.1.1, q.2.2) * (κ q.1.2 q.2.1 - κ₂ q.1.2 q.2.1) ∂μν := by
    rw [kernelProductPairing, kernelProductPairing, ← integral_sub hFκint hFκ₂int]
    apply integral_congr_ae
    filter_upwards [] with q
    dsimp [Fκ, Fκ₂]
    ring
  have hdiffInt : Integrable
      (fun q : (Plane × Plane) × (Plane × Plane) =>
        Φ (q.1.1, q.2.2) * (κ q.1.2 q.2.1 - κ₂ q.1.2 q.2.1)) μν := by
    convert hFκint.sub hFκ₂int using 1
    ext q
    dsimp [Fκ, Fκ₂]
    ring
  have hconstInt : Integrable (fun _ : (Plane × Plane) × (Plane × Plane) => M * δ) μν :=
    integrable_const _
  have hpoint (q : (Plane × Plane) × (Plane × Plane)) :
      |Φ (q.1.1, q.2.2) * (κ q.1.2 q.2.1 - κ₂ q.1.2 q.2.1)| ≤ M * δ := by
    rw [abs_mul]
    exact mul_le_mul (hΦ _) (hclose _ _) (abs_nonneg _) hM
  have hrealProd : μν.real Set.univ = μ.real Set.univ * ν.real Set.univ := by
    simpa only [μν, Set.univ_prod_univ] using
      (measureReal_prod_prod (μ := μ) (ν := ν) Set.univ Set.univ)
  calc
    _ = |∫ q, Φ (q.1.1, q.2.2) *
          (κ q.1.2 q.2.1 - κ₂ q.1.2 q.2.1) ∂μν| := by rw [hpair]
    _ ≤ ∫ q, |Φ (q.1.1, q.2.2) *
          (κ q.1.2 q.2.1 - κ₂ q.1.2 q.2.1)| ∂μν := abs_integral_le_integral_abs
    _ ≤ ∫ _ : (Plane × Plane) × (Plane × Plane), M * δ ∂μν := by
      apply integral_mono hdiffInt.abs hconstInt
      intro q
      exact hpoint q
    _ = M * δ * (μ.real Set.univ * ν.real Set.univ) := by
      rw [integral_const, hrealProd]
      ring

/-- At a fixed positive slab width, the smoothed and raw slab connectors converge uniformly over
all endpoint locations as the mollifier scale shrinks and the lattice scale grows. -/
theorem tendsto_slabSmoothedConnector_sub_slabMeanKernel_uniform
    (ϑ : ℝ) {t : ℝ} (ht : 0 ≤ t) {v : ℝ} (hv : 0 < v)
    (w : Plane → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∫ x, w x = 1) :
    ∀ ε > 0, ∃ η > 0, ∀ e : ℝ, 0 < e → e < η →
      ∀ᶠ N : ℕ in atTop, ∀ a b,
        |slabSmoothedConnector ϑ N t (t + v)
            (fun x => e⁻¹ ^ 2 * w (e⁻¹ • x)) a b -
          slabMeanKernel ϑ N t (t + v) a b| < ε := by
  intro ε hε
  obtain ⟨Cs, cs, hcs, hsmoothed⟩ :=
    exists_slabSmoothedConnector_gaussianBound ϑ ht hv w hw hwc hw0 hw1
  obtain ⟨Cr, cr, hcr, hraw⟩ := exists_slabMeanKernel_gaussianBound ϑ ht hv
  have hCs : 0 ≤ Cs := by
    have h := hsmoothed 1 one_pos (by norm_num) 0 (0 : Plane) (0 : Plane)
    simpa using (abs_nonneg _).trans h
  have hCr : 0 ≤ Cr := by
    have h := hraw 0 (0 : Plane) (0 : Plane)
    simpa using (abs_nonneg _).trans h
  let C := max Cs Cr
  let c := min cs cr
  have hC : 0 ≤ C := le_trans hCs (le_max_left _ _)
  have hc : 0 < c := lt_min hcs hcr
  have hdecay : Tendsto (fun R : ℝ => C * Real.exp (-c * R ^ 2)) atTop (𝓝 0) := by
    have hpow : Tendsto (fun R : ℝ => R ^ 2) atTop atTop :=
      tendsto_pow_atTop (by norm_num : 2 ≠ 0)
    have harg : Tendsto (fun R : ℝ => -c * R ^ 2) atTop atBot :=
      hpow.const_mul_atTop_of_neg (neg_lt_zero.mpr hc)
    have hexp : Tendsto (fun R : ℝ => Real.exp (-c * R ^ 2)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp harg
    simpa using tendsto_const_nhds.mul hexp
  have hsmall : ∀ᶠ R : ℝ in atTop, C * Real.exp (-c * R ^ 2) < ε / 3 := by
    filter_upwards [hdecay.eventually (Metric.ball_mem_nhds 0 (by positivity : 0 < ε / 3))]
      with R hR
    have hdist : |C * Real.exp (-c * R ^ 2)| < ε / 3 := by
      simpa only [Real.dist_eq, sub_zero] using hR
    rw [abs_of_nonneg (mul_nonneg hC (Real.exp_nonneg _))] at hdist
    exact hdist
  obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.1 hsmall
  let R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have htail : C * Real.exp (-c * R ^ 2) < ε / 3 :=
    hR₀ R (le_max_left _ _)
  obtain ⟨η₀, hη₀, hlocal⟩ :=
    tendsto_slabSmoothedConnector_sub_slabMeanKernel_uniformOn_differenceBall
      ϑ ht hv w hw hwc hw0 hw1 R hR (ε / 3) (by positivity)
  let η := min η₀ 1
  have hη : 0 < η := lt_min hη₀ one_pos
  refine ⟨η, hη, ?_⟩
  intro e he heη
  have heη₀ : e < η₀ := lt_of_lt_of_le heη (min_le_left _ _)
  have heone : e ≤ 1 := (lt_of_lt_of_le heη (min_le_right _ _)).le
  filter_upwards [hlocal e he heη₀] with N hN
  intro a b
  by_cases hdist : ‖b - a‖ ≤ R
  · exact (hN a b hdist).trans (by linarith)
  · have hlarge : R < ‖b - a‖ := lt_of_not_ge hdist
    have hsq : R ^ 2 ≤ ‖b - a‖ ^ 2 := by
      exact (sq_le_sq₀ hR (norm_nonneg _)).mpr hlarge.le
    have hexpS : Real.exp (-cs * ‖b - a‖ ^ 2) ≤ Real.exp (-c * R ^ 2) := by
      apply Real.exp_le_exp.mpr
      have htime : -cs * ‖b - a‖ ^ 2 ≤ -c * ‖b - a‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left _ _)) (sq_nonneg _)
      have hspace : -c * ‖b - a‖ ^ 2 ≤ -c * R ^ 2 :=
        mul_le_mul_of_nonpos_left hsq (by linarith)
      exact htime.trans hspace
    have hexpR : Real.exp (-cr * ‖b - a‖ ^ 2) ≤ Real.exp (-c * R ^ 2) := by
      apply Real.exp_le_exp.mpr
      have htime : -cr * ‖b - a‖ ^ 2 ≤ -c * ‖b - a‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right _ _)) (sq_nonneg _)
      have hspace : -c * ‖b - a‖ ^ 2 ≤ -c * R ^ 2 :=
        mul_le_mul_of_nonpos_left hsq (by linarith)
      exact htime.trans hspace
    have hSbound :
        |slabSmoothedConnector ϑ N t (t + v)
            (fun x => e⁻¹ ^ 2 * w (e⁻¹ • x)) a b| < ε / 3 := by
      calc
        _ ≤ Cs * Real.exp (-cs * ‖b - a‖ ^ 2) := hsmoothed e he heone N a b
        _ ≤ Cs * Real.exp (-c * R ^ 2) :=
          mul_le_mul_of_nonneg_left hexpS hCs
        _ ≤ C * Real.exp (-c * R ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
        _ < ε / 3 := htail
    have hRbound :
        |slabMeanKernel ϑ N t (t + v) a b| < ε / 3 := by
      calc
        _ ≤ Cr * Real.exp (-cr * ‖b - a‖ ^ 2) := hraw N a b
        _ ≤ Cr * Real.exp (-c * R ^ 2) :=
          mul_le_mul_of_nonneg_left hexpR hCr
        _ ≤ C * Real.exp (-c * R ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _)
        _ < ε / 3 := htail
    calc
      _ ≤ |slabSmoothedConnector ϑ N t (t + v)
            (fun x => e⁻¹ ^ 2 * w (e⁻¹ • x)) a b| +
          |slabMeanKernel ϑ N t (t + v) a b| := by
        calc
          _ ≤ |slabSmoothedConnector ϑ N t (t + v)
                (fun x => e⁻¹ ^ 2 * w (e⁻¹ • x)) a b - 0| +
              |0 - slabMeanKernel ϑ N t (t + v) a b| := abs_sub_le _ _ _
          _ = _ := by simp
      _ < ε := by linarith

/-- At a fixed positive slab width, the two separated products become close in annealed
second moment as the mollifier shrinks. -/
theorem slabSmoothedProduct_sub_slabProduct_sq_small_of (ϑ : ℝ)
    (_hPolymerMomentInput : PolymerMomentLimit ϑ) (_hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s t u : ℝ} (hs : 0 ≤ s) (hst : s < t) (_htu : t < u)
    (Φ : C_c(Plane × Plane, ℝ)) (w : Plane → ℝ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∫ x, w x = 1) {v : ℝ} (hv : 0 < v)
    (hvu : t + v < u) :
    ∀ ε > 0, ∃ η > 0, ∀ e : ℝ, 0 < e → e < η → ∀ᶠ N : ℕ in atTop,
      ∫ ω, (kernelProductPairing (polymerMeasure ϑ N s t ω)
          (fun a b => ∫ y, e⁻¹ ^ 2 * w (e⁻¹ • (a - y)) *
            slabMeanKernel ϑ N t (t + v) y b)
          (polymerMeasure ϑ N (t + v) u ω) Φ -
        kernelProductPairing (polymerMeasure ϑ N s t ω)
          (slabMeanKernel ϑ N t (t + v))
          (polymerMeasure ϑ N (t + v) u ω) Φ) ^ 2 ∂disorderLaw ≤ ε := by
  classical
  intro ε hε
  obtain ⟨Cmass, hCmass, hmass⟩ :=
    eventually_slabOuterEndpointMassProduct_sq_bound ϑ hs hst
      (by linarith : t < t + v) hvu Φ
  obtain ⟨CΦ, hΦnorm⟩ :=
    Φ.continuous.bounded_above_of_compact_support Φ.hasCompactSupport
  let M := max CΦ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hΦ (p : Plane × Plane) : |Φ p| ≤ M := by
    calc
      |Φ p| = ‖Φ p‖ := (Real.norm_eq_abs _).symm
      _ ≤ CΦ := hΦnorm p
      _ ≤ M := le_max_left _ _
  let δ := Real.sqrt ε / ((M + 1) * Real.sqrt Cmass)
  have hδ : 0 < δ := by
    dsimp [δ]
    apply div_pos (Real.sqrt_pos.2 hε)
    positivity
  have hcoeff : (M * δ) ^ 2 * Cmass ≤ ε := by
    have hsqrtε : (Real.sqrt ε) ^ 2 = ε := Real.sq_sqrt hε.le
    have hsqrtC : (Real.sqrt Cmass) ^ 2 = Cmass := Real.sq_sqrt hCmass.le
    have hratio0 : 0 ≤ M / (M + 1) := div_nonneg hM (by positivity)
    have hratio1 : M / (M + 1) ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hratioSq : (M / (M + 1)) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (M / (M + 1) - 1)]
    dsimp [δ]
    have heq :
        (M * (Real.sqrt ε / ((M + 1) * Real.sqrt Cmass))) ^ 2 * Cmass =
          ε * (M / (M + 1)) ^ 2 := by
      field_simp
      rw [hsqrtε, hsqrtC]
      ring
    rw [heq]
    exact mul_le_of_le_one_right (by positivity) hratioSq
  obtain ⟨η₀, hη₀, hclose⟩ :=
    tendsto_slabSmoothedConnector_sub_slabMeanKernel_uniform ϑ
      (le_trans hs hst.le) hv w hw.continuous hwc hw0 hw1 δ hδ
  let η := min η₀ 1
  have hη : 0 < η := lt_min hη₀ one_pos
  obtain ⟨Cs, cs, hcs, hsmoothed⟩ :=
    exists_slabSmoothedConnector_gaussianBound ϑ (le_trans hs hst.le) hv
      w hw.continuous hwc hw0 hw1
  obtain ⟨Cr, cr, hcr, hraw⟩ :=
    exists_slabMeanKernel_gaussianBound ϑ (le_trans hs hst.le) hv
  have hCs : 0 ≤ Cs := by
    have h := hsmoothed 1 one_pos (by norm_num) 0 (0 : Plane) (0 : Plane)
    simpa using (abs_nonneg _).trans h
  have hCr : 0 ≤ Cr := by
    have h := hraw 0 (0 : Plane) (0 : Plane)
    simpa using (abs_nonneg _).trans h
  refine ⟨η, hη, ?_⟩
  intro e he heη
  have heη₀ : e < η₀ := lt_of_lt_of_le heη (min_le_left _ _)
  have heone : e ≤ 1 := (lt_of_lt_of_le heη (min_le_right _ _)).le
  let we : Plane → ℝ := fun x => e⁻¹ ^ 2 * w (e⁻¹ • x)
  have hwe : Continuous we := by
    dsimp [we]
    exact continuous_const.mul (hw.continuous.comp
      ((continuous_const : Continuous fun _ : Plane => e⁻¹).smul continuous_id))
  have hwec : HasCompactSupport we := by
    have hcomp : HasCompactSupport (fun x : Plane => w (e⁻¹ • x)) :=
      hwc.comp_smul (inv_ne_zero he.ne')
    change HasCompactSupport (fun x : Plane => (e⁻¹ ^ 2 : ℝ) • w (e⁻¹ • x))
    exact HasCompactSupport.smul_left
      (f := fun _ : Plane => (e⁻¹ ^ 2 : ℝ)) hcomp
  have huniform := hclose e he heη₀
  filter_upwards [hmass, huniform] with N hmassN huniformN
  have hleftInt : Integrable (fun ω =>
      (((polymerMeasure ϑ N s t ω
          ((Prod.fst '' tsupport Φ) ×ˢ (Set.univ : Set Plane))).toReal) *
        ((polymerMeasure ϑ N (t + v) u ω
          ((Set.univ : Set Plane) ×ˢ (Prod.snd '' tsupport Φ))).toReal)) ^ 2)
      disorderLaw := by simpa using hmassN.1
  have hleftBound : ∫ ω,
      (((polymerMeasure ϑ N s t ω
          ((Prod.fst '' tsupport Φ) ×ˢ (Set.univ : Set Plane))).toReal) *
        ((polymerMeasure ϑ N (t + v) u ω
          ((Set.univ : Set Plane) ×ˢ (Prod.snd '' tsupport Φ))).toReal)) ^ 2
      ∂disorderLaw ≤ Cmass := by simpa using hmassN.2
  let X : Disorder → ℝ := fun ω =>
    (polymerMeasure ϑ N s t ω
      ((Prod.fst '' tsupport Φ) ×ˢ (Set.univ : Set Plane))).toReal
  let Y : Disorder → ℝ := fun ω =>
    (polymerMeasure ϑ N (t + v) u ω
      ((Set.univ : Set Plane) ×ˢ (Prod.snd '' tsupport Φ))).toReal
  let E : Disorder → ℝ := fun ω =>
    (kernelProductPairing (polymerMeasure ϑ N s t ω)
        (fun a b => ∫ y, we (a - y) * slabMeanKernel ϑ N t (t + v) y b)
        (polymerMeasure ϑ N (t + v) u ω) Φ -
      kernelProductPairing (polymerMeasure ϑ N s t ω)
        (slabMeanKernel ϑ N t (t + v))
        (polymerMeasure ϑ N (t + v) u ω) Φ) ^ 2
  have hEint : Integrable E disorderLaw := by
    dsimp [E]
    exact integrable_slabSmoothedProduct_sub_slabProduct_sq
      ϑ N hs hst Φ w hw.continuous hwc hv hvu he
  have hmassInt : Integrable (fun ω => (X ω * Y ω) ^ 2) disorderLaw := by
    simpa [X, Y] using hleftInt
  have hmassBound : ∫ ω, (X ω * Y ω) ^ 2 ∂disorderLaw ≤ Cmass := by
    simpa [X, Y] using hleftBound
  have hrightInt : Integrable (fun ω => (M * δ) ^ 2 * (X ω * Y ω) ^ 2)
      disorderLaw := hmassInt.const_mul _
  have hrightBound : ∫ ω, (M * δ) ^ 2 * (X ω * Y ω) ^ 2 ∂disorderLaw ≤ ε := by
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left hmassBound (sq_nonneg _)).trans hcoeff
  have hpoint (ω : Disorder) : E ω ≤ (M * δ) ^ 2 * (X ω * Y ω) ^ 2 := by
    let μ₀ := polymerMeasure ϑ N s t ω
    let ν₀ := polymerMeasure ϑ N (t + v) u ω
    let A : Set Plane := Prod.fst '' tsupport Φ
    let B : Set Plane := Prod.snd '' tsupport Φ
    let μ := μ₀.restrict (A ×ˢ (Set.univ : Set Plane))
    let ν := ν₀.restrict ((Set.univ : Set Plane) ×ˢ B)
    have hA : IsCompact A := Φ.hasCompactSupport.image continuous_fst
    have hB : IsCompact B := Φ.hasCompactSupport.image continuous_snd
    have hμfiniteENN : μ₀ (A ×ˢ (Set.univ : Set Plane)) < ⊤ := by
      exact polymerMeasure_finite_first_compact ϑ N s t ω A hA
    have hνfiniteENN : ν₀ ((Set.univ : Set Plane) ×ˢ B) < ⊤ := by
      exact polymerMeasure_finite_second_compact ϑ N (t + v) u ω B hB
    have hμfinite : IsFiniteMeasure μ := ⟨by
      rw [Measure.restrict_apply_univ]
      simpa [μ] using hμfiniteENN⟩
    have hνfinite : IsFiniteMeasure ν := ⟨by
      rw [Measure.restrict_apply_univ]
      simpa [ν] using hνfiniteENN⟩
    have hμ₀SFinite : SFinite μ₀ := by
      change SFinite ((volume : Measure (Plane × Plane)).withDensity fun p =>
        ENNReal.ofReal (rescaledP2P ϑ N s t p ω))
      have hvol : SFinite (volume : Measure (Plane × Plane)) := by infer_instance
      infer_instance
    have hν₀SFinite : SFinite ν₀ := by
      change SFinite ((volume : Measure (Plane × Plane)).withDensity fun p =>
        ENNReal.ofReal (rescaledP2P ϑ N (t + v) u p ω))
      have hvol : SFinite (volume : Measure (Plane × Plane)) := by infer_instance
      infer_instance
    have houter : ∀ p, Φ p ≠ 0 → p.1 ∈ A ∧ p.2 ∈ B := by
      intro p hp
      have hpK : p ∈ tsupport Φ := subset_tsupport Φ (Function.mem_support.mpr hp)
      exact ⟨⟨p, hpK, rfl⟩, ⟨p, hpK, rfl⟩⟩
    let κs : Plane → Plane → ℝ := fun a b =>
      slabSmoothedConnector ϑ N t (t + v) we a b
    let κr : Plane → Plane → ℝ := slabMeanKernel ϑ N t (t + v)
    have hκsm : Measurable (fun p : Plane × Plane => κs p.1 p.2) := by
      simpa [κs] using measurable_slabSmoothedConnector ϑ N t (t + v) we hwe hwec
    have hκraw : Measurable (fun p : Plane × Plane => κr p.1 p.2) := by
      let m := evenCeil ((N : ℝ) * (t + v)) - evenCeil ((N : ℝ) * t)
      have hsites : Measurable (fun p : Plane × Plane =>
          (latticePoint N p.1, latticePoint N p.2)) := by
        convert (((measurable_latticePoint N).comp measurable_fst).prodMk
          ((measurable_latticePoint N).comp measurable_snd)) using 1
        funext p
        rfl
      have hbase : Measurable (fun p : Plane × Plane =>
          (N : ℝ) / 4 * Critical2DKPZ.srwKernel m
            (latticePoint N p.2 - latticePoint N p.1)) := by
        convert (measurable_of_countable (fun z : Site × Site =>
          (N : ℝ) / 4 * Critical2DKPZ.srwKernel m (z.2 - z.1))).comp hsites using 1
        funext p
        rfl
      have heq : (fun p : Plane × Plane => κr p.1 p.2) = fun p =>
          (N : ℝ) / 4 * Critical2DKPZ.srwKernel m
            (latticePoint N p.2 - latticePoint N p.1) := by
        funext p
        exact slabMeanKernel_eq_srwKernel ϑ N t (t + v) p.1 p.2
      rw [heq]
      exact hbase
    have hCsbound (a b : Plane) : |κs a b| ≤ Cs := by
      calc
        |κs a b| ≤ Cs * Real.exp (-cs * ‖b - a‖ ^ 2) := by
          simpa [κs, we] using hsmoothed e he heone N a b
        _ ≤ Cs := by
          calc
            _ ≤ Cs * 1 := mul_le_mul_of_nonneg_left
              (Real.exp_le_one_iff.mpr
                (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcs.le) (sq_nonneg _))) hCs
            _ = Cs := by ring
    have hCrbound (a b : Plane) : |κr a b| ≤ Cr := by
      calc
        |κr a b| ≤ Cr * Real.exp (-cr * ‖b - a‖ ^ 2) := by simpa [κr] using hraw N a b
        _ ≤ Cr := by
          calc
            _ ≤ Cr * 1 := mul_le_mul_of_nonneg_left
              (Real.exp_le_one_iff.mpr
                (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcr.le) (sq_nonneg _))) hCr
            _ = Cr := by ring
    have hclose' (a b : Plane) : |κs a b - κr a b| ≤ δ := by
      simpa [κs, κr, we] using (huniformN a b).le
    have hrestrictS : kernelProductPairing μ₀ κs ν₀ Φ =
        kernelProductPairing μ κs ν Φ :=
      @kernelProductPairing_restrict_outer_support μ₀ ν₀ κs Φ A B
        hμ₀SFinite hν₀SFinite hA.measurableSet hB.measurableSet houter
    have hrestrictR : kernelProductPairing μ₀ κr ν₀ Φ =
        kernelProductPairing μ κr ν Φ :=
      @kernelProductPairing_restrict_outer_support μ₀ ν₀ κr Φ A B
        hμ₀SFinite hν₀SFinite hA.measurableSet hB.measurableSet houter
    have hX : μ.real Set.univ = X ω := by
      change (μ Set.univ).toReal = X ω
      rw [Measure.restrict_apply_univ]
    have hY : ν.real Set.univ = Y ω := by
      change (ν Set.univ).toReal = Y ω
      rw [Measure.restrict_apply_univ]
    have hpair := abs_kernelProductPairing_sub_le μ ν κs κr hκsm hκraw Φ Cs Cr M δ
      hM hΦ hCsbound hCrbound hclose'
    have hpair' :
        |kernelProductPairing μ₀ κs ν₀ Φ - kernelProductPairing μ₀ κr ν₀ Φ| ≤
          M * δ * (X ω * Y ω) := by
      rw [← hrestrictS, ← hrestrictR] at hpair
      simpa [hX, hY, mul_assoc] using hpair
    have hXnonneg : 0 ≤ X ω := ENNReal.toReal_nonneg
    have hYnonneg : 0 ≤ Y ω := ENNReal.toReal_nonneg
    have hcoeffnonneg : 0 ≤ M * δ := mul_nonneg hM hδ.le
    have hmassnonneg : 0 ≤ X ω * Y ω := mul_nonneg hXnonneg hYnonneg
    have hfactor : 0 ≤ M * δ * (X ω * Y ω) := mul_nonneg hcoeffnonneg hmassnonneg
    have hsq := (sq_le_sq₀ (abs_nonneg _) hfactor).mpr hpair'
    let Dω := kernelProductPairing μ₀ κs ν₀ Φ - kernelProductPairing μ₀ κr ν₀ Φ
    have hsq' : Dω ^ 2 ≤ (M * δ) ^ 2 * (X ω * Y ω) ^ 2 := by
      calc
        Dω ^ 2 = |Dω| ^ 2 := (sq_abs Dω).symm
        _ ≤ (M * δ * (X ω * Y ω)) ^ 2 := hsq
        _ = (M * δ) ^ 2 * (X ω * Y ω) ^ 2 := by ring
    simpa [E, Dω, κs, κr, we, slabSmoothedConnector, mul_assoc] using hsq'
  calc
    ∫ ω, E ω ∂disorderLaw ≤ ∫ ω, (M * δ) ^ 2 * (X ω * Y ω) ^ 2 ∂disorderLaw :=
      integral_mono hEint hrightInt hpoint
    _ ≤ ε := hrightBound


end Critical2DKPZ.SHF.Flow

end
