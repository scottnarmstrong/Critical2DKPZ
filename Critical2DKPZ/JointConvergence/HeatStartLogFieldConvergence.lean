/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.JointConvergence.HeatStartLogConvergence
public import Critical2DKPZ.JointConvergence.LogHeatFieldMeasurability
public import Critical2DKPZ.JointConvergence.HeatKernelTranslation
public import Critical2DKPZ.JointConvergence.MomentConvergence
public import Critical2DKPZ.Analysis.Lattice.Sampling
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Normed.Group.Bounded
import Critical2DKPZ.SHF.Positivity.MeasurablePairing
import Critical2DKPZ.SHF.Positivity.HeatBoundedIntegrability
import Critical2DKPZ.Smoothing.Measurability
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Spatially integrated logarithmic heat-start convergence -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Positivity
open scoped BigOperators BoundedContinuousFunction ENNReal Topology

namespace Critical2DKPZ.JointConvergence

/-- Mean spatial continuity of a polymer heat-start pairing, controlled by the first-marginal
mean identity and the `L¹` translation modulus of the heat kernel. -/
private theorem polymer_heatPairing_translation_l1_le (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (s T δ : ℝ) (hδ : 0 < δ) (x x' : Plane) (g : Plane →ᵇ ℝ) :
    Integrable (fun ω => |(∫ p, heatKernel δ (p.1 - x) * g p.2
        ∂polymerMeasure ϑ N s T ω) -
      (∫ p, heatKernel δ (p.1 - x') * g p.2
        ∂polymerMeasure ϑ N s T ω)|) disorderLaw ∧
    (∫ ω, |(∫ p, heatKernel δ (p.1 - x) * g p.2
        ∂polymerMeasure ϑ N s T ω) -
      (∫ p, heatKernel δ (p.1 - x') * g p.2
        ∂polymerMeasure ϑ N s T ω)| ∂disorderLaw) ≤
      ‖g‖ * ∫ y, |heatKernel δ (y - x) - heatKernel δ (y - x')| := by
  let μ : Disorder → Measure (Plane × Plane) := polymerMeasure ϑ N s T
  let f : Plane → ℝ := fun y => |heatKernel δ (y - x) - heatKernel δ (y - x')|
  let m : Disorder → ℝ := fun ω => ∫ p, f p.1 ∂(μ ω)
  let A : Disorder → ℝ := fun ω => ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(μ ω)
  let B : Disorder → ℝ := fun ω => ∫ p, heatKernel δ (p.1 - x') * g p.2 ∂(μ ω)
  have hf : Integrable f := by
    simpa only [f, Pi.sub_apply] using integrable_abs_heatKernel_sub hδ x x'
  have hfmeas : Measurable f := by
    dsimp [f]
    exact measurable_abs.comp
      (((measurable_heatKernel δ).comp (measurable_id.sub_const x)).sub
        ((measurable_heatKernel δ).comp (measurable_id.sub_const x')))
  have hmass := integral_flat_polymerMeasure_pairing_eq ϑ hN s T f hf
  have hKx : ∀ᵐ ω ∂disorderLaw, Integrable
      (fun p : Plane × Plane => heatKernel δ (p.1 - x)) (μ ω) :=
    ae_integrable_polymer_heat_start ϑ hN s T δ hδ x
  have hKx' : ∀ᵐ ω ∂disorderLaw, Integrable
      (fun p : Plane × Plane => heatKernel δ (p.1 - x')) (μ ω) :=
    ae_integrable_polymer_heat_start ϑ hN s T δ hδ x'
  have hFpair : ∀ᵐ ω ∂disorderLaw, Integrable (fun p : Plane × Plane => f p.1) (μ ω) := by
    filter_upwards [hKx, hKx'] with ω hω hω'
    have hsub := hω.sub hω'
    have habs := hsub.norm
    have heq : (fun p : Plane × Plane => f p.1) =
        fun p => ‖heatKernel δ (p.1 - x) - heatKernel δ (p.1 - x')‖ := by
      funext p
      simp [f, Real.norm_eq_abs]
    rw [heq]
    exact habs
  have hmeq : m =ᵐ[disorderLaw] (fun ω =>
      ∫ y, f y ∂((μ ω).map Prod.fst)) := by
    filter_upwards [hFpair] with ω hω
    have hω' := (integrable_map_measure hfmeas.aestronglyMeasurable
      measurable_fst.aemeasurable).mpr hω
    exact (integral_map measurable_fst.aemeasurable hω'.aestronglyMeasurable).symm
  have hMint : Integrable m disorderLaw := hmass.1.congr hmeq.symm
  have hMmean : (∫ ω, m ω ∂disorderLaw) = ∫ y, f y := by
    rw [integral_congr_ae hmeq]
    exact hmass.2
  have hIntA : ∀ᵐ ω ∂disorderLaw, Integrable
      (fun p : Plane × Plane => heatKernel δ (p.1 - x) * g p.2) (μ ω) := by
    filter_upwards [hKx] with ω hω
    exact integrable_heatKernel_mul_boundedTerminal (μ ω) hδ x g hω
  have hIntB : ∀ᵐ ω ∂disorderLaw, Integrable
      (fun p : Plane × Plane => heatKernel δ (p.1 - x') * g p.2) (μ ω) := by
    filter_upwards [hKx'] with ω hω
    exact integrable_heatKernel_mul_boundedTerminal (μ ω) hδ x' g hω
  have hMeasA : AEMeasurable A disorderLaw := by
    exact aemeasurable_integral_of_measurable_measure disorderLaw μ
      (measurable_polymerMeasure ϑ N s T)
      (fun p => heatKernel δ (p.1 - x) * g p.2)
      ((((measurable_heatKernel δ).comp (measurable_fst.sub_const x)).mul
        (g.continuous.measurable.comp measurable_snd))) hIntA
  have hMeasB : AEMeasurable B disorderLaw := by
    exact aemeasurable_integral_of_measurable_measure disorderLaw μ
      (measurable_polymerMeasure ϑ N s T)
      (fun p => heatKernel δ (p.1 - x') * g p.2)
      ((((measurable_heatKernel δ).comp (measurable_fst.sub_const x')).mul
        (g.continuous.measurable.comp measurable_snd))) hIntB
  have hMassA : Integrable (fun ω => ∫ p, heatKernel δ (p.1 - x) ∂(μ ω)) disorderLaw :=
    (integral_polymer_heat_start_pairing_eq_one ϑ hN s T δ hδ x).1
  have hMassB : Integrable (fun ω => ∫ p, heatKernel δ (p.1 - x') ∂(μ ω)) disorderLaw :=
    (integral_polymer_heat_start_pairing_eq_one ϑ hN s T δ hδ x').1
  have hIntA' : Integrable A disorderLaw := by
    have hmajor : Integrable (fun ω => ‖g‖ *
        ∫ p, heatKernel δ (p.1 - x) ∂(μ ω)) disorderLaw := hMassA.const_mul ‖g‖
    apply hmajor.mono' hMeasA.aestronglyMeasurable
    filter_upwards [hKx] with ω hω
    rw [Real.norm_eq_abs]
    have hPair := integrable_heatKernel_mul_boundedTerminal (μ ω) hδ x g hω
    have hMajor := hω.const_mul ‖g‖
    calc
      |∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(μ ω)| ≤
          ∫ p, ‖heatKernel δ (p.1 - x) * g p.2‖ ∂(μ ω) := by
            rw [← Real.norm_eq_abs]
            exact norm_integral_le_integral_norm _
      _ ≤ ∫ p, ‖g‖ * heatKernel δ (p.1 - x) ∂(μ ω) := by
        apply integral_mono hPair.norm hMajor
        intro p
        change |heatKernel δ (p.1 - x) * g p.2| ≤
          ‖g‖ * heatKernel δ (p.1 - x)
        rw [abs_mul, abs_of_nonneg (heatKernel_nonneg hδ.le (p.1 - x))]
        calc
          heatKernel δ (p.1 - x) * |g p.2| =
              heatKernel δ (p.1 - x) * ‖g p.2‖ := by rw [Real.norm_eq_abs]
          _ ≤ heatKernel δ (p.1 - x) * ‖g‖ :=
            mul_le_mul_of_nonneg_left (g.norm_coe_le_norm p.2)
              (heatKernel_nonneg hδ.le (p.1 - x))
          _ = ‖g‖ * heatKernel δ (p.1 - x) := by ring
      _ = ‖g‖ * ∫ p, heatKernel δ (p.1 - x) ∂(μ ω) := integral_const_mul _ _
  have hIntB' : Integrable B disorderLaw := by
    have hmajor : Integrable (fun ω => ‖g‖ *
        ∫ p, heatKernel δ (p.1 - x') ∂(μ ω)) disorderLaw := hMassB.const_mul ‖g‖
    apply hmajor.mono' hMeasB.aestronglyMeasurable
    filter_upwards [hKx'] with ω hω
    rw [Real.norm_eq_abs]
    have hPair := integrable_heatKernel_mul_boundedTerminal (μ ω) hδ x' g hω
    have hMajor := hω.const_mul ‖g‖
    calc
      |∫ p, heatKernel δ (p.1 - x') * g p.2 ∂(μ ω)| ≤
          ∫ p, ‖heatKernel δ (p.1 - x') * g p.2‖ ∂(μ ω) := by
            rw [← Real.norm_eq_abs]
            exact norm_integral_le_integral_norm _
      _ ≤ ∫ p, ‖g‖ * heatKernel δ (p.1 - x') ∂(μ ω) := by
        apply integral_mono hPair.norm hMajor
        intro p
        change |heatKernel δ (p.1 - x') * g p.2| ≤
          ‖g‖ * heatKernel δ (p.1 - x')
        rw [abs_mul, abs_of_nonneg (heatKernel_nonneg hδ.le (p.1 - x'))]
        calc
          heatKernel δ (p.1 - x') * |g p.2| =
              heatKernel δ (p.1 - x') * ‖g p.2‖ := by rw [Real.norm_eq_abs]
          _ ≤ heatKernel δ (p.1 - x') * ‖g‖ :=
            mul_le_mul_of_nonneg_left (g.norm_coe_le_norm p.2)
              (heatKernel_nonneg hδ.le (p.1 - x'))
          _ = ‖g‖ * heatKernel δ (p.1 - x') := by ring
      _ = ‖g‖ * ∫ p, heatKernel δ (p.1 - x') ∂(μ ω) := integral_const_mul _ _
  have hDint : Integrable (fun ω => |A ω - B ω|) disorderLaw :=
    (hIntA'.sub hIntB').norm
  have hDpoint : ∀ᵐ ω ∂disorderLaw, |A ω - B ω| ≤ ‖g‖ * m ω := by
    filter_upwards [hIntA, hIntB, hFpair] with ω hA hB hF
    have hdiff : A ω - B ω = ∫ p, (heatKernel δ (p.1 - x) -
        heatKernel δ (p.1 - x')) * g p.2 ∂(μ ω) := by
      calc
        A ω - B ω =
            (∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(μ ω)) -
              ∫ p, heatKernel δ (p.1 - x') * g p.2 ∂(μ ω) := rfl
        _ = ∫ p, (heatKernel δ (p.1 - x) * g p.2 -
            heatKernel δ (p.1 - x') * g p.2) ∂(μ ω) := (integral_sub hA hB).symm
        _ = ∫ p, (heatKernel δ (p.1 - x) - heatKernel δ (p.1 - x')) * g p.2
            ∂(μ ω) := by
              congr 1
              funext p
              ring
    have hpairInt : Integrable (fun p : Plane × Plane =>
        (heatKernel δ (p.1 - x) - heatKernel δ (p.1 - x')) * g p.2) (μ ω) := by
      apply (hA.sub hB).congr
      filter_upwards [] with p
      change heatKernel δ (p.1 - x) * g p.2 -
        heatKernel δ (p.1 - x') * g p.2 =
          (heatKernel δ (p.1 - x) - heatKernel δ (p.1 - x')) * g p.2
      ring
    have hmajor : Integrable (fun p : Plane × Plane => ‖g‖ * f p.1) (μ ω) :=
      hF.const_mul ‖g‖
    have hpointbound : |A ω - B ω| ≤ ‖g‖ * m ω := by
      rw [hdiff]
      calc
        |∫ p, (heatKernel δ (p.1 - x) - heatKernel δ (p.1 - x')) * g p.2
            ∂(μ ω)| ≤ ∫ p, ‖(heatKernel δ (p.1 - x) - heatKernel δ (p.1 - x')) * g p.2‖
              ∂(μ ω) := by
                rw [← Real.norm_eq_abs]
                exact norm_integral_le_integral_norm _
        _ ≤ ∫ p, ‖g‖ * f p.1 ∂(μ ω) := by
          apply integral_mono hpairInt.norm hmajor
          intro p
          calc
            ‖(heatKernel δ (p.1 - x) - heatKernel δ (p.1 - x')) * g p.2‖ =
                |heatKernel δ (p.1 - x) - heatKernel δ (p.1 - x')| * |g p.2| := by
                  rw [Real.norm_eq_abs, abs_mul]
            _ ≤ f p.1 * ‖g‖ := by
                dsimp [f]
                exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm p.2)
                  (abs_nonneg _)
            _ = ‖g‖ * f p.1 := by ring
        _ = ‖g‖ * m ω := by
          rw [integral_const_mul]
    exact hpointbound
  refine ⟨hDint, ?_⟩
  have hmajor : Integrable (fun ω => ‖g‖ * m ω) disorderLaw := hMint.const_mul ‖g‖
  calc
    (∫ ω, |A ω - B ω| ∂disorderLaw) ≤ ∫ ω, ‖g‖ * m ω ∂disorderLaw :=
      integral_mono_ae hDint hmajor hDpoint
    _ = ‖g‖ * ∫ ω, m ω ∂disorderLaw := integral_const_mul _ _
    _ = ‖g‖ * ∫ y, f y := by rw [hMmean]
    _ = ‖g‖ * ∫ y, |heatKernel δ (y - x) - heatKernel δ (y - x')| := rfl

/-- The continuous logarithm clamp is bounded by its truncation radius. -/
theorem abs_heatStartLogClamp_le (R x : ℝ) (hR : 0 ≤ R) :
    |heatStartLogClamp R x| ≤ R := by
  have hlow : -R ≤ heatStartLogClamp R x := by
    dsimp [heatStartLogClamp]
    have hmax : Real.exp (-R) ≤ max (Real.exp (-R)) (min x (Real.exp R)) := le_max_left _ _
    have hlog := Real.log_le_log (Real.exp_pos _) hmax
    simpa only [Real.log_exp] using hlog
  have hupp : heatStartLogClamp R x ≤ R := by
    dsimp [heatStartLogClamp]
    have hmax : max (Real.exp (-R)) (min x (Real.exp R)) ≤ Real.exp R :=
      max_le (Real.exp_le_exp.mpr (by linarith)) (min_le_right _ _)
    calc
      Real.log (max (Real.exp (-R)) (min x (Real.exp R))) ≤ Real.log (Real.exp R) :=
        Real.log_le_log ((Real.exp_pos _).trans_le (le_max_left _ _)) hmax
      _ = R := Real.log_exp _
  exact abs_le.mpr ⟨hlow, hupp⟩

/-- Clamping a polymer heat pairing preserves a spatial translation estimate in mean. -/
theorem polymer_heatPairing_clamp_translation_l1_le (ϑ : ℝ) {N : ℕ}
    (hN : 1 ≤ N) (s T δ : ℝ) (hδ : 0 < δ) (R : ℝ) (hR : 0 ≤ R)
    (C : ℝ) (hKernel : ∀ u : ℝ, 0 < u → ∀ a b : Plane,
      ∫ y, |heatKernel u (y - a) - heatKernel u (y - b)| ≤
        C * ‖a - b‖ / Real.sqrt u)
    (x x' : Plane) (g : Plane →ᵇ ℝ) :
    Integrable (fun ω => |heatStartLogClamp R
          (∫ p, heatKernel δ (p.1 - x) * g p.2 ∂polymerMeasure ϑ N s T ω) -
        heatStartLogClamp R
          (∫ p, heatKernel δ (p.1 - x') * g p.2 ∂polymerMeasure ϑ N s T ω)|) disorderLaw ∧
      (∫ ω, |heatStartLogClamp R
        (∫ p, heatKernel δ (p.1 - x) * g p.2 ∂polymerMeasure ϑ N s T ω) -
      heatStartLogClamp R
        (∫ p, heatKernel δ (p.1 - x') * g p.2 ∂polymerMeasure ϑ N s T ω)| ∂disorderLaw) ≤
        Real.exp R * (‖g‖ * (C * ‖x - x'‖ / Real.sqrt δ)) := by
  let μ : Disorder → Measure (Plane × Plane) := polymerMeasure ϑ N s T
  let A : Disorder → ℝ := fun ω =>
    ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂μ ω
  let B : Disorder → ℝ := fun ω =>
    ∫ p, heatKernel δ (p.1 - x') * g p.2 ∂μ ω
  have hKx : ∀ᵐ ω ∂disorderLaw, Integrable
      (fun p : Plane × Plane => heatKernel δ (p.1 - x)) (μ ω) :=
    ae_integrable_polymer_heat_start ϑ hN s T δ hδ x
  have hKx' : ∀ᵐ ω ∂disorderLaw, Integrable
      (fun p : Plane × Plane => heatKernel δ (p.1 - x')) (μ ω) :=
    ae_integrable_polymer_heat_start ϑ hN s T δ hδ x'
  have hIntA : ∀ᵐ ω ∂disorderLaw, Integrable
      (fun p : Plane × Plane => heatKernel δ (p.1 - x) * g p.2) (μ ω) := by
    filter_upwards [hKx] with ω hω
    exact integrable_heatKernel_mul_boundedTerminal (μ ω) hδ x g hω
  have hIntB : ∀ᵐ ω ∂disorderLaw, Integrable
      (fun p : Plane × Plane => heatKernel δ (p.1 - x') * g p.2) (μ ω) := by
    filter_upwards [hKx'] with ω hω
    exact integrable_heatKernel_mul_boundedTerminal (μ ω) hδ x' g hω
  have hMeasA : AEMeasurable A disorderLaw := by
    exact aemeasurable_integral_of_measurable_measure disorderLaw μ
      (measurable_polymerMeasure ϑ N s T)
      (fun p => heatKernel δ (p.1 - x) * g p.2)
      ((((measurable_heatKernel δ).comp (measurable_fst.sub_const x)).mul
        (g.continuous.measurable.comp measurable_snd))) hIntA
  have hMeasB : AEMeasurable B disorderLaw := by
    exact aemeasurable_integral_of_measurable_measure disorderLaw μ
      (measurable_polymerMeasure ϑ N s T)
      (fun p => heatKernel δ (p.1 - x') * g p.2)
      ((((measurable_heatKernel δ).comp (measurable_fst.sub_const x')).mul
        (g.continuous.measurable.comp measurable_snd))) hIntB
  have hClampA : AEMeasurable (fun ω => heatStartLogClamp R (A ω)) disorderLaw :=
    (heatStartLogClamp_continuous R).measurable.comp_aemeasurable hMeasA
  have hClampB : AEMeasurable (fun ω => heatStartLogClamp R (B ω)) disorderLaw :=
    (heatStartLogClamp_continuous R).measurable.comp_aemeasurable hMeasB
  have hClampDiff : Integrable
      (fun ω => heatStartLogClamp R (A ω) - heatStartLogClamp R (B ω)) disorderLaw := by
    apply Integrable.of_bound (hClampA.sub hClampB).aestronglyMeasurable (2 * R)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs]
    calc
      |heatStartLogClamp R (A ω) - heatStartLogClamp R (B ω)| ≤
          |heatStartLogClamp R (A ω)| + |heatStartLogClamp R (B ω)| := abs_sub _ _
      _ ≤ R + R := add_le_add (abs_heatStartLogClamp_le R _ hR)
        (abs_heatStartLogClamp_le R _ hR)
      _ = 2 * R := by ring
  have hpair := polymer_heatPairing_translation_l1_le ϑ hN s T δ hδ x x' g
  have hmajor : Integrable (fun ω => Real.exp R * |A ω - B ω|) disorderLaw :=
    hpair.1.const_mul (Real.exp R)
  have hpoint : ∀ᵐ ω ∂disorderLaw,
      |heatStartLogClamp R (A ω) - heatStartLogClamp R (B ω)| ≤
        Real.exp R * |A ω - B ω| := by
    filter_upwards [] with ω
    have hL := heatStartLogClamp_lipschitz R hR
    have h := hL.norm_sub_le (A ω) (B ω)
    rw [Real.norm_eq_abs] at h
    exact h
  have hmean := integral_mono_ae hClampDiff.norm hmajor hpoint
  refine ⟨hClampDiff.norm, ?_⟩
  calc
    (∫ ω, |heatStartLogClamp R (A ω) - heatStartLogClamp R (B ω)| ∂disorderLaw) ≤
        ∫ ω, Real.exp R * |A ω - B ω| ∂disorderLaw := by
      simpa only [Real.norm_eq_abs] using hmean
    _ = Real.exp R * (∫ ω, |A ω - B ω| ∂disorderLaw) := integral_const_mul _ _
    _ ≤ Real.exp R * (‖g‖ * ∫ y,
          |heatKernel δ (y - x) - heatKernel δ (y - x')|) :=
      mul_le_mul_of_nonneg_left hpair.2 (Real.exp_nonneg _)
    _ ≤ Real.exp R * (‖g‖ * (C * ‖x - x'‖ / Real.sqrt δ)) := by
      gcongr
      exact hKernel δ hδ x x'

/-- Joint convergence transfers the polymer translation bound to the clamped SHF heat field. -/
theorem shf_heatPairing_clamp_translation_l1_le (ϑ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hjoint : ∀ (k : ℕ) (s t δ : Fin k → ℝ) (x : Fin k → Plane)
      (g : Fin k → (Plane →ᵇ ℝ)),
      (∀ i, 0 ≤ s i ∧ s i < t i ∧ 0 < δ i) →
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
          ∫ p, heatKernel (δ i) (p.1 - x i) * g i p.2
            ∂(polymerMeasure ϑ N (s i) (t i) ω))
        atTop
        (fun ω i => shfPairing Z (s i) (t i)
          (fun y => heatKernel (δ i) (y - x i)) (g i) ω)
        (fun _ => disorderLaw) P)
    {s T δ : ℝ} (hs : 0 ≤ s) (hsT : s < T) (hδ : 0 < δ)
    (R : ℝ) (hR : 0 ≤ R) (C : ℝ)
    (hKernel : ∀ u : ℝ, 0 < u → ∀ a b : Plane,
      ∫ y, |heatKernel u (y - a) - heatKernel u (y - b)| ≤
        C * ‖a - b‖ / Real.sqrt u)
    (x x' : Plane) (g : Plane →ᵇ ℝ) :
    Integrable (fun ω => |heatStartLogClamp R
        (shfPairing Z s T (fun y => heatKernel δ (y - x)) g ω) -
      heatStartLogClamp R
        (shfPairing Z s T (fun y => heatKernel δ (y - x')) g ω)|) P ∧
    (∫ ω, |heatStartLogClamp R
        (shfPairing Z s T (fun y => heatKernel δ (y - x)) g ω) -
      heatStartLogClamp R
        (shfPairing Z s T (fun y => heatKernel δ (y - x')) g ω)| ∂P) ≤
      Real.exp R * (‖g‖ * (C * ‖x - x'‖ / Real.sqrt δ)) := by
  classical
  let xp : Fin 2 → Plane := fun i => if i = 0 then x else x'
  let U : ℕ → Disorder → Fin 2 → ℝ := fun N ω i =>
    ∫ p, heatKernel δ (p.1 - xp i) * g p.2 ∂polymerMeasure ϑ N s T ω
  let V : Ω → Fin 2 → ℝ := fun ω i =>
    shfPairing Z s T (fun y => heatKernel δ (y - xp i)) g ω
  have hparams : ∀ i : Fin 2, 0 ≤ s ∧ s < T ∧ 0 < δ :=
    fun _ => ⟨hs, hsT, hδ⟩
  have hraw : TendstoInDistribution U atTop V (fun _ => disorderLaw) P := by
    simpa only [U, V, xp] using hjoint 2 (fun _ => s) (fun _ => T) (fun _ => δ)
      xp (fun _ => g) hparams
  let F : (Fin 2 → ℝ) → ℝ := fun v =>
    |heatStartLogClamp R (v 0) - heatStartLogClamp R (v 1)|
  have hFbound (v : Fin 2 → ℝ) : |F v| ≤ 2 * R := by
    have hFeq : F v = |heatStartLogClamp R (v 0) - heatStartLogClamp R (v 1)| := rfl
    rw [hFeq, abs_abs]
    calc
      |heatStartLogClamp R (v 0) - heatStartLogClamp R (v 1)| ≤
          |heatStartLogClamp R (v 0)| + |heatStartLogClamp R (v 1)| := abs_sub _ _
      _ ≤ R + R := add_le_add (abs_heatStartLogClamp_le R _ hR)
        (abs_heatStartLogClamp_le R _ hR)
      _ = 2 * R := by ring
  have hcoord (v w : Fin 2 → ℝ) (i : Fin 2) :
      |heatStartLogClamp R (v i) - heatStartLogClamp R (w i)| ≤
        Real.exp R * ‖v - w‖ := by
    have hL := heatStartLogClamp_lipschitz R hR
    have h := hL.norm_sub_le (v i) (w i)
    rw [Real.norm_eq_abs] at h
    have hi : |v i - w i| ≤ ‖v - w‖ := by
      rw [Pi.norm_def]
      have hreal : (↑(‖(v - w) i‖₊) : ℝ) ≤
          ↑(Finset.univ.sup (fun j : Fin 2 => ‖(v - w) j‖₊)) :=
        NNReal.coe_le_coe.mpr
          (Finset.le_sup (s := Finset.univ)
            (f := fun j : Fin 2 => ‖(v - w) j‖₊) (Finset.mem_univ i))
      simpa only [Pi.sub_apply, Real.norm_eq_abs, coe_nnnorm] using hreal
    calc
      |heatStartLogClamp R (v i) - heatStartLogClamp R (w i)| ≤
          Real.exp R * ‖v i - w i‖ := h
      _ ≤ Real.exp R * ‖v - w‖ := by
        exact mul_le_mul_of_nonneg_left hi (Real.exp_nonneg _)
  have hFLipschitz : LipschitzWith ⟨2 * Real.exp R, by positivity⟩ F := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    change |F v - F w| ≤ (2 * Real.exp R) * ‖v - w‖
    dsimp [F]
    calc
      _ ≤ |(heatStartLogClamp R (v 0) - heatStartLogClamp R (v 1)) -
          (heatStartLogClamp R (w 0) - heatStartLogClamp R (w 1))| :=
            abs_abs_sub_abs_le_abs_sub _ _
      _ ≤ |heatStartLogClamp R (v 0) - heatStartLogClamp R (w 0)| +
          |heatStartLogClamp R (v 1) - heatStartLogClamp R (w 1)| := by
        calc
          _ = |(heatStartLogClamp R (v 0) - heatStartLogClamp R (w 0)) -
              (heatStartLogClamp R (v 1) - heatStartLogClamp R (w 1))| := by
            congr 1
            ring
          _ ≤ _ := abs_sub _ _
      _ ≤ Real.exp R * ‖v - w‖ + Real.exp R * ‖v - w‖ :=
        add_le_add (hcoord v w 0) (hcoord v w 1)
      _ = (2 * Real.exp R) * ‖v - w‖ := by ring
  have htest :=
    (tendsto_iff_forall_lipschitz_integral_tendsto (Ω := Fin 2 → ℝ)).mp hraw.tendsto
      F ⟨4 * R, fun v w => by
        rw [Real.dist_eq]
        calc
          |F v - F w| ≤ |F v| + |F w| := abs_sub _ _
          _ ≤ 2 * R + 2 * R := add_le_add (hFbound v) (hFbound w)
          _ = 4 * R := by ring⟩
      ⟨⟨2 * Real.exp R, by positivity⟩, hFLipschitz⟩
  have hmapN (N : ℕ) :
      (∫ z, F z ∂(disorderLaw).map (U N)) = ∫ ω, F (U N ω) ∂disorderLaw :=
    integral_map (hraw.forall_aemeasurable N)
      (hFLipschitz.continuous.measurable.aestronglyMeasurable)
  have hmapLim :
      (∫ z, F z ∂P.map V) = ∫ ω, F (V ω) ∂P :=
    integral_map hraw.aemeasurable_limit
      (hFLipschitz.continuous.measurable.aestronglyMeasurable)
  have htest' : Tendsto (fun N => ∫ ω, F (U N ω) ∂disorderLaw) atTop
      (𝓝 (∫ ω, F (V ω) ∂P)) := by
    simpa only [ProbabilityMeasure.coe_mk, hmapN, hmapLim] using htest
  have hboundN : ∀ᶠ N : ℕ in atTop,
      ∫ ω, F (U N ω) ∂disorderLaw ≤
        Real.exp R * (‖g‖ * (C * ‖x - x'‖ / Real.sqrt δ)) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hclamp := polymer_heatPairing_clamp_translation_l1_le ϑ hN s T δ hδ R hR
      C hKernel x x' g
    simpa [F, U, xp, Fin.isValue] using hclamp.2
  have hlimitBound : ∫ ω, F (V ω) ∂P ≤
      Real.exp R * (‖g‖ * (C * ‖x - x'‖ / Real.sqrt δ)) :=
    le_of_tendsto_of_tendsto htest' tendsto_const_nhds hboundN
  have hFmeas : AEMeasurable (fun ω => F (V ω)) P :=
    hFLipschitz.continuous.measurable.comp_aemeasurable hraw.aemeasurable_limit
  have hFint : Integrable (fun ω => F (V ω)) P := by
    apply Integrable.of_bound hFmeas.aestronglyMeasurable (2 * R)
    filter_upwards [] with ω
    exact hFbound (V ω)
  refine ⟨?_, hlimitBound⟩
  simpa [F, V, xp, Fin.isValue] using hFint.norm

/-- A compactly tested lattice log field is measurable as a function of the disorder. -/
theorem aemeasurable_integral_heatStartLogProfile (ϑ : ℝ) (N : ℕ)
    (s T δ : ℝ) (h₀ : Plane →ᵇ ℝ) (φ : TestFn) :
    AEMeasurable (fun ω : Disorder => ∫ x : Plane,
      φ x * heatStartLogProfile ϑ N s T δ x h₀ ω) disorderLaw := by
  let ν : Plane × Disorder → Site → ℝ := fun q z =>
    srwKernel (evenCeil (N * δ)) (z - latticePoint N q.1)
  have hν (z : Site) : Measurable (fun q : Plane × Disorder => ν q z) := by
    exact (measurable_of_countable fun w : Site => srwKernel (evenCeil (N * δ)) (z - w))
      |>.comp ((measurable_latticePoint N).comp measurable_fst)
  have hprofile : Measurable (fun q : Plane × Disorder =>
      profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * T))
        (ν q) (cellAverage N fun y => Real.exp (h₀ y)) q.2) :=
    Smoothing.measurable_profileP2Fun_param (criticalBeta ϑ N)
      (evenCeil (N * s)) (evenCeil (N * T))
      (cellAverage N fun y => Real.exp (h₀ y)) hν measurable_snd
  have hfield : Measurable (fun q : Plane × Disorder =>
      φ q.1 * Real.log (profileP2Fun (criticalBeta ϑ N)
        (evenCeil (N * s)) (evenCeil (N * T))
        (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N q.1))
        (cellAverage N fun y => Real.exp (h₀ y)) q.2)) := by
    exact (φ.continuous.measurable.comp measurable_fst).mul (by
      simpa only [ν] using hprofile.log)
  have hprod : AEStronglyMeasurable (fun q : Plane × Disorder =>
      φ q.1 * heatStartLogProfile ϑ N s T δ q.1 h₀ q.2)
      (volume.prod disorderLaw) := by
    exact hfield.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun q => by
      simp only [heatStartLogProfile])
  exact hprod.prod_swap.integral_prod_right'.aemeasurable

/-- Joint measurability of the lattice heat-start log field in space and disorder. -/
theorem aemeasurable_heatStartLogProfile_joint (ϑ : ℝ) (N : ℕ)
    (s T δ : ℝ) (h₀ : Plane →ᵇ ℝ) :
    AEMeasurable (fun q : Plane × Disorder =>
      heatStartLogProfile ϑ N s T δ q.1 h₀ q.2) (volume.prod disorderLaw) := by
  let ν : Plane × Disorder → Site → ℝ := fun q z =>
    srwKernel (evenCeil (N * δ)) (z - latticePoint N q.1)
  have hν (z : Site) : Measurable (fun q : Plane × Disorder => ν q z) := by
    exact (measurable_of_countable fun w : Site => srwKernel (evenCeil (N * δ)) (z - w))
      |>.comp ((measurable_latticePoint N).comp measurable_fst)
  have hprofile : Measurable (fun q : Plane × Disorder =>
      profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * T))
        (ν q) (cellAverage N fun y => Real.exp (h₀ y)) q.2) :=
    Smoothing.measurable_profileP2Fun_param (criticalBeta ϑ N)
      (evenCeil (N * s)) (evenCeil (N * T))
      (cellAverage N fun y => Real.exp (h₀ y)) hν measurable_snd
  have hlog : Measurable (fun q : Plane × Disorder => Real.log
      (profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * T))
        (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N q.1))
        (cellAverage N fun y => Real.exp (h₀ y)) q.2)) := by
    exact Real.measurable_log.comp (by simpa only [ν] using hprofile)
  exact (hlog.aemeasurable.congr (Filter.Eventually.of_forall fun q => by
    simp only [heatStartLogProfile]))

/-- Joint measurability of the limiting SHF heat-start log field in the spatial variable and random outcome. -/
theorem aemeasurable_shfLogField_joint (ϑ : ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (s T δ : ℝ) (hs : 0 ≤ s) (hsT : s < T) (hδ : 0 < δ)
    (h₀ : Plane →ᵇ ℝ) :
    AEMeasurable (fun q : Plane × Ω => Real.log
      (shfPairing Z s T (fun y => heatKernel δ (y - q.1))
        (fun y => Real.exp (h₀ y)) q.2)) (volume.prod P) := by
  let μ : Ω → Measure (Plane × Plane) := Z s T
  have hlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
    filter_upwards [hZ.2.1 s T hs hsT] with ω hω
    exact hω.1
  have hg : Measurable (fun y : Plane => Real.exp (h₀ y)) :=
    Real.continuous_exp.measurable.comp h₀.continuous.measurable
  have hgn : ∀ y : Plane, 0 ≤ Real.exp (h₀ y) := fun y => (Real.exp_pos _).le
  have h := aemeasurable_log_heatPairing_joint P μ (hZ.1 s T hs hsT) hlocal
    δ hδ (fun y => Real.exp (h₀ y)) hg hgn
  simpa only [μ, shfPairing, sub_zero] using h


/-- A spatially integrated SHF log field is measurable, using local finiteness to obtain joint
measurability of its heat pairing. -/
theorem aemeasurable_integral_shfLogField (ϑ : ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (s T δ : ℝ) (hs : 0 ≤ s) (hsT : s < T) (hδ : 0 < δ)
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn) :
    AEMeasurable (fun ω : Ω => ∫ x : Plane, φ x *
      Real.log (shfPairing Z s T (fun y => heatKernel δ (y - x))
        (fun y => Real.exp (h₀ y)) ω)) P := by
  let μ : Ω → Measure (Plane × Plane) := Z s T
  have hlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
    filter_upwards [hZ.2.1 s T hs hsT] with ω hω
    exact hω.1
  have hg : Measurable (fun y : Plane => Real.exp (h₀ y)) :=
    Real.continuous_exp.measurable.comp h₀.continuous.measurable
  have hgn : ∀ y : Plane, 0 ≤ Real.exp (h₀ y) := fun y => (Real.exp_pos _).le
  have h := aemeasurable_integral_log_heatPairing P μ
    (hZ.1 s T hs hsT) hlocal δ 0 hδ (fun y => Real.exp (h₀ y)) φ hg hgn
    φ.continuous.measurable
  simpa only [μ, shfPairing, sub_zero] using h

/-- Integrating a lattice-cell constant against a compactly supported continuous test function
reduces to the finite set of cells that meet the test support. -/
theorem integral_mul_latticePoint_piecewise {φ : Plane → ℝ}
    (hφ : Continuous φ) (hφs : HasCompactSupport φ) (m : ℕ) (G : Site → ℝ)
    (S : Finset Site) (hS : ∀ x, φ x ≠ 0 → latticePoint m x ∈ S) :
    ∫ x, φ x * G (latticePoint m x) =
      ∑ z ∈ S, (∫ x in cell m z, φ x) * G z := by
  classical
  let f : Plane → ℝ := fun x => φ x * G (latticePoint m x)
  let C : ℝ := ∑ z ∈ S, |G z|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hfmeas : Measurable f := by
    dsimp [f]
    exact hφ.measurable.mul ((measurable_of_countable G).comp (measurable_latticePoint m))
  have hfbound (x : Plane) : ‖f x‖ ≤ C * ‖φ x‖ := by
    by_cases hx : φ x = 0
    · simp [f, C, hx]
    · have hz : latticePoint m x ∈ S := hS x hx
      have hG : |G (latticePoint m x)| ≤ C := by
        dsimp [C]
        exact Finset.single_le_sum (fun z _ => abs_nonneg (G z)) hz
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      calc
        |φ x| * |G (latticePoint m x)| ≤ |φ x| * C :=
          mul_le_mul_of_nonneg_left hG (abs_nonneg _)
        _ = C * |φ x| := by ring
  have hf : Integrable f := by
    apply ((hφ.integrable_of_hasCompactSupport hφs).norm.const_mul C).mono'
      hfmeas.aestronglyMeasurable
    filter_upwards [] with x
    simpa only [f, Real.norm_eq_abs] using hfbound x
  have hcover : (⋃ z : Site, cell m z) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨latticePoint m x, mem_cell_latticePoint m x⟩
  have hi := integral_iUnion (measurableSet_cell m) (pairwise_disjoint_cell m)
    hf.integrableOn
  rw [hcover, setIntegral_univ] at hi
  rw [hi]
  have hcell (z : Site) : (∫ x in cell m z, f x) =
      (∫ x in cell m z, φ x) * G z := by
    have heq : (fun x : Plane => f x) =ᵐ[volume.restrict (cell m z)]
        fun x => φ x * G z := by
      filter_upwards [ae_restrict_mem (measurableSet_cell m z)] with x hx
      simp only [f, mem_cell_iff] at hx ⊢
      rw [hx]
    rw [integral_congr_ae heq, integral_mul_const]
  simp_rw [hcell]
  apply tsum_eq_sum
  intro z hz
  have hφzero : ∀ x ∈ cell m z, φ x = 0 := by
    intro x hx
    by_contra hne
    have hxS := hS x hne
    have hzEq : latticePoint m x = z := (mem_cell_iff m z x).mp hx
    exact hz (hzEq ▸ hxS)
  have hzero : (∫ x in cell m z, φ x) = 0 := by
    exact setIntegral_eq_zero_of_forall_eq_zero hφzero
  simp [hzero]

/-- The exponential of a bounded continuous terminal profile is a bounded continuous function. -/
def heatStartExpTerminal (h₀ : Plane →ᵇ ℝ) : Plane →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun y => Real.exp (h₀ y), by fun_prop⟩ (2 * Real.exp ‖h₀‖) (by
      intro y z
      change |Real.exp (h₀ y) - Real.exp (h₀ z)| ≤ 2 * Real.exp ‖h₀‖
      have hy : Real.exp (h₀ y) ≤ Real.exp ‖h₀‖ :=
        Real.exp_le_exp.mpr (abs_le.mp (h₀.norm_coe_le_norm y)).2
      have hz : Real.exp (h₀ z) ≤ Real.exp ‖h₀‖ :=
        Real.exp_le_exp.mpr (abs_le.mp (h₀.norm_coe_le_norm z)).2
      have hye : 0 ≤ Real.exp (h₀ y) := Real.exp_nonneg _
      have hze : 0 ≤ Real.exp (h₀ z) := Real.exp_nonneg _
      have h := abs_sub (Real.exp (h₀ y)) (Real.exp (h₀ z))
      rw [abs_of_nonneg hye, abs_of_nonneg hze] at h
      nlinarith)

/-- The exponential terminal profile evaluates to the exponential of the initial height. -/
@[simp] theorem heatStartExpTerminal_apply (h₀ : Plane →ᵇ ℝ) (y : Plane) :
    heatStartExpTerminal h₀ y = Real.exp (h₀ y) := rfl

/-- A common finite set contains every lattice cell that meets one of finitely many test supports. -/
theorem exists_finite_heatStartCells {k : ℕ} (φ : Fin k → TestFn) (m : ℕ) :
    ∃ S : Finset Site, ∀ i x, φ i x ≠ 0 → latticePoint m x ∈ S := by
  classical
  let K : Set Plane := ⋃ i : Fin k, tsupport (φ i)
  have hK : IsCompact K := by
    apply isCompact_iUnion
    intro i
    exact (φ i).hasCompactSupport.isCompact
  have hS := SHF.Limit.finite_latticePoint_image_of_bounded
    (N := m) (s := K) hK.isBounded
  refine ⟨hS.toFinset, ?_⟩
  intro i x hx
  apply hS.mem_toFinset.mpr
  refine ⟨x, ?_, rfl⟩
  exact Set.mem_iUnion.mpr ⟨i, subset_tsupport (φ i) hx⟩

/-- For a fixed mesh, a finite weighted sum of clamped heat pairings converges in law by the
joint heat-pairing hypothesis and the continuous mapping theorem. -/
theorem finiteMesh_clamped_pairing_tendsto (ϑ : ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (k : ℕ)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hjoint : ∀ (k : ℕ) (s t δ : Fin k → ℝ) (x : Fin k → Plane)
      (g : Fin k → (Plane →ᵇ ℝ)),
      (∀ i, 0 ≤ s i ∧ s i < t i ∧ 0 < δ i) →
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
          ∫ p, heatKernel (δ i) (p.1 - x i) * g i p.2
            ∂(polymerMeasure ϑ N (s i) (t i) ω))
        atTop
        (fun ω i => shfPairing Z (s i) (t i)
          (fun y => heatKernel (δ i) (y - x i)) (g i) ω)
        (fun _ => disorderLaw) P)
    (T : ℝ) (h₀ : Fin k → (Plane →ᵇ ℝ)) (s δ : Fin k → ℝ)
    (φ : Fin k → TestFn) (hs : ∀ i, 0 ≤ s i ∧ s i < T ∧ 0 < δ i)
    (m : ℕ) (R : ℝ) (S : Finset Site) :
    TendstoInDistribution
      (fun N ω i => ∑ z : S.attach,
        (∫ x in cell m z.1, φ i x) * heatStartLogClamp R
          (∫ p, heatKernel (δ i) (p.1 - latticeRepresentative m z.1) *
            Real.exp (h₀ i p.2) ∂(polymerMeasure ϑ N (s i) T ω)))
      atTop
      (fun ω i => ∑ z : S.attach,
        (∫ x in cell m z.1, φ i x) * heatStartLogClamp R
          (shfPairing Z (s i) T
            (fun y => heatKernel (δ i) (y - latticeRepresentative m z.1))
            (fun y => Real.exp (h₀ i y)) ω))
      (fun _ => disorderLaw) P := by
  classical
  let I := Fin k × S.attach
  let n : ℕ := Fintype.card I
  let e : I ≃ Fin n := Fintype.equivFin I
  let ix : Fin n → Fin k := fun a => (e.symm a).1
  let iz : Fin n → S.attach := fun a => (e.symm a).2
  let st : Fin n → ℝ := fun a => s (ix a)
  let tt : Fin n → ℝ := fun _ => T
  let dt : Fin n → ℝ := fun a => δ (ix a)
  let xt : Fin n → Plane := fun a => latticeRepresentative m (iz a).1
  let gt : Fin n → (Plane →ᵇ ℝ) := fun a => heatStartExpTerminal (h₀ (ix a))
  let U : ℕ → Disorder → Fin n → ℝ := fun N ω a =>
    ∫ p, heatKernel (dt a) (p.1 - xt a) * gt a p.2
      ∂(polymerMeasure ϑ N (st a) (tt a) ω)
  let V : Ω → Fin n → ℝ := fun ω a =>
    shfPairing Z (st a) (tt a) (fun y => heatKernel (dt a) (y - xt a)) (gt a) ω
  have hparams : ∀ a, 0 ≤ st a ∧ st a < tt a ∧ 0 < dt a := by
    intro a
    exact ⟨(hs (ix a)).1, (hs (ix a)).2.1, (hs (ix a)).2.2⟩
  have hraw : TendstoInDistribution U atTop V (fun _ => disorderLaw) P := by
    exact hjoint n st tt dt xt gt hparams
  let F : (Fin n → ℝ) → Fin k → ℝ := fun v i =>
    ∑ z : S.attach, (∫ x in cell m z.1, φ i x) *
      heatStartLogClamp R (v (e (i, z)))
  have hclamp : Continuous (heatStartLogClamp R) := heatStartLogClamp_continuous R
  have hFcont : Continuous F := by
    apply continuous_pi
    intro i
    dsimp [F]
    exact continuous_finsetSum Finset.univ fun z hz =>
      continuous_const.mul (hclamp.comp (continuous_apply (e (i, z))))
  have hcomp := hraw.continuous_comp (g := F) hFcont
  have hrewriteN (N : ℕ) (ω : Disorder) (i : Fin k) :
      F (U N ω) i = ∑ z : S.attach,
        (∫ x in cell m z.1, φ i x) * heatStartLogClamp R
          (∫ p, heatKernel (δ i) (p.1 - latticeRepresentative m z.1) *
            Real.exp (h₀ i p.2) ∂(polymerMeasure ϑ N (s i) T ω)) := by
    simp [F, U, st, tt, dt, xt, gt, ix, iz]
  have hterminal (i : Fin k) :
      (heatStartExpTerminal (h₀ i) : Plane → ℝ) = fun y => Real.exp (h₀ i y) := by
    funext y
    simp
  have hrewriteL (ω : Ω) (i : Fin k) :
      F (V ω) i = ∑ z : S.attach,
        (∫ x in cell m z.1, φ i x) * heatStartLogClamp R
          (shfPairing Z (s i) T
            (fun y => heatKernel (δ i) (y - latticeRepresentative m z.1))
            (fun y => Real.exp (h₀ i y)) ω) := by
    simp [F, V, st, tt, dt, xt, gt, ix, iz, hterminal]
  have hinput :
      (fun N ω i => ∑ z : S.attach,
        (∫ x in cell m z.1, φ i x) * heatStartLogClamp R
          (∫ p, heatKernel (δ i) (p.1 - latticeRepresentative m z.1) *
            Real.exp (h₀ i p.2) ∂(polymerMeasure ϑ N (s i) T ω))) =
        fun N ω => F (U N ω) := by
    funext N ω
    ext i
    exact (hrewriteN N ω i).symm
  have hlimit :
      (fun ω i => ∑ z : S.attach,
        (∫ x in cell m z.1, φ i x) * heatStartLogClamp R
          (shfPairing Z (s i) T
            (fun y => heatKernel (δ i) (y - latticeRepresentative m z.1))
            (fun y => Real.exp (h₀ i y)) ω)) =
        fun ω => F (V ω) := by
    funext ω
    ext i
    exact (hrewriteL ω i).symm
  rw [hinput, hlimit]
  exact hcomp

/-- A spatially weighted random field with a uniform square-moment bound is integrable on the
space-probability product. -/
theorem integrable_test_mul_joint {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {F : Plane × Ω → ℝ}
    (hF : AEMeasurable F (volume.prod P))
    (hFsec : ∀ x, AEStronglyMeasurable (fun ω => F (x, ω)) P)
    {M : ℝ} (hM : 0 ≤ M)
    (hSq : ∀ x, Integrable (fun ω => |F (x, ω)| ^ 2) P ∧
      ∫ ω, |F (x, ω)| ^ 2 ∂P ≤ M)
    (φ : TestFn) : Integrable (fun q : Plane × Ω => φ q.1 * F q) (volume.prod P) := by
  have hφ : Integrable (fun x : Plane => |φ x|) :=
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).norm
  have hW : AEStronglyMeasurable (fun q : Plane × Ω => φ q.1 * F q)
      (volume.prod P) := by
    exact (φ.continuous.measurable.comp measurable_fst).aestronglyMeasurable.mul
      hF.aestronglyMeasurable
  have hsection (x : Plane) : Integrable (fun ω => φ x * F (x, ω)) P := by
    have hplus : Integrable (fun ω => (1 : ℝ) + |F (x, ω)| ^ 2) P :=
      (integrable_const (1 : ℝ)).add (hSq x).1
    have hfirst : Integrable (fun ω => |F (x, ω)|) P := by
      apply hplus.mono' (hFsec x).norm
      filter_upwards [] with ω
      simp only [Real.norm_eq_abs, abs_abs]
      nlinarith [sq_nonneg (|F (x, ω)| - 1)]
    have hFint : Integrable (fun ω => F (x, ω)) P :=
      (integrable_norm_iff (hFsec x)).mp (by simpa [Real.norm_eq_abs] using hfirst)
    exact hFint.const_mul (φ x)
  let H : Plane → ℝ := fun x => ∫ ω, ‖φ x * F (x, ω)‖ ∂P
  have hHmeas : AEMeasurable H volume := by
    exact hW.norm.integral_prod_right'.aemeasurable
  have hHbound (x : Plane) : H x ≤ (1 + M) * |φ x| := by
    have hplus : Integrable (fun ω => (1 : ℝ) + |F (x, ω)| ^ 2) P :=
      (integrable_const (1 : ℝ)).add (hSq x).1
    have hfirst : Integrable (fun ω => |F (x, ω)|) P := by
      apply hplus.mono' (hFsec x).norm
      filter_upwards [] with ω
      simp only [Real.norm_eq_abs, abs_abs]
      nlinarith [sq_nonneg (|F (x, ω)| - 1)]
    have hpoint (ω : Ω) : |F (x, ω)| ≤ 1 + |F (x, ω)| ^ 2 := by
      nlinarith [sq_nonneg (|F (x, ω)| - 1)]
    have hmean : ∫ ω, |F (x, ω)| ∂P ≤ 1 + M := by
      calc
        ∫ ω, |F (x, ω)| ∂P ≤ ∫ ω, (1 + |F (x, ω)| ^ 2) ∂P :=
          integral_mono hfirst hplus hpoint
        _ = 1 + ∫ ω, |F (x, ω)| ^ 2 ∂P := by
          rw [integral_add (integrable_const (1 : ℝ)) (hSq x).1]
          simp [sq_abs]
        _ ≤ 1 + M := add_le_add le_rfl (hSq x).2
    dsimp [H]
    calc
      (∫ ω, ‖φ x * F (x, ω)‖ ∂P) = |φ x| * ∫ ω, |F (x, ω)| ∂P := by
        simp_rw [Real.norm_eq_abs, abs_mul]
        exact integral_const_mul _ _
      _ ≤ |φ x| * (1 + M) := mul_le_mul_of_nonneg_left hmean (abs_nonneg _)
      _ = (1 + M) * |φ x| := by ring
  have hHint : Integrable H volume := by
    have hmajor : Integrable (fun x : Plane => (1 + M) * |φ x|) :=
      hφ.const_mul (1 + M)
    apply hmajor.mono' hHmeas.aestronglyMeasurable
    filter_upwards [] with x
    have hn : 0 ≤ H x := integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun ω => norm_nonneg _)
    have hmajorNonneg : 0 ≤ (1 + M) * |φ x| :=
      mul_nonneg (by linarith) (abs_nonneg _)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn, abs_of_nonneg hmajorNonneg] using
      hHbound x
  exact (integrable_prod_iff hW).mpr ⟨Filter.Eventually.of_forall hsection, hHint⟩


/-- Square integrability of a real field implies integrability of its absolute value. -/
theorem integrable_abs_of_integrable_sq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : AEStronglyMeasurable f P)
    (hsq : Integrable (fun ω => |f ω| ^ 2) P) : Integrable (fun ω => |f ω|) P := by
  have hplus : Integrable (fun ω => (1 : ℝ) + |f ω| ^ 2) P :=
    (integrable_const (1 : ℝ)).add hsq
  have habs : Integrable (fun ω => |f ω|) P := by
    apply hplus.mono' hf.norm
    filter_upwards [] with ω
    simp only [Real.norm_eq_abs, abs_abs]
    nlinarith [sq_nonneg (|f ω| - 1)]
  exact habs

/-- An upper bound for the nonnegative integral of an integrable absolute value also bounds its Bochner integral. -/
theorem integral_abs_le_of_lintegral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {f : Ω → ℝ} (hf : Integrable (fun ω => |f ω|) P)
    {B : ℝ} (hB : 0 ≤ B)
    (hlin : ∫⁻ ω, ENNReal.ofReal |f ω| ∂P ≤ ENNReal.ofReal B) :
    ∫ ω, |f ω| ∂P ≤ B := by
  have hEq := ofReal_integral_eq_lintegral_ofReal hf
    (Filter.Eventually.of_forall fun ω => abs_nonneg (f ω))
  rw [← hEq] at hlin
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hlin

/-- Compact test weights make every bounded jointly measurable field product integrable. -/
theorem integrable_test_mul_bounded_joint {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {F : Plane × Ω → ℝ}
    (hF : AEMeasurable F (volume.prod P)) {C : ℝ} (_hC : 0 ≤ C)
    (hbound : ∀ q, |F q| ≤ C) (φ : TestFn) :
    Integrable (fun q : Plane × Ω => φ q.1 * F q) (volume.prod P) := by
  have hφ : Integrable (fun x : Plane => |φ x|) :=
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).norm
  have hbase : Integrable (fun q : Plane × Ω => |φ q.1|) (volume.prod P) :=
    hφ.comp_fst P
  have hmajor : Integrable (fun q : Plane × Ω => C * |φ q.1|) (volume.prod P) :=
    hbase.const_mul C
  have hmeas : AEStronglyMeasurable (fun q : Plane × Ω => φ q.1 * F q)
      (volume.prod P) :=
    (φ.continuous.measurable.comp measurable_fst).aestronglyMeasurable.mul
      hF.aestronglyMeasurable
  apply hmajor.mono' hmeas
  filter_upwards [] with q
  rw [Real.norm_eq_abs, abs_mul]
  calc
    |φ q.1| * |F q| ≤ |φ q.1| * C :=
      mul_le_mul_of_nonneg_left (hbound q) (abs_nonneg _)
    _ = C * |φ q.1| := by ring

/-- A uniform second-moment bound for a convergent sequence transfers to its limiting law,
including integrability of the limiting square. -/
private theorem integrable_sq_limit_of_tendstoInDistribution
    {Ω' Ω : Type*} [MeasurableSpace Ω'] [MeasurableSpace Ω]
    {μ : ℕ → Measure Ω'} {P : Measure Ω} [∀ N, IsProbabilityMeasure (μ N)]
    [IsProbabilityMeasure P] {X : ℕ → Ω' → ℝ} {Y : Ω → ℝ} {M : ℝ}
    (hX : TendstoInDistribution X atTop Y μ P)
    (hint : ∀ᶠ N in atTop, Integrable (fun ω => |X N ω| ^ 2) (μ N))
    (hbound : ∀ᶠ N in atTop, ∫ ω, |X N ω| ^ 2 ∂(μ N) ≤ M) :
    Integrable (fun ω => |Y ω| ^ 2) P ∧ ∫ ω, |Y ω| ^ 2 ∂P ≤ M := by
  have hopen : ∀ G, IsOpen G → (P.map Y) G ≤
      atTop.liminf (fun N => ((μ N).map (X N)) G) := by
    intro G hG
    exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto hX.tendsto hG
  have hport := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    (μ := P.map Y) (μs := fun N => (μ N).map (X N))
    (f := fun x : ℝ => |x| ^ (2 : ℕ))
    (by fun_prop : Continuous (fun x : ℝ => |x| ^ (2 : ℕ)))
    (fun _ => sq_nonneg _) hopen
  have hmapY : ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ (2 : ℕ)) ∂P.map Y =
      ∫⁻ ω, ENNReal.ofReal (|Y ω| ^ (2 : ℕ)) ∂P :=
    lintegral_map' (by fun_prop) hX.aemeasurable_limit
  have hmapN : ∀ᶠ N in atTop,
      ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ (2 : ℕ)) ∂(μ N).map (X N) =
        ENNReal.ofReal (∫ ω, |X N ω| ^ 2 ∂(μ N)) := by
    filter_upwards [hint] with N hN
    rw [lintegral_map' (by fun_prop) (hX.forall_aemeasurable N)]
    rw [← ofReal_integral_eq_lintegral_ofReal hN
      (Filter.Eventually.of_forall fun ω => sq_nonneg (|X N ω|))]
  have hport' : ∫⁻ ω, ENNReal.ofReal (|Y ω| ^ (2 : ℕ)) ∂P ≤
      atTop.liminf (fun N => ENNReal.ofReal (∫ ω, |X N ω| ^ 2 ∂(μ N))) := by
    rw [← hmapY]
    exact hport.trans_eq (liminf_congr hmapN)
  have hbound' : ∫⁻ ω, ENNReal.ofReal (|Y ω| ^ (2 : ℕ)) ∂P ≤ ENNReal.ofReal M := by
    calc
      _ ≤ atTop.liminf (fun N => ENNReal.ofReal (∫ ω, |X N ω| ^ 2 ∂(μ N))) := hport'
      _ ≤ ENNReal.ofReal M := by
        refine liminf_le_of_le (by isBoundedDefault) (fun b hb => ?_)
        obtain ⟨N, hN⟩ :=
          (hb.and (hbound.mono fun N hN => ENNReal.ofReal_le_ofReal hN)).exists
        exact hN.1.trans hN.2
  have hM : 0 ≤ M := by
    obtain ⟨N, hN⟩ := hbound.exists
    exact (integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun ω => sq_nonneg (|X N ω|))).trans hN
  have hYmeas : AEStronglyMeasurable Y P := hX.aemeasurable_limit.aestronglyMeasurable
  have hsqMeas : AEStronglyMeasurable (fun ω => |Y ω| ^ (2 : ℕ)) P := by
    exact (by fun_prop : Continuous (fun x : ℝ => |x| ^ (2 : ℕ))).comp_aestronglyMeasurable hYmeas
  have hsqInt : Integrable (fun ω => |Y ω| ^ 2) P := by
    refine ⟨hsqMeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun ω => sq_nonneg (|Y ω|))]
    exact lt_of_le_of_lt hbound' ENNReal.ofReal_lt_top
  refine ⟨hsqInt, ?_⟩
  have hreal := hbound'
  rw [← ofReal_integral_eq_lintegral_ofReal hsqInt
    (Filter.Eventually.of_forall fun ω => sq_nonneg (|Y ω|))] at hreal
  exact (ENNReal.ofReal_le_ofReal_iff hM).mp hreal

/-- Pointwise log convergence transfers the uniform lattice second-moment bound to the SHF log
field, uniformly in its spatial center. -/
theorem shf_heatStartLogField_square_bound (ϑ : ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hpair : ∀ {s t δ : ℝ}, 0 ≤ s → s < t → 0 < δ → ∀ (x : Plane) (g : Plane →ᵇ ℝ),
      (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane =>
        heatKernel δ (p.1 - x) * g p.2) (Z s t ω)) ∧
      Integrable (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) P ∧
      (∫ ω, |shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω| ∂P ≤ ‖g‖) ∧
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) =>
          ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(polymerMeasure ϑ N s t ω))
        atTop (shfPairing Z s t (fun y => heatKernel δ (y - x)) g)
        (fun _ => disorderLaw) P)
    (hjoint : ∀ (k : ℕ) (s t δ : Fin k → ℝ) (x : Fin k → Plane)
      (g : Fin k → (Plane →ᵇ ℝ)),
      (∀ i, 0 ≤ s i ∧ s i < t i ∧ 0 < δ i) →
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
          ∫ p, heatKernel (δ i) (p.1 - x i) * g i p.2
            ∂(polymerMeasure ϑ N (s i) (t i) ω))
        atTop (fun ω i => shfPairing Z (s i) (t i)
          (fun y => heatKernel (δ i) (y - x i)) (g i) ω)
        (fun _ => disorderLaw) P)
    (hpos : ∀ (s t δ : ℝ) (x : Plane) (h₀ : Plane →ᵇ ℝ),
      0 ≤ s → s < t → 0 < δ →
      (∀ᵐ ω ∂P, 0 < shfPairing Z s t (fun y => heatKernel δ (y - x))
        (fun y => Real.exp (h₀ y)) ω) ∧
      AEMeasurable (fun ω => Real.log (shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)) P)
    (T : ℝ) (h₀ : Plane →ᵇ ℝ) {s δ : ℝ} (hs : 0 ≤ s)
    (hsT : s < T) (hδ : 0 < δ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Plane,
      Integrable (fun ω => |Real.log (shfPairing Z s T
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)| ^ 2) P ∧
      ∫ ω, |Real.log (shfPairing Z s T
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)| ^ 2 ∂P ≤ M := by
  obtain ⟨C, hC, hCN⟩ := heatStartLogProfile_square_bound ϑ hs hsT hδ h₀
  let M : ℝ := C * 2 * Real.Gamma 2
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (mul_nonneg hC (by norm_num))
      (Real.Gamma_pos_of_pos (by norm_num)).le
  refine ⟨M, hM, ?_⟩
  intro x
  have hconv := heatStart_log_tendsto_of ϑ P Z hZ hpair hjoint hpos T h₀ 1
    (fun _ => s) (fun _ => δ) (fun _ => x)
    (by intro i; exact ⟨hs, hsT, hδ⟩)
  have hscalar := hconv.2.1.continuous_comp (g := fun v : Fin 1 → ℝ => v 0)
    (continuous_apply 0)
  have hTID : TendstoInDistribution
      (fun N ω => heatStartLogProfile ϑ N s T δ x h₀ ω) atTop
      (fun ω => Real.log (shfPairing Z s T
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω))
      (fun _ => disorderLaw) P := by
    simpa [heatStartLogProfile, Function.comp_def] using hscalar
  have hN : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => |heatStartLogProfile ϑ N s T δ x h₀ ω| ^ 2) disorderLaw ∧
      ∫ ω, |heatStartLogProfile ϑ N s T δ x h₀ ω| ^ 2 ∂disorderLaw ≤ M := by
    filter_upwards [hCN] with N hN
    exact ⟨hN x |>.1, by simpa [M, heatStartLogProfile] using hN x |>.2⟩
  exact integrable_sq_limit_of_tendstoInDistribution hTID
    (hN.mono fun N hN => hN.1) (hN.mono fun N hN => hN.2)

/-- Uniform exponential tails of the lattice heat-start logarithms transfer every positive
absolute moment, including its integrability, to the limiting SHF logarithm. -/
theorem shf_heatStartLogField_rpow_bound_of
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) {s T δ : ℝ}
    (h₀ : Plane →ᵇ ℝ) {q : ℝ} (hq : 0 < q)
    (hTail : ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, ∀ x : Plane, ∀ u : ℝ, 0 ≤ u →
      (disorderLaw {ω | u < |Real.log (profileP2Fun (criticalBeta ϑ N)
        (evenCeil (N * s)) (evenCeil (N * T))
        (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x))
        (cellAverage N fun y => Real.exp (h₀ y)) ω)|}).toReal ≤ C * Real.exp (-u))
    (hconv : ∀ x : Plane, TendstoInDistribution
      (fun N ω => heatStartLogProfile ϑ N s T δ x h₀ ω) atTop
      (fun ω => Real.log (shfPairing Z s T
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω))
      (fun _ => disorderLaw) P) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Plane,
      Integrable (fun ω => |Real.log (shfPairing Z s T
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)| ^ q) P ∧
      ∫ ω, |Real.log (shfPairing Z s T
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)| ^ q ∂P ≤ M := by
  obtain ⟨Ctail, htail⟩ := hTail
  have hCtail : 0 ≤ Ctail := by
    obtain ⟨N, hN⟩ := htail.exists
    have hmeasure : 0 ≤ (disorderLaw {ω | 0 <
        |Real.log (profileP2Fun (criticalBeta ϑ N)
          (evenCeil (N * s)) (evenCeil (N * T))
          (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N 0))
          (cellAverage N fun y => Real.exp (h₀ y)) ω)|}).toReal := ENNReal.toReal_nonneg
    exact hmeasure.trans (by simpa using hN 0 0 le_rfl)
  let M : ℝ := Ctail * q * Real.Gamma q
  have hM : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (mul_nonneg hCtail hq.le) (Real.Gamma_pos_of_pos hq).le
  refine ⟨M, hM, ?_⟩
  intro x
  have hN : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => |heatStartLogProfile ϑ N s T δ x h₀ ω| ^ q) disorderLaw ∧
      ∫ ω, |heatStartLogProfile ϑ N s T δ x h₀ ω| ^ q ∂disorderLaw ≤ M := by
    filter_upwards [htail] with N htailN
    let f : Disorder → ℝ := heatStartLogProfile ϑ N s T δ x h₀
    have hf : AEMeasurable f disorderLaw := by
      dsimp [f, heatStartLogProfile]
      exact (Polymer.measurable_profileP2Fun (criticalBeta ϑ N)
        (evenCeil (N * s)) (evenCeil (N * T))
        (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x))
        (cellAverage N fun y => Real.exp (h₀ y))).log.aemeasurable
    have htailf : ∀ u : ℝ, 0 ≤ u →
        (disorderLaw {ω | u < |f ω|}).toReal ≤ Ctail * Real.exp (-u) := by
      intro u hu
      simpa [f, heatStartLogProfile] using htailN x u hu
    have hmoment := integrable_rpow_of_exp_tail hf hCtail hq htailf
    exact ⟨hmoment.1, by simpa [f, heatStartLogProfile, M] using hmoment.2⟩
  exact integrable_rpow_limit_of_tendstoInDistribution (hconv x) hq
    (hN.mono fun N hN => hN.1) (hN.mono fun N hN => hN.2)

end Critical2DKPZ.JointConvergence

end
