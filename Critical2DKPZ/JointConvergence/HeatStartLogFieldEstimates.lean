/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.JointConvergence.HeatStartLogFieldConvergence
public import Critical2DKPZ.SHF.Positivity.HeatBoundedIntegrability
public import Critical2DKPZ.SHF.Positivity.MeasurablePairing
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Estimates for spatial heat-start logarithm fields -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Positivity
open scoped BigOperators BoundedContinuousFunction ENNReal Topology

namespace Critical2DKPZ.JointConvergence

/-- Convergence of the `L¹` seminorm to zero implies convergence in distribution on a probability
space. -/
private theorem tendstoInDistribution_of_tendsto_eLpNorm_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (Y : ℕ → Ω → Fin k → ℝ) (L : Ω → Fin k → ℝ)
    (hY : ∀ j, AEMeasurable (Y j) P)
    (hNorm : Tendsto (fun j => eLpNorm (fun ω => Y j ω - L ω) 1 P)
      atTop (𝓝 0)) :
    TendstoInDistribution Y atTop L (fun _ => P) P := by
  have hMeasure : TendstoInMeasure P Y atTop L :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := (1 : ℝ≥0∞)) (by norm_num) hNorm
  exact hMeasure.tendstoInDistribution hY

private theorem pi_norm_le_sum_norm {k : ℕ} (v : Fin k → ℝ) :
    ‖v‖ ≤ ∑ i : Fin k, ‖v i‖ := by
  apply (pi_norm_le_iff_of_nonneg
    (Finset.sum_nonneg fun i hi => norm_nonneg (v i))).2
  intro i
  exact Finset.single_le_sum (fun j hj => norm_nonneg (v j)) (Finset.mem_univ i)

private theorem lintegral_norm_pi_le_of_component_bounds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {k : ℕ}
    (D : Ω → Fin k → ℝ) (hD : AEMeasurable D P)
    (hDint : ∀ i, Integrable (fun ω => ‖D ω i‖) P)
    (B : Fin k → ℝ) (hB : ∀ i, ∫ ω, ‖D ω i‖ ∂P ≤ B i) :
    ∫⁻ ω, ENNReal.ofReal ‖D ω‖ ∂P ≤ ENNReal.ofReal (∑ i, B i) := by
  have hsumInt : Integrable (fun ω => ∑ i : Fin k, ‖D ω i‖) P :=
    integrable_finsetSum Finset.univ (fun i hi => hDint i)
  have hnormInt : Integrable (fun ω => ‖D ω‖) P := by
    apply hsumInt.mono' hD.aestronglyMeasurable.norm
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
      pi_norm_le_sum_norm (D ω)
  have hsumBound : ∫ ω, ‖D ω‖ ∂P ≤ ∑ i, B i := by
    calc
      _ ≤ ∫ ω, ∑ i : Fin k, ‖D ω i‖ ∂P := by
        apply integral_mono hnormInt hsumInt
        intro ω
        exact pi_norm_le_sum_norm (D ω)
      _ = ∑ i, ∫ ω, ‖D ω i‖ ∂P :=
        integral_finsetSum Finset.univ (fun i hi => hDint i)
      _ ≤ ∑ i, B i := Finset.sum_le_sum fun i hi => hB i
  have hnonneg : ∀ᵐ ω ∂P, 0 ≤ ‖D ω‖ :=
    Filter.Eventually.of_forall fun ω => norm_nonneg _
  rw [← ofReal_integral_eq_lintegral_ofReal hnormInt hnonneg]
  exact ENNReal.ofReal_le_ofReal hsumBound

private theorem tendstoInDistribution_of_integral_norm_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} (Y : ℕ → Ω → Fin k → ℝ) (L : Ω → Fin k → ℝ)
    (hY : ∀ j, AEMeasurable (Y j) P) (hL : AEMeasurable L P)
    (hDint : ∀ j, Integrable (fun ω => ‖Y j ω - L ω‖) P)
    (B : ℕ → ℝ) (hBlim : Tendsto B atTop (𝓝 0))
    (hB : ∀ j, ∫ ω, ‖Y j ω - L ω‖ ∂P ≤ B j) :
    TendstoInDistribution Y atTop L (fun _ => P) P := by
  have hDsm (j : ℕ) : AEStronglyMeasurable (fun ω => Y j ω - L ω) P :=
    (hY j).aestronglyMeasurable.sub hL.aestronglyMeasurable
  have hLpBound (j : ℕ) : eLpNorm (fun ω => Y j ω - L ω) 1 P ≤ ENNReal.ofReal (B j) := by
    calc
      eLpNorm (fun ω => Y j ω - L ω) 1 P =
          ∫⁻ ω, ‖Y j ω - L ω‖ₑ ∂P := eLpNorm_one_eq_lintegral_enorm (hDsm j)
      _ = ∫⁻ ω, ENNReal.ofReal ‖Y j ω - L ω‖ ∂P := by
        apply lintegral_congr
        intro ω
        exact (ofReal_norm _).symm
      _ = ENNReal.ofReal (∫ ω, ‖Y j ω - L ω‖ ∂P) := by
        symm
        exact ofReal_integral_eq_lintegral_ofReal (hDint j)
          (Filter.Eventually.of_forall fun ω => norm_nonneg _)
      _ ≤ ENNReal.ofReal (B j) := ENNReal.ofReal_le_ofReal (hB j)
  have hOfReal : Tendsto (fun j => ENNReal.ofReal (B j)) atTop (𝓝 0) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hBlim
    convert h using 1
    ext j
    rfl
    simp
  have hNorm : Tendsto (fun j => eLpNorm (fun ω => Y j ω - L ω) 1 P)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hOfReal
      (fun j => (bot_le : 0 ≤ eLpNorm (fun ω => Y j ω - L ω) 1 P))
      hLpBound
  exact tendstoInDistribution_of_tendsto_eLpNorm_one P Y L hY hNorm

private theorem exists_lattice_mesh_for_finite_coefficients {k : ℕ}
    (Q : Fin k → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ ∀ i,
      Q i * (Real.sqrt ((m : ℝ) / 2))⁻¹ ≤ ε := by
  have hsmall (i : Fin k) : ∀ᶠ m : ℕ in atTop,
      Q i * (Real.sqrt ((m : ℝ) / 2))⁻¹ < ε := by
    have hlim : Tendsto (fun m : ℕ => Q i * (Real.sqrt ((m : ℝ) / 2))⁻¹)
        atTop (𝓝 0) := by
      simpa using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => Q i) atTop (𝓝 (Q i))).mul
          tendsto_lattice_mesh
    exact hlim.eventually (Iio_mem_nhds hε)
  have hAll : ∀ᶠ m : ℕ in atTop, ∀ i : Fin k,
      Q i * (Real.sqrt ((m : ℝ) / 2))⁻¹ < ε := Filter.eventually_all.mpr hsmall
  obtain ⟨m, hmAll, hmpos⟩ := (hAll.and (eventually_gt_atTop 0)).exists
  refine ⟨m, hmpos, ?_⟩
  intro i
  exact (hmAll i).le

private theorem tendsto_const_div_nat_add_one (C : ℝ) :
    Tendsto (fun j : ℕ => C / ((j : ℝ) + 1)) atTop (𝓝 0) := by
  have hden : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop := by
    convert (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      (tendsto_add_atTop_nat 1) using 1
    ext j
    simp
  have hinv : Tendsto (fun j : ℕ => ((j : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    hden.inv_tendsto_atTop
  simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul hinv

private theorem tendsto_exp_neg_nat_add_one :
    Tendsto (fun j : ℕ => Real.exp (-((j : ℝ) + 1))) atTop (𝓝 0) := by
  have hden : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop := by
    convert (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      (tendsto_add_atTop_nat 1) using 1
    ext j
    simp
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp hden using 1
  ext j
  simp

/-- The logarithm clamp error has an integrable absolute value and its integral is controlled by
the square moment of the logarithm. -/
private theorem integrable_abs_log_sub_heatStartLogClamp_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → ℝ}
    (hf : AEMeasurable f P) (hpos : ∀ᵐ ω ∂P, 0 < f ω)
    (hlogSq : Integrable (fun ω => |Real.log (f ω)| ^ 2) P)
    {M R : ℝ} (hM : 0 ≤ M)
    (hMbound : ∫ ω, |Real.log (f ω)| ^ 2 ∂P ≤ M) (hR : 0 < R) :
    Integrable (fun ω => |Real.log (f ω) - heatStartLogClamp R (f ω)|) P ∧
      ∫ ω, |Real.log (f ω) - heatStartLogClamp R (f ω)| ∂P ≤ M / R := by
  have htail := lintegral_abs_log_clamp_le hf hpos hlogSq hMbound hR
  have hlogMeas : AEMeasurable (fun ω => Real.log (f ω)) P :=
    Real.measurable_log.comp_aemeasurable hf
  have hlogAbs := integrable_abs_of_integrable_sq hlogMeas.aestronglyMeasurable hlogSq
  have hlogInt : Integrable (fun ω => Real.log (f ω)) P := by
    apply (integrable_norm_iff hlogMeas.aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs] using hlogAbs
  have hclampMeas : AEMeasurable (fun ω => heatStartLogClamp R (f ω)) P :=
    (heatStartLogClamp_continuous R).measurable.comp_aemeasurable hf
  have hclampInt : Integrable (fun ω => heatStartLogClamp R (f ω)) P := by
    refine Integrable.of_bound hclampMeas.aestronglyMeasurable R ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs]
    exact abs_heatStartLogClamp_le R (f ω) hR.le
  have hdiffInt : Integrable
      (fun ω => |Real.log (f ω) - heatStartLogClamp R (f ω)|) P :=
    (hlogInt.sub hclampInt).norm
  have hbound : 0 ≤ M / R := div_nonneg hM hR.le
  refine ⟨hdiffInt, ?_⟩
  exact integral_abs_le_of_lintegral hdiffInt hbound htail

private theorem aemeasurable_polymer_heatPairing_clamp_at (ϑ : ℝ) {N : ℕ}
    (hN : 1 ≤ N) (s T δ : ℝ) (hδ : 0 < δ) (x : Plane) (h₀ : Plane →ᵇ ℝ) (R : ℝ) :
    AEMeasurable (fun ω : Disorder => heatStartLogClamp R
      (∫ p, heatKernel δ (p.1 - x) * Real.exp (h₀ p.2)
        ∂polymerMeasure ϑ N s T ω)) disorderLaw := by
  let μ : Disorder → Measure (Plane × Plane) := polymerMeasure ϑ N s T
  let g : Plane →ᵇ ℝ := heatStartExpTerminal h₀
  have hK : ∀ᵐ ω ∂disorderLaw, Integrable
      (fun p : Plane × Plane => heatKernel δ (p.1 - x)) (μ ω) :=
    ae_integrable_polymer_heat_start ϑ hN s T δ hδ x
  have hInt : ∀ᵐ ω ∂disorderLaw, Integrable
      (fun p : Plane × Plane => heatKernel δ (p.1 - x) * g p.2) (μ ω) := by
    filter_upwards [hK] with ω hω
    exact integrable_heatKernel_mul_boundedTerminal (μ ω) hδ x g hω
  have hraw := aemeasurable_integral_of_measurable_measure disorderLaw μ
    (measurable_polymerMeasure ϑ N s T)
    (fun p => heatKernel δ (p.1 - x) * g p.2)
    ((((measurable_heatKernel δ).comp (measurable_fst.sub_const x)).mul
      (g.continuous.measurable.comp measurable_snd))) hInt
  have hclamp := (heatStartLogClamp_continuous R).measurable.comp_aemeasurable hraw
  exact hclamp.congr (Filter.Eventually.of_forall fun ω => by
    simp [μ, g, heatStartExpTerminal_apply])

private theorem aemeasurable_shf_heatPairing_clamp_at {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    {ϑ : ℝ} (hZ : IsCriticalSHF ϑ P Z)
    (hpair : ∀ {s t δ : ℝ}, 0 ≤ s → s < t → 0 < δ →
      ∀ (x : Plane) (g : Plane →ᵇ ℝ),
        (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane =>
          heatKernel δ (p.1 - x) * g p.2) (Z s t ω)) ∧
        Integrable (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) P ∧
        (∫ ω, |shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω| ∂P ≤ ‖g‖) ∧
        TendstoInDistribution
          (fun (N : ℕ) (ω : Disorder) =>
            ∫ p, heatKernel δ (p.1 - x) * g p.2
              ∂polymerMeasure ϑ N s t ω)
          atTop (shfPairing Z s t (fun y => heatKernel δ (y - x)) g)
          (fun _ => disorderLaw) P)
    (s T δ : ℝ) (hs : 0 ≤ s) (hsT : s < T) (hδ : 0 < δ)
    (x : Plane) (h₀ : Plane →ᵇ ℝ) (R : ℝ) :
    AEMeasurable (fun ω : Ω => heatStartLogClamp R
      (shfPairing Z s T (fun y => heatKernel δ (y - x))
        (fun y => Real.exp (h₀ y)) ω)) P := by
  let μ : Ω → Measure (Plane × Plane) := Z s T
  let g : Plane →ᵇ ℝ := heatStartExpTerminal h₀
  have hInt := (hpair (s := s) (t := T) (δ := δ) hs hsT hδ x g).1
  have hraw := aemeasurable_integral_of_measurable_measure P μ
    (hZ.1 s T hs hsT)
    (fun p => heatKernel δ (p.1 - x) * g p.2)
    ((((measurable_heatKernel δ).comp (measurable_fst.sub_const x)).mul
      (g.continuous.measurable.comp measurable_snd))) hInt
  have hclamp := (heatStartLogClamp_continuous R).measurable.comp_aemeasurable hraw
  exact hclamp.congr (Filter.Eventually.of_forall fun ω => by
    simp [μ, g, heatStartExpTerminal_apply, shfPairing])

private theorem aemeasurable_latticeSiteSum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (m : ℕ) (S : Finset Site)
    (F : Site → Ω → ℝ) (hF : ∀ z, AEMeasurable (F z) P) :
    AEMeasurable (fun q : Plane × Ω =>
      ∑ z : S.attach, if latticePoint m q.1 = z.1 then F z.1 q.2 else 0)
      (volume.prod P) := by
  classical
  have hterm (z : ↥S.attach) : AEMeasurable
      (fun q : Plane × Ω => if latticePoint m q.1 = z.1 then F z.1 q.2 else 0)
      (volume.prod P) := by
    let E : Set (Plane × Ω) := {q | latticePoint m q.1 = z.1}
    have hE : MeasurableSet E := by
      change MeasurableSet
        ((fun q : Plane × Ω => latticePoint m q.1) ⁻¹' ({(z.1 : Site)} : Set Site))
      exact (measurableSet_singleton (z.1 : Site)).preimage
        ((measurable_latticePoint m).comp measurable_fst)
    have hFz : AEMeasurable (fun q : Plane × Ω => F z.1 q.2) (volume.prod P) :=
      (hF z.1).comp_snd
    have h := (aemeasurable_indicator_iff hE).2
      (hFz.mono_measure Measure.restrict_le_self)
    convert h using 1
    ext q
    simp [Set.indicator, E]
  have hsum : ∀ s : Finset (↥S.attach), AEMeasurable
      (fun q : Plane × Ω => ∑ z ∈ s, if latticePoint m q.1 = z.1 then F z.1 q.2 else 0)
      (volume.prod P) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact aemeasurable_const
    | @insert z s hz ih =>
        simp only [Finset.sum_insert hz]
        exact (hterm z).add ih
  exact hsum Finset.univ

private theorem latticeSiteSum_eq_sample_of_mem {Ω : Type*} (m : ℕ)
    (S : Finset Site) (F : Site → Ω → ℝ) {x : Plane} (ω : Ω)
    (hx : latticePoint m x ∈ S) :
    (∑ z : S.attach,
      if latticePoint m x = z.1 then F z.1 ω else 0) = F (latticePoint m x) ω := by
  classical
  let z₀ : ↥S := ⟨latticePoint m x, hx⟩
  let z₀' : ↥S.attach := ⟨z₀, Finset.mem_attach S z₀⟩
  change (∑ z ∈ (Finset.univ : Finset (↥S.attach)),
      if latticePoint m x = z.1.1 then F z.1.1 ω else 0) =
    F (latticePoint m x) ω
  rw [Finset.sum_eq_single z₀']
  · simp [z₀, z₀']
  · intro z hz hzne
    have hne : latticePoint m x ≠ z.1.1 := by
      intro heq
      apply hzne
      apply Subtype.ext
      apply Subtype.ext
      exact heq.symm
    simp [hne]
  · intro hz
    exact (hz (Finset.mem_univ _)).elim

private theorem aemeasurable_sum_of_finite_index {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (P : Measure Ω) (F : ι → Ω → ℝ)
    (hF : ∀ i, AEMeasurable (F i) P) :
    AEMeasurable (fun ω => ∑ i : ι, F i ω) P := by
  classical
  have hsum : ∀ s : Finset ι, AEMeasurable (fun ω => ∑ i ∈ s, F i ω) P := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact aemeasurable_const
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        exact (hF i).add ih
  exact hsum Finset.univ

private theorem aemeasurable_latticeSiteSum_section {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (m : ℕ) (S : Finset Site) (F : Site → Ω → ℝ)
    (hF : ∀ z, AEMeasurable (F z) P) (x : Plane) :
    AEMeasurable (fun ω => ∑ z : S.attach,
      if latticePoint m x = z.1 then F z.1 ω else 0) P := by
  classical
  apply aemeasurable_sum_of_finite_index
  intro z
  by_cases hz : latticePoint m x = z.1
  · simpa [hz] using hF z.1
  · simp [hz]

private theorem latticeSiteSum_eq_siteFunction {Ω : Type*} (m : ℕ)
    (S : Finset Site) (F : Site → Ω → ℝ) (x : Plane) (ω : Ω) :
    (∑ z : S.attach,
      if latticePoint m x = z.1 then F z.1 ω else 0) =
      if latticePoint m x ∈ S then F (latticePoint m x) ω else 0 := by
  classical
  by_cases hx : latticePoint m x ∈ S
  · rw [latticeSiteSum_eq_sample_of_mem m S F ω hx]
    simp [hx]
  · have hrhs : (if latticePoint m x ∈ S then F (latticePoint m x) ω else 0) = 0 := by
      split_ifs; simp_all
    rw [hrhs]
    apply Finset.sum_eq_zero
    intro z hz
    have hne : latticePoint m x ≠ z.1.1 := by
      intro heq
      exact hx (heq ▸ z.1.2)
    simp [hne]

private theorem sum_attached_sites_type {S : Finset Site} (f : Site → ℝ) :
    (∑ z : S.attach, f z.1) = ∑ z ∈ S, f z := by
  classical
  have huniv : (Finset.univ : Finset (↥S.attach)) = S.attach.attach := by
    ext z
    simp
  change (∑ z ∈ (Finset.univ : Finset (↥S.attach)), f z.1.1) = _
  rw [huniv]
  calc
    (∑ z ∈ S.attach.attach, f z.1.1) = ∑ z ∈ S.attach, f z.1 :=
      Finset.sum_attach (s := S.attach) (f := fun z => f z.1)
    _ = ∑ z ∈ S, f z := Finset.sum_attach (s := S) (f := f)

private theorem integral_test_latticeSiteSum_eq {φ : TestFn} (m : ℕ) (S : Finset Site)
    (F : Site → ℝ) (hS : ∀ x, φ x ≠ 0 → latticePoint m x ∈ S) :
    (∫ x, φ x * (∑ z : S.attach,
      if latticePoint m x = z.1 then F z.1 else 0)) =
      ∑ z : S.attach, (∫ x in cell m z.1, φ x) * F z.1 := by
  classical
  let G : Site → ℝ := fun z => if z ∈ S then F z else 0
  have hEq (x : Plane) :
      (∑ z : S.attach, if latticePoint m x = z.1 then F z.1 else 0) =
        G (latticePoint m x) := by
    simpa [G] using latticeSiteSum_eq_siteFunction m S
      (fun (z : Site) (_ : Unit) => F z) x ()
  calc
    _ = ∫ x, φ x * G (latticePoint m x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change φ x * _ = φ x * _
        rw [hEq x]
    _ = ∑ z ∈ S, (∫ x in cell m z, φ x) * G z :=
      integral_mul_latticePoint_piecewise φ.continuous φ.hasCompactSupport m G S hS
    _ = ∑ z ∈ S, (∫ x in cell m z, φ x) * F z := by
      apply Finset.sum_congr rfl
      intro z hz
      simp [G, hz]
    _ = ∑ z : S.attach, (∫ x in cell m z.1, φ x) * F z.1 :=
      (sum_attached_sites_type (S := S)
        (fun z => (∫ x in cell m z, φ x) * F z)).symm

/-- The field form of the test-integral estimate, with the pointwise error needed only on the
support of the test function. -/
private theorem integral_test_field_difference_l1_on_support_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {F G : Plane × Ω → ℝ} (φ : TestFn)
    (hF : Integrable (fun q => φ q.1 * F q) (volume.prod P))
    (hG : Integrable (fun q => φ q.1 * G q) (volume.prod P))
    (hsec : ∀ x, Integrable (fun ω => |F (x, ω) - G (x, ω)|) P)
    {B : ℝ} (_hB : 0 ≤ B)
    (hpoint : ∀ x, φ x ≠ 0 →
      ∫ ω, |F (x, ω) - G (x, ω)| ∂P ≤ B) :
    Integrable (fun ω => ∫ x, φ x * (F (x, ω) - G (x, ω))) P ∧
      ∫ ω, |∫ x, φ x * (F (x, ω) - G (x, ω))| ∂P ≤ B * ∫ x, |φ x| := by
  let Q : Plane × Ω → ℝ := fun q => φ q.1 * (F q - G q)
  have hQ : Integrable Q (volume.prod P) := by
    have h := hF.sub hG
    convert h using 1
    ext q
    simp [Q, mul_sub]
  have hQswap := hQ.swap
  have hQnorm := hQ.norm
  have hQnormSwap := hQnorm.swap
  have hJint : Integrable (fun ω => ∫ x, Q (x, ω)) P := hQswap.integral_prod_left
  have hHint : Integrable (fun ω => ∫ x, ‖Q (x, ω)‖ ∂volume) P :=
    hQnormSwap.integral_prod_left
  have hpoint' (x : Plane) : ∫ ω, ‖Q (x, ω)‖ ∂P ≤ B * |φ x| := by
    by_cases hx : φ x = 0
    · simp [Q, hx]
    · have hsecx := hsec x
      calc
        ∫ ω, ‖Q (x, ω)‖ ∂P = |φ x| * ∫ ω, |F (x, ω) - G (x, ω)| ∂P := by
          simp only [Q, Real.norm_eq_abs, abs_mul]
          rw [integral_const_mul]
        _ ≤ |φ x| * B := mul_le_mul_of_nonneg_left (hpoint x hx) (abs_nonneg _)
        _ = B * |φ x| := by ring
  have hφ : Integrable (fun x : Plane => |φ x|) :=
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).norm
  have hmajor : Integrable (fun x : Plane => B * |φ x|) := hφ.const_mul B
  have hHmeas : AEMeasurable (fun x => ∫ ω, ‖Q (x, ω)‖ ∂P) volume :=
    hQnorm.aestronglyMeasurable.integral_prod_right'.aemeasurable
  have hHintX : Integrable (fun x => ∫ ω, ‖Q (x, ω)‖ ∂P) volume := by
    apply hmajor.mono' hHmeas.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun ω => norm_nonneg _))]
    exact hpoint' x
  have hHbound : ∫ x, (∫ ω, ‖Q (x, ω)‖ ∂P) ≤ B * ∫ x, |φ x| := by
    calc
      _ ≤ ∫ x, B * |φ x| := integral_mono hHintX hmajor hpoint'
      _ = B * ∫ x, |φ x| := integral_const_mul _ _
  have hswap : (∫ ω, (∫ x, ‖Q (x, ω)‖ ∂volume) ∂P) =
      ∫ x, (∫ ω, ‖Q (x, ω)‖ ∂P) ∂volume := by
    calc
      _ = ∫ q, ‖Q q‖ ∂(volume.prod P) := (integral_prod_symm _ hQnorm).symm
      _ = ∫ x, (∫ ω, ‖Q (x, ω)‖ ∂P) ∂volume := integral_prod _ hQnorm
  have hJbound : (∫ ω, ‖∫ x, Q (x, ω) ∂volume‖ ∂P) ≤
      ∫ ω, (∫ x, ‖Q (x, ω)‖ ∂volume) ∂P := by
    apply integral_mono hJint.norm hHint
    intro ω
    exact norm_integral_le_integral_norm _
  have hJbound' : ∫ ω, ‖∫ x, Q (x, ω) ∂volume‖ ∂P ≤ B * ∫ x, |φ x| := by
    rw [hswap] at hJbound
    exact hJbound.trans hHbound
  refine ⟨?_, ?_⟩
  · simpa only [Q, mul_sub] using hJint
  · simpa only [Q, Real.norm_eq_abs] using hJbound'

private theorem integrable_test_mul_bounded_field {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {F : Plane × Ω → ℝ}
    (hF : AEMeasurable F (volume.prod P))
    (hFsec : ∀ x, AEMeasurable (fun ω => F (x, ω)) P)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ q, |F q| ≤ C) (φ : TestFn) :
    Integrable (fun q => φ q.1 * F q) (volume.prod P) := by
  have hsec (x : Plane) : AEStronglyMeasurable (fun ω => F (x, ω)) P :=
    (hFsec x).aestronglyMeasurable
  have hSq (x : Plane) : Integrable (fun ω => |F (x, ω)| ^ 2) P ∧
      ∫ ω, |F (x, ω)| ^ 2 ∂P ≤ C ^ 2 := by
    have hm : AEMeasurable (fun ω => |F (x, ω)| ^ 2) P :=
      (show Measurable (fun y : ℝ => |y| ^ 2) by fun_prop).comp_aemeasurable (hFsec x)
    have hi : Integrable (fun ω => |F (x, ω)| ^ 2) P := by
      apply Integrable.of_bound hm.aestronglyMeasurable (C ^ 2)
      filter_upwards [] with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h := hbound (x, ω)
      nlinarith [abs_nonneg (F (x, ω)), hC]
    refine ⟨hi, ?_⟩
    calc
      (∫ ω, |F (x, ω)| ^ 2 ∂P) ≤ ∫ ω, C ^ 2 ∂P := by
        apply integral_mono hi (integrable_const (C ^ 2))
        intro ω
        have h := hbound (x, ω)
        nlinarith [abs_nonneg (F (x, ω)), hC]
      _ = C ^ 2 := by simp
  exact integrable_test_mul_joint P hF hsec (sq_nonneg C) hSq φ

private theorem polymer_log_profile_cellSample_error (ϑ : ℝ) {N : ℕ}
    (hN : 1 ≤ N) (s T δ : ℝ) (hs : 0 ≤ s ∧ s < T) (hδ : 0 < δ)
    (h₀ : Plane →ᵇ ℝ) (R η M C : ℝ) (hR : 0 < R) (hη : 0 < η)
    (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hKernel : ∀ u : ℝ, 0 < u → ∀ a b : Plane,
      ∫ y, |heatKernel u (y - a) - heatKernel u (y - b)| ≤
        C * ‖a - b‖ / Real.sqrt u)
    (hKernelN : ∀ x : Plane,
      ∑' w : Site,
        |srwKernel (evenCeil (N * δ)) (w - latticePoint N x) -
          ∫ y in cell N w, heatKernel δ (y - x)| ≤ η)
    (hSq : ∀ x : Plane,
      Integrable (fun ω => |heatStartLogProfile ϑ N s T δ x h₀ ω| ^ 2) disorderLaw ∧
      ∫ ω, |heatStartLogProfile ϑ N s T δ x h₀ ω| ^ 2 ∂disorderLaw ≤ M)
    (m : ℕ) (hm : 0 < m) (x : Plane) :
    Integrable (fun ω => |heatStartLogProfile ϑ N s T δ x h₀ ω -
      heatStartLogClamp R (∫ p, heatKernel δ (p.1 - cellSample m x) *
        Real.exp (h₀ p.2) ∂polymerMeasure ϑ N s T ω)|) disorderLaw ∧
    (∫ ω, |heatStartLogProfile ϑ N s T δ x h₀ ω -
      heatStartLogClamp R (∫ p, heatKernel δ (p.1 - cellSample m x) *
        Real.exp (h₀ p.2) ∂polymerMeasure ϑ N s T ω)| ∂disorderLaw) ≤
      M / R + Real.exp R * (Real.exp ‖h₀‖ * η) +
        Real.exp R * (‖heatStartExpTerminal h₀‖ *
          (C / Real.sqrt δ * (Real.sqrt ((m : ℝ) / 2))⁻¹)) := by
  let g : Plane →ᵇ ℝ := heatStartExpTerminal h₀
  have hg : (g : Plane → ℝ) = fun y => Real.exp (h₀ y) := rfl
  let A : Disorder → ℝ := fun ω =>
    ∫ p, heatKernel δ (p.1 - x) * Real.exp (h₀ p.2)
      ∂polymerMeasure ϑ N s T ω
  have hprofMeas : AEMeasurable (fun ω => heatStartLogProfile ϑ N s T δ x h₀ ω)
      disorderLaw := by
    change AEMeasurable (fun ω =>
      Real.log (profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * T))
        (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x))
        (cellAverage N fun y => Real.exp (h₀ y)) ω)) disorderLaw
    exact (Polymer.measurable_profileP2Fun (criticalBeta ϑ N)
      (evenCeil (N * s)) (evenCeil (N * T))
      (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x))
      (cellAverage N fun y => Real.exp (h₀ y))).log.aemeasurable
  have hprofInt : Integrable (fun ω => heatStartLogProfile ϑ N s T δ x h₀ ω)
      disorderLaw := by
    have habs := integrable_abs_of_integrable_sq hprofMeas.aestronglyMeasurable (hSq x).1
    apply (integrable_norm_iff hprofMeas.aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs] using habs
  have hAmeas : AEMeasurable (fun ω => heatStartLogClamp R (A ω)) disorderLaw := by
    simpa [A] using aemeasurable_polymer_heatPairing_clamp_at ϑ hN
      s T δ hδ x h₀ R
  have hAint : Integrable (fun ω => heatStartLogClamp R (A ω)) disorderLaw := by
    apply Integrable.of_bound hAmeas.aestronglyMeasurable R
    filter_upwards [] with ω
    rw [Real.norm_eq_abs]
    exact abs_heatStartLogClamp_le R (A ω) hR.le
  have hPairInt : Integrable (fun ω =>
      |heatStartLogProfile ϑ N s T δ x h₀ ω - heatStartLogClamp R (A ω)|)
      disorderLaw := (hprofInt.sub hAint).norm
  have hPairENN := heatStart_log_clamp_pair_error ϑ hN s T δ hs.2 hδ x h₀ η R M
    hR (hKernelN x) (hSq x).1 (hSq x).2
  have hPairBound : ∫ ω,
      |heatStartLogProfile ϑ N s T δ x h₀ ω - heatStartLogClamp R (A ω)|
        ∂disorderLaw ≤ M / R + Real.exp R * (Real.exp ‖h₀‖ * η) := by
    have hlin := ofReal_integral_eq_lintegral_ofReal hPairInt
      (Filter.Eventually.of_forall fun ω => abs_nonneg _)
    have hbound : 0 ≤ M / R + Real.exp R * (Real.exp ‖h₀‖ * η) :=
      add_nonneg (div_nonneg hM hR.le)
        (mul_nonneg (Real.exp_nonneg _) (mul_nonneg (Real.exp_nonneg _) hη.le))
    have hreal : ENNReal.ofReal (∫ ω,
        |heatStartLogProfile ϑ N s T δ x h₀ ω - heatStartLogClamp R (A ω)|
          ∂disorderLaw) ≤ ENNReal.ofReal (M / R + Real.exp R * (Real.exp ‖h₀‖ * η)) := by
      rw [hlin]
      exact hPairENN
    exact (ENNReal.ofReal_le_ofReal_iff hbound).mp hreal
  have hshift := polymer_heatPairing_clamp_translation_l1_le ϑ hN
    s T δ hδ R hR.le C hKernel x (cellSample m x) g
  have hmeshDist : ‖x - cellSample m x‖ ≤ (Real.sqrt ((m : ℝ) / 2))⁻¹ := by
    calc
      ‖x - cellSample m x‖ = dist x (cellSample m x) := (dist_eq_norm _ _).symm
      _ = dist (cellSample m x) x := dist_comm _ _
      _ ≤ (Real.sqrt ((m : ℝ) / 2))⁻¹ := dist_cellSample_le hm x
  have hkernelMesh : C * ‖x - cellSample m x‖ / Real.sqrt δ ≤
      C / Real.sqrt δ * (Real.sqrt ((m : ℝ) / 2))⁻¹ := by
    rw [show C * ‖x - cellSample m x‖ / Real.sqrt δ =
      (C / Real.sqrt δ) * ‖x - cellSample m x‖ by ring]
    exact mul_le_mul_of_nonneg_left hmeshDist (div_nonneg hC (Real.sqrt_nonneg _))
  have hshiftRaw : ∫ ω, |heatStartLogClamp R (A ω) -
      heatStartLogClamp R (∫ p, heatKernel δ (p.1 - cellSample m x) *
        Real.exp (h₀ p.2) ∂polymerMeasure ϑ N s T ω)| ∂disorderLaw ≤
      Real.exp R * (‖g‖ * (C / Real.sqrt δ * (Real.sqrt ((m : ℝ) / 2))⁻¹)) := by
    calc
      _ ≤ Real.exp R * (‖g‖ * (C * ‖x - cellSample m x‖ / Real.sqrt δ)) := by
        simpa only [A, hg] using hshift.2
      _ ≤ Real.exp R * (‖g‖ * (C / Real.sqrt δ * (Real.sqrt ((m : ℝ) / 2))⁻¹)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left hkernelMesh (norm_nonneg _)
        · positivity
  have hCellMeas : AEMeasurable (fun ω => heatStartLogClamp R
      (∫ p, heatKernel δ (p.1 - cellSample m x) * Real.exp (h₀ p.2)
        ∂polymerMeasure ϑ N s T ω)) disorderLaw := by
    simpa using aemeasurable_polymer_heatPairing_clamp_at ϑ hN s T δ hδ
      (cellSample m x) h₀ R
  have hCellInt : Integrable (fun ω => heatStartLogClamp R
      (∫ p, heatKernel δ (p.1 - cellSample m x) * Real.exp (h₀ p.2)
        ∂polymerMeasure ϑ N s T ω)) disorderLaw := by
    apply Integrable.of_bound hCellMeas.aestronglyMeasurable R
    filter_upwards [] with ω
    rw [Real.norm_eq_abs]
    exact abs_heatStartLogClamp_le R _ hR.le
  have hErrInt : Integrable (fun ω => |heatStartLogProfile ϑ N s T δ x h₀ ω -
      heatStartLogClamp R (∫ p, heatKernel δ (p.1 - cellSample m x) *
        Real.exp (h₀ p.2) ∂polymerMeasure ϑ N s T ω)|) disorderLaw :=
    (hprofInt.sub hCellInt).norm
  have hsumInt : Integrable (fun ω =>
      |heatStartLogProfile ϑ N s T δ x h₀ ω - heatStartLogClamp R (A ω)| +
      |heatStartLogClamp R (A ω) -
        heatStartLogClamp R (∫ p, heatKernel δ (p.1 - cellSample m x) *
          Real.exp (h₀ p.2) ∂polymerMeasure ϑ N s T ω)|) disorderLaw := by
    let hsumSrc := hPairInt.add hshift.1
    refine ⟨hsumSrc.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    exact (hasFiniteIntegral_iff_norm _).mp hsumSrc.hasFiniteIntegral
  have hpointwise (ω : Disorder) :
      |heatStartLogProfile ϑ N s T δ x h₀ ω -
        heatStartLogClamp R (∫ p, heatKernel δ (p.1 - cellSample m x) *
          Real.exp (h₀ p.2) ∂polymerMeasure ϑ N s T ω)| ≤
      |heatStartLogProfile ϑ N s T δ x h₀ ω - heatStartLogClamp R (A ω)| +
      |heatStartLogClamp R (A ω) -
        heatStartLogClamp R (∫ p, heatKernel δ (p.1 - cellSample m x) *
          Real.exp (h₀ p.2) ∂polymerMeasure ϑ N s T ω)| := abs_sub_le _ _ _
  refine ⟨hErrInt, ?_⟩
  calc
    _ ≤ ∫ ω,
        |heatStartLogProfile ϑ N s T δ x h₀ ω - heatStartLogClamp R (A ω)| +
        |heatStartLogClamp R (A ω) -
          heatStartLogClamp R (∫ p, heatKernel δ (p.1 - cellSample m x) *
            Real.exp (h₀ p.2) ∂polymerMeasure ϑ N s T ω)| ∂disorderLaw := by
      exact integral_mono hErrInt hsumInt hpointwise
    _ = _ := by
      simpa only [hg] using (integral_add hPairInt hshift.1)
    _ ≤ M / R + Real.exp R * (Real.exp ‖h₀‖ * η) +
        Real.exp R * (‖g‖ * (C / Real.sqrt δ * (Real.sqrt ((m : ℝ) / 2))⁻¹)) :=
      add_le_add hPairBound hshiftRaw

end Critical2DKPZ.JointConvergence
