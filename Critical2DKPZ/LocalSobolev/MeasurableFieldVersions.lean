/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.ExpectedField
public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.Definitions.KpzRegularized
public import Critical2DKPZ.Definitions.ShfSigma
public import Critical2DKPZ.JointConvergence.LogHeatFieldMeasurability
public import Critical2DKPZ.JointConvergence.KPZRegularizedReversal
public import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Tactic

/-! # Measurable distribution versions of regularized fields -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal BoundedContinuousFunction

namespace Critical2DKPZ.LocalSobolev

set_option linter.style.haveILetI false in
private theorem locallyFinite_of_closedBall_mass (μ : Measure (Plane × Plane))
    (hμ : ∀ n : ℕ, μ (Metric.closedBall (0 : Plane × Plane) (n : ℝ)) < ∞) :
    IsLocallyFiniteMeasure μ := by
  have hfc : IsFiniteMeasureOnCompacts μ := by
    refine ⟨?_⟩
    intro K hK
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : Plane × Plane)
    obtain ⟨n, hn⟩ := exists_nat_gt r
    calc
      μ K ≤ μ (Metric.closedBall (0 : Plane × Plane) r) := measure_mono hr
      _ ≤ μ (Metric.closedBall (0 : Plane × Plane) (n : ℝ)) :=
        measure_mono (Metric.closedBall_subset_closedBall (le_of_lt hn))
      _ < ∞ := hμ n
  letI : IsFiniteMeasureOnCompacts μ := hfc
  infer_instance

set_option linter.style.haveILetI false in
private theorem measurableSet_locallyIntegrable_section
    {Ω : Type*} (m : MeasurableSpace Ω) (G : Ω × Plane → ℝ)
    (hG : Measurable[m.prod inferInstance] G) :
    MeasurableSet[m] {ω | LocallyIntegrable (fun x => G (ω, x)) volume} := by
  letI : MeasurableSpace Ω := m
  classical
  let K : ℕ → Set Plane := fun n => Metric.closedBall 0 (n : ℝ)
  have hsection (ω : Ω) : Measurable (fun x : Plane => G (ω, x)) :=
    hG.comp (measurable_const.prodMk measurable_id)
  have henergy (n : ℕ) : Measurable[m] (fun ω =>
      ∫⁻ x : Plane in K n, ‖G (ω, x)‖ₑ) := by
    let f : Ω × Plane → ℝ≥0∞ := fun q =>
      if q.2 ∈ K n then ‖G q‖ₑ else 0
    have hf : Measurable f := by
      apply Measurable.ite (measurableSet_preimage measurable_snd
        (Metric.isClosed_closedBall.measurableSet))
      · exact hG.enorm
      · exact measurable_const
    have hfull : Measurable[m] (fun ω => ∫⁻ x : Plane, f (ω, x) ∂volume) :=
      hf.lintegral_prod_right'
    have heq (ω : Ω) : (∫⁻ x : Plane in K n, ‖G (ω, x)‖ₑ) =
        ∫⁻ x : Plane, f (ω, x) ∂volume := by
      rw [← lintegral_indicator (Metric.isClosed_closedBall.measurableSet)]
      simp [f, K, Set.indicator, Metric.mem_closedBall, dist_eq_norm]
    have heqfun : (fun ω => ∫⁻ x : Plane in K n, ‖G (ω, x)‖ₑ) =
        fun ω => ∫⁻ x : Plane, f (ω, x) ∂volume := funext heq
    rw [heqfun]
    exact hfull
  have hInt (ω : Ω) (n : ℕ) :
      IntegrableOn (fun x : Plane => G (ω, x)) (K n) volume ↔
        (∫⁻ x : Plane in K n, ‖G (ω, x)‖ₑ) < ∞ := by
    rw [IntegrableOn, Integrable]
    have hsm : AEStronglyMeasurable (fun x : Plane => G (ω, x))
        (volume.restrict (K n)) := (hsection ω).aestronglyMeasurable.restrict
    simp only [hsm, true_and]
    exact hasFiniteIntegral_iff_enorm
  have hloc (ω : Ω) : LocallyIntegrable (fun x : Plane => G (ω, x)) volume ↔
      ∀ n, IntegrableOn (fun x : Plane => G (ω, x)) (K n) volume := by
    constructor
    · intro h n
      exact h.integrableOn_isCompact (isCompact_closedBall (0 : Plane) (n : ℝ))
    · intro h
      apply locallyIntegrable_iff.mpr
      intro C hC
      obtain ⟨r, hr⟩ := hC.isBounded.subset_closedBall (0 : Plane)
      obtain ⟨n, hn⟩ := exists_nat_gt r
      exact (h n).mono_set (hr.trans (Metric.closedBall_subset_closedBall
        (le_of_lt hn)))
  have hsets : ∀ n : ℕ,
      MeasurableSet[m] {ω | IntegrableOn (fun x : Plane => G (ω, x)) (K n) volume} := by
    intro n
    have hsetEq : {ω | IntegrableOn (fun x : Plane => G (ω, x)) (K n) volume} =
        {ω | (∫⁻ x : Plane in K n, ‖G (ω, x)‖ₑ) < ∞} := by
      ext ω
      exact hInt ω n
    rw [hsetEq]
    exact measurableSet_lt (henergy n) measurable_const
  have hset : MeasurableSet[m]
      (⋂ n : ℕ, {ω | IntegrableOn (fun x : Plane => G (ω, x)) (K n) volume}) :=
    MeasurableSet.iInter hsets
  convert hset using 1
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  exact hloc ω

set_option linter.style.haveILetI false in
private theorem exists_measurable_ofFun_version
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : @Measure Ω mΩ) (m : MeasurableSpace Ω)
    (X : Ω → Plane → ℝ)
    (G : Ω × Plane → ℝ) (hG : Measurable[m.prod inferInstance] G)
    (hGX : G =ᵐ[@Measure.prod Ω Plane mΩ (inferInstance : MeasurableSpace Plane)
      P (volume : Measure Plane)] (fun q => X q.1 q.2)) :
    ∃ F : Ω → Distr,
      (∀ φ : TestFn, Measurable[m] (fun ω => F ω φ)) ∧
      F =ᵐ[P] (fun ω => Distribution.ofFun ⊤ (X ω) volume ⊤) := by
  classical
  let F : Ω → Distr := fun ω => Distribution.ofFun ⊤ (fun x => G (ω, x)) volume ⊤
  have hLocMeas := measurableSet_locallyIntegrable_section m G hG
  refine ⟨F, ?_, ?_⟩
  · intro φ
    let J : Ω → ℝ := fun ω => ∫ x : Plane, φ x * G (ω, x)
    have hJ : Measurable[m] J := by
      have hprod : Measurable[m.prod inferInstance]
          (fun q : Ω × Plane => φ q.2 * G q) := by
        exact (φ.continuous.measurable.comp measurable_snd).mul hG
      letI : MeasurableSpace Ω := m
      exact hprod.stronglyMeasurable.integral_prod_right.measurable
    have hEval (ω : Ω) : F ω φ =
        if LocallyIntegrable (fun x => G (ω, x)) volume then J ω else 0 := by
      dsimp [F, J]
      rw [Distribution.ofFun_apply_eq_ite]
      simp only [smul_eq_mul]
      rw [show (↑(⊤ : TopologicalSpace.Opens Plane) : Set Plane) = Set.univ by simp,
        locallyIntegrableOn_univ]
    rw [show (fun ω => F ω φ) = fun ω =>
        if ω ∈ {ω | LocallyIntegrable (fun x => G (ω, x)) volume} then J ω else 0 by
      funext ω
      simpa only [Set.mem_ofPred_eq] using hEval ω]
    exact Measurable.ite hLocMeas hJ measurable_const
  · have hsection : ∀ᵐ ω ∂P, (fun x => G (ω, x)) =ᵐ[volume] X ω := by
      exact @Measure.ae_ae_of_ae_prod Ω Plane mΩ inferInstance P volume inferInstance
        (fun q => G q = X q.1 q.2) hGX
    filter_upwards [hsection] with ω hω
    apply Distribution.ofFun_congr_ae
    have htop : (↑(⊤ : TopologicalSpace.Opens Plane) : Set Plane) = Set.univ := by simp
    rw [htop, Measure.restrict_univ]
    exact hω

set_option linter.style.haveILetI false in
/-- A jointly measurable representative of the regularized field can be chosen as a function of
the SHF coordinates. Taking its distribution gives a testwise measurable random distribution
which agrees almost surely with the `ofFun` distribution. -/
theorem exists_shfSigma_measurable_kpzRegularized_distribution
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t δ : ℝ} (_ht : 0 < t) (hδ : 0 < δ) (hδt : δ < t)
    (h₀ : Plane →ᵇ ℝ) :
    ∃ F : Ω → Distr,
      (∀ φ : TestFn, Measurable[shfSigma Z] (fun ω => F ω φ)) ∧
      F =ᵐ[P] (fun ω => Distribution.ofFun ⊤
        (fun x => kpzRegularized P Z t δ h₀ x ω) volume ⊤) := by
  classical
  let μ : Ω → Measure (Plane × Plane) := fun ω =>
    (Z 0 (t - δ) ω).map Prod.swap
  have hcoord : Measurable (Z 0 (t - δ)) := hZ.1 0 (t - δ) le_rfl (by linarith)
  have hμ : Measurable μ :=
    (Measure.measurable_map Prod.swap measurable_swap).comp hcoord
  have hμSigma : Measurable[shfSigma Z] μ := by
    have hcoordSigma : Measurable[shfSigma Z] (Z 0 (t - δ)) := by
      apply Measurable.of_comap_le
      dsimp [shfSigma]
      exact le_iSup_of_le 0 <| le_iSup_of_le (t - δ) <|
        le_iSup_of_le ⟨le_rfl, by linarith⟩ le_rfl
    exact (Measure.measurable_map Prod.swap measurable_swap).comp hcoordSigma
  let ν : Measure (Measure (Plane × Plane)) := P.map μ
  let S : Set (Measure (Plane × Plane)) := {m | ∀ n : ℕ,
    m (Metric.closedBall (0 : Plane × Plane) (n : ℝ)) < ∞}
  have hS : MeasurableSet S := by
    simp only [S, Set.ofPred_forall]
    exact MeasurableSet.iInter fun n => measurableSet_lt
      (Measure.measurable_coe (Metric.isClosed_closedBall.measurableSet)) measurable_const
  have hsource : ∀ᵐ ω ∂P, μ ω ∈ S := by
    filter_upwards [hZ.2.1 0 (t - δ) le_rfl (by linarith)] with ω hω
    intro n
    have hpre : Prod.swap ⁻¹'
        Metric.closedBall (0 : Plane × Plane) (n : ℝ) =
          Metric.closedBall (0 : Plane × Plane) (n : ℝ) := by
      ext p
      simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm,
        Prod.swap, Prod.norm_def, sub_zero]
      rw [max_comm]
    change (Z 0 (t - δ) ω).map Prod.swap
      (Metric.closedBall (0 : Plane × Plane) (n : ℝ)) < ∞
    rw [Measure.map_apply measurable_swap
      (Metric.isClosed_closedBall.measurableSet), hpre]
    letI : IsLocallyFiniteMeasure (Z 0 (t - δ) ω) := hω.1
    exact (isCompact_closedBall (0 : Plane × Plane) (n : ℝ)).measure_lt_top
  have hmass : ∀ᵐ m ∂ν, m ∈ S :=
    (ae_map_iff hμ.aemeasurable hS).2 hsource
  have hlocalLaw : ∀ᵐ m ∂ν, IsLocallyFiniteMeasure m := by
    filter_upwards [hmass] with m hm
    exact locallyFinite_of_closedBall_mass m hm
  let g : Plane → ℝ := fun y => Real.exp (h₀ y)
  have hg : Measurable g := Real.continuous_exp.measurable.comp h₀.continuous.measurable
  have hgn : ∀ y, 0 ≤ g y := fun y => (Real.exp_pos _).le
  let c : ℝ := ∫ ω, Real.log
    (shfPairing Z 0 (t - δ) (fun _ => 1) (fun y => heatKernel δ y) ω) ∂P
  let rawMeasureField : Plane × Measure (Plane × Plane) → ℝ := fun q =>
    Real.log (∫ p, heatKernel δ (p.1 - q.1) * g p.2 ∂q.2) - c
  have hrawMeasureField : AEMeasurable rawMeasureField (volume.prod ν) := by
    have hlog := Critical2DKPZ.JointConvergence.aemeasurable_log_heatPairing_joint
      ν (fun m : Measure (Plane × Plane) => m) measurable_id hlocalLaw δ hδ g hg hgn
    exact hlog.sub_const c
  let rawMeasureFieldMeas := hrawMeasureField.mk rawMeasureField
  have hrawMeasureFieldMeas : Measurable rawMeasureFieldMeas :=
    hrawMeasureField.measurable_mk
  let Ψ : Ω × Plane → Plane × Measure (Plane × Plane) := fun q => (q.2, μ q.1)
  have hΨ : Measurable[(shfSigma Z).prod inferInstance] Ψ := by
    exact measurable_snd.prodMk (hμSigma.comp measurable_fst)
  have hΨAmbient : Measurable[(inferInstance : MeasurableSpace Ω).prod inferInstance] Ψ := by
    exact measurable_snd.prodMk (hμ.comp measurable_fst)
  have hmapAux : (P.prod volume).map (fun q : Ω × Plane => (μ q.1, q.2)) =
      ν.prod volume := by
    have hfun : (fun q : Ω × Plane => (μ q.1, q.2)) = Prod.map μ id := by
      funext q
      rfl
    rw [hfun, ← Measure.map_prod_map P volume hμ measurable_id]
    simp [ν]
  have hpush : (P.prod volume).map Ψ = volume.prod ν := by
    calc
      (P.prod volume).map Ψ = Measure.map Prod.swap
          ((P.prod volume).map (fun q : Ω × Plane => (μ q.1, q.2))) := by
            have hfun : Ψ = Prod.swap ∘ (fun q : Ω × Plane => (μ q.1, q.2)) := by
              funext q
              rfl
            rw [hfun]
            exact (Measure.map_map measurable_swap (hμ.prodMap measurable_id)).symm
      _ = Measure.map Prod.swap (ν.prod volume) := by rw [hmapAux]
      _ = volume.prod ν := Measure.prod_swap
  have hcomp : rawMeasureFieldMeas ∘ Ψ =ᵐ[P.prod volume]
      rawMeasureField ∘ Ψ := by
    have hraw : rawMeasureFieldMeas =ᵐ[volume.prod ν] rawMeasureField :=
      hrawMeasureField.ae_eq_mk.symm
    have hraw' : rawMeasureFieldMeas =ᵐ[(P.prod volume).map Ψ] rawMeasureField := by
      simpa only [hpush] using hraw
    exact ae_eq_comp hΨAmbient.aemeasurable hraw'
  have hpoint (ω : Ω) (x : Plane) :
      rawMeasureField (x, μ ω) = kpzRegularized P Z t δ h₀ x ω := by
    let Zrev : ℝ → ℝ → Ω → Measure (Plane × Plane) :=
      fun s u ω => (Z (t - u) (t - s) ω).map Prod.swap
    have hrev := Critical2DKPZ.JointConvergence.kpzRegularized_eq_kpzRegularizedReversed_of_reverseMeasure
      P Z t t δ h₀ x ω
    have hcent : c = ∫ ω', Real.log
        (shfPairing Zrev δ t (fun y => heatKernel δ y) (fun _ => 1) ω') ∂P := by
      dsimp [c]
      apply integral_congr_ae
      filter_upwards [] with ω'
      congr 1
      simpa [Zrev] using
        (Critical2DKPZ.JointConvergence.shfPairing_reverse Z t 0 (t - δ)
          (fun _ => 1) (fun y => heatKernel δ y) ω')
    have hpoint' : kpzRegularized P Z t δ h₀ x ω =
        Real.log (∫ p, heatKernel δ (p.1 - x) * g p.2 ∂μ ω) - c := by
      rw [hrev]
      simp [kpzRegularizedReversed, Zrev, μ, c, g, shfPairing, hcent]
    simpa [rawMeasureField] using hpoint'.symm
  let G : Ω × Plane → ℝ := rawMeasureFieldMeas ∘ Ψ
  have hG : Measurable[(shfSigma Z).prod inferInstance] G :=
    hrawMeasureFieldMeas.comp hΨ
  have hGX : G =ᵐ[P.prod volume]
      (fun q => kpzRegularized P Z t δ h₀ q.2 q.1) := by
    filter_upwards [hcomp] with q hq
    exact hq.trans (hpoint q.1 q.2)
  exact exists_measurable_ofFun_version P (shfSigma Z)
    (fun ω x => kpzRegularized P Z t δ h₀ x ω) G hG hGX

end Critical2DKPZ.LocalSobolev

end
