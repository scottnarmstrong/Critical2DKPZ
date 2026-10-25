/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.EndpointMeans
public import Critical2DKPZ.NonGaussian.Basic
public import Critical2DKPZ.JointConvergence.HeatStartLogFieldConvergence
public import Critical2DKPZ.SHF.Positivity.BoundedPairingConvergence
public import Critical2DKPZ.JointConvergence.ThmToyJointConvergence
public import Critical2DKPZ.JointConvergence.KPZRegularizedReversal
public import Critical2DKPZ.JointConvergence.LogHeatFieldMeasurability
public import Critical2DKPZ.CovarianceKernel.RegularizedSpecification
import Mathlib.Tactic

/-! # Flat-terminal logarithmic field limits -/

@[expose] public section

open MeasureTheory Filter
open Critical2DKPZ.JointConvergence Critical2DKPZ.SHF.Positivity
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.LocalSobolev
open scoped BoundedContinuousFunction ENNReal Topology

namespace Critical2DKPZ.NonGaussian

universe u

private theorem aemeasurable_integral_kpzRegularized_endpoint
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (s δ : ℝ) (hsδ : δ < s) (hδ : 0 < δ) (h₀ : Plane →ᵇ ℝ) (φ : TestFn) :
    AEMeasurable (fun ω => ∫ x, φ x * kpzRegularized P Z s δ h₀ x ω) P := by
  let Zrev : ℝ → ℝ → Ω → Measure (Plane × Plane) :=
    fun a b ω => (Z (s - b) (s - a) ω).map Prod.swap
  let μ : Ω → Measure (Plane × Plane) := fun ω => (Z 0 (s - δ) ω).map Prod.swap
  have hμ : Measurable μ := by
    exact (Measure.measurable_map Prod.swap measurable_swap).comp
      (hZ.1 0 (s - δ) le_rfl (by linarith))
  have hlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
    filter_upwards [(hZ.2.1 0 (s - δ) le_rfl (by linarith)).mono
      (fun ω hω => hω.1)] with ω hω
    exact Critical2DKPZ.CovarianceKernel.locallyFinite_map_homeomorph
      (Homeomorph.prodComm Plane Plane) (Z 0 (s - δ) ω) hω
  let c : ℝ := ∫ ω', Real.log
    (shfPairing Zrev δ s (fun y => heatKernel δ y) (fun _ => 1) ω') ∂P
  let g : Plane → ℝ := fun y => Real.exp (h₀ y)
  have hg : Measurable g := Real.continuous_exp.measurable.comp h₀.continuous.measurable
  have hgn : ∀ y, 0 ≤ g y := fun y => (Real.exp_pos _).le
  have hameas := aemeasurable_integral_log_heatPairing P μ hμ hlocal δ c hδ
    g (φ : Plane → ℝ) hg hgn φ.continuous.measurable
  have hpoint (ω : Ω) (x : Plane) : kpzRegularized P Z s δ h₀ x ω =
      Real.log (∫ p, heatKernel δ (p.1 - x) * g p.2 ∂μ ω) - c := by
    have hrev := kpzRegularized_eq_kpzRegularizedReversed_of_reverseMeasure
      P Z s s δ h₀ x ω
    rw [hrev]
    simp [kpzRegularizedReversed, Zrev, μ, c, g, shfPairing]
  have hEq : (fun ω => ∫ x, φ x * kpzRegularized P Z s δ h₀ x ω) =
      fun ω => ∫ x, φ x *
        (Real.log (∫ p, heatKernel δ (p.1 - x) * g p.2 ∂μ ω) - c) := by
    funext ω
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change φ x * kpzRegularized P Z s δ h₀ x ω = _
      rw [hpoint ω x]
  rw [hEq]
  exact hameas

private theorem avgLogField_one_memLp_and_mean_zero (ϑ : ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hHeatStartLogInput : HeatStartLogAt ϑ P Z)
    {r t : ℝ} (hr : 0 < r) (hrt : r < t) (ψ : TestFn) :
    MemLp (avgLogField P Z r t ψ (fun _ => 1)) 2 P ∧
      (∫ ω, avgLogField P Z r t ψ (fun _ => 1) ω ∂P) = 0 := by
  let one : Plane →ᵇ ℝ := 1
  let G : Plane × Ω → ℝ := fun q => Real.log
    (shfPairing Z r t (fun y => heatKernel r (y - q.1)) (fun _ => (1 : ℝ)) q.2)
  have hlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Z r t ω) := by
    filter_upwards [(hZ.2.1 r t hr.le hrt).mono (fun ω hω => hω.1)] with ω hω
    exact hω
  have hG : AEMeasurable G (volume.prod P) := by
    exact aemeasurable_log_heatPairing_joint P (Z r t) (hZ.1 r t hr.le hrt)
      hlocal r hr one (by fun_prop) (by intro y; norm_num)
  have hsec (x : Plane) : AEStronglyMeasurable (fun ω => G (x, ω)) P := by
    have h := (hsym.2.2.2.2.2.2 r t r x (0 : Plane →ᵇ ℝ) hr.le hrt hr)
    simpa [G, one] using h.2.1.aestronglyMeasurable
  have hpair : ∀ {s t δ : ℝ}, 0 ≤ s → s < t → 0 < δ → ∀ (x : Plane)
      (g : Plane →ᵇ ℝ),
      (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane =>
        heatKernel δ (p.1 - x) * g p.2) (Z s t ω)) ∧
      Integrable (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) P ∧
      (∫ ω, |shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω| ∂P ≤ ‖g‖) ∧
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) =>
          ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(polymerMeasure ϑ N s t ω))
        atTop (shfPairing Z s t (fun y => heatKernel δ (y - x)) g)
        (fun _ => disorderLaw) P := by
    intro s t δ hs hst hδ x g
    exact isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hs hst hδ x g
  have hjoint := isCriticalSHF_heat_bounded_pairing_joint ϑ P Z hZ
  have hpos : ∀ (s t δ : ℝ) (x : Plane) (h₀ : Plane →ᵇ ℝ),
      0 ≤ s → s < t → 0 < δ →
      (∀ᵐ ω ∂P, 0 < shfPairing Z s t (fun y => heatKernel δ (y - x))
        (fun y => Real.exp (h₀ y)) ω) ∧
      AEMeasurable (fun ω => Real.log (shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)) P := by
    intro s t δ x h₀ hs hst hδ
    rcases hsym.2.2.2.2.2.2 s t δ x h₀ hs hst hδ with ⟨hpos, hmeas, _⟩
    exact ⟨hpos, hmeas⟩
  obtain ⟨M, hM, hSq⟩ := shf_heatStartLogField_square_bound
    ϑ P Z hZ hpair hjoint hpos t (0 : Plane →ᵇ ℝ) (s := r) (δ := r) hr.le hrt hr
  have hSqG : ∀ x : Plane, Integrable (fun ω => |G (x, ω)| ^ 2) P ∧
      ∫ ω, |G (x, ω)| ^ 2 ∂P ≤ M := by
    intro x
    simpa [G, Real.exp_zero] using hSq x
  let m₀ : ℝ := ∫ ω, G (0, ω) ∂P
  have hmem := memLp_centered_integral_test_of_uniform_square P hG hsec hM hSqG ψ
  have hcenter (x : Plane) : ∫ ω, G (x, ω) ∂P = m₀ := by
    dsimp [m₀, G]
    simpa [sub_zero] using
      (integral_log_heatPairing_eq_of_heatStartLogAt ϑ P Z hHeatStartLogInput hr.le hrt hr x)
  have hcenterEq (ω : Ω) : avgLogField P Z r t ψ (fun _ => 1) ω =
      ∫ x, ψ x * (G (x, ω) - m₀) := by
    unfold avgLogField
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change ψ x * (G (x, ω) - ∫ ω', G (x, ω') ∂P) =
        ψ x * (G (x, ω) - m₀)
      rw [hcenter x]
  have hmemAvg : MemLp (avgLogField P Z r t ψ (fun _ => 1)) 2 P := by
    have hfun : avgLogField P Z r t ψ (fun _ => 1) =
        fun ω => ∫ x, ψ x * (G (x, ω) - m₀) := funext hcenterEq
    rw [hfun]
    exact hmem
  have hprod := integrable_test_mul_joint P hG hsec hM hSqG ψ
  have hψInt : Integrable (fun x : Plane => ψ x) volume := by
    exact (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport)
  have hconst : Integrable (fun q : Plane × Ω => ψ q.1 * m₀) (volume.prod P) := by
    have hsm : AEStronglyMeasurable (fun q : Plane × Ω => ψ q.1 * m₀)
        (volume.prod P) := by fun_prop
    apply (integrable_prod_iff hsm).2
    constructor
    · exact Filter.Eventually.of_forall fun x => by
        simpa using (integrable_const (ψ x * m₀) : Integrable (fun _ : Ω => ψ x * m₀) P)
    · simpa [mul_comm] using hψInt.norm.const_mul |m₀|
  let F : Plane × Ω → ℝ := fun q => ψ q.1 * (G q - m₀)
  have hFint : Integrable F (volume.prod P) := by
    have hEq : F = (fun q : Plane × Ω => ψ q.1 * G q) -
        (fun q : Plane × Ω => ψ q.1 * m₀) := by
      funext q
      dsimp [F]
      ring
    rw [hEq]
    exact hprod.sub hconst
  have hpoint (x : Plane) : ∫ ω, F (x, ω) ∂P = 0 := by
    have hGmem : MemLp (fun ω => G (x, ω)) 2 P := by
      apply (memLp_two_iff_integrable_sq (hsec x)).2
      simpa [sq_abs] using (hSqG x).1
    have hGint : Integrable (fun ω => G (x, ω)) P := hGmem.integrable (by norm_num)
    simp only [F]
    rw [show (fun ω => ψ x * (G (x, ω) - m₀)) =
      fun ω => ψ x * G (x, ω) - ψ x * m₀ by funext ω; ring]
    rw [integral_sub (hGint.const_mul (ψ x)) (integrable_const (ψ x * m₀)),
      integral_const_mul, integral_const, hcenter x]
    simp [m₀]
  have hmean : (∫ ω, avgLogField P Z r t ψ (fun _ => 1) ω ∂P) = 0 := by
    calc
      (∫ ω, avgLogField P Z r t ψ (fun _ => 1) ω ∂P) =
          ∫ ω, ∫ x, F (x, ω) ∂volume ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall hcenterEq)
      _ = ∫ x, ∫ ω, F (x, ω) ∂P ∂volume := integral_integral_swap hFint.swap
      _ = 0 := by simp_rw [hpoint]; simp
  exact ⟨hmemAvg, hmean⟩

/-- The centered flat-terminal logarithmic averages converge in L² to a centered variable
with the law of the flat-initial KPZ test pairing. -/
theorem avgLogField_one_tendsto_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hC12 : ToyJointAt ϑ P Z)
    (hHeatStartLogInput : HeatStartLogAt ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {t : ℝ} (ht : 0 < t) (ψ : TestFn) :
    ∃ X : Ω → ℝ, P.map X = P.map (fun ω => H t 0 ω ψ) ∧ MemLp X 2 P ∧
      (∫ ω, X ω ∂P) = 0 ∧
      Tendsto (fun r => eLpNorm
        (fun ω => avgLogField P Z r t ψ (fun _ => 1) ω - X ω) 2 P)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  obtain ⟨Xfam, hXm, hRate, hLp, hDist, hLaw⟩ := hC12 t ht
  let X : Ω → ℝ := Xfam 0 0 ψ
  have hL2 : Tendsto (fun r => eLpNorm
      (fun ω => (∫ x, ψ x * kpzRegularizedReversed P Z 0 t r 0 x ω) - X ω) 2 P)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) :=
    hLp 0 0 ψ 2 (by norm_num) ht (by norm_num) (by norm_num)
  have hEq (r : ℝ) (hr : 0 < r) (hrt : r < t) (ω : Ω) :
      avgLogField P Z r t ψ (fun _ => 1) ω =
        ∫ x, ψ x * kpzRegularizedReversed P Z 0 t r 0 x ω := by
    unfold avgLogField kpzRegularizedReversed
    simp only [zero_add, BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    have hmean := integral_log_heatPairing_eq_of_heatStartLogAt ϑ P Z hHeatStartLogInput
      hr.le hrt hr x
    have hmean' : (∫ ω', Real.log (shfPairing Z r t
        (fun y => heatKernel r (y - x)) (fun _ => (1 : ℝ)) ω') ∂P) =
        ∫ ω', Real.log (shfPairing Z r t (fun y => heatKernel r y)
          (fun _ => (1 : ℝ)) ω') ∂P := by simpa [sub_zero] using hmean
    change ψ x * (Real.log (shfPairing Z r t
      (fun y => heatKernel r (y - x)) (fun _ => (1 : ℝ)) ω) -
        ∫ ω', Real.log (shfPairing Z r t
          (fun y => heatKernel r (y - x)) (fun _ => (1 : ℝ)) ω') ∂P) =
      ψ x * (Real.log (shfPairing Z r t
        (fun y => heatKernel r (y - x)) (fun _ => (1 : ℝ)) ω) -
          ∫ ω', Real.log (shfPairing Z r t (fun y => heatKernel r y)
            (fun _ => (1 : ℝ)) ω') ∂P)
    rw [hmean']
  have hConv : Tendsto (fun r => eLpNorm
      (fun ω => avgLogField P Z r t ψ (fun _ => 1) ω - X ω) 2 P)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    apply hL2.congr'
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds ht)] with r hr hrt
    apply eLpNorm_congr_ae
    exact Filter.Eventually.of_forall fun ω =>
      congrArg (fun z : ℝ => z - X ω) (hEq r hr hrt ω).symm
  have hLawX : P.map X = P.map (fun ω => H t 0 ω ψ) := by
    have h := hLaw H hH 1 (fun _ => 0) (fun _ => 0) (fun _ => ψ)
      (by intro i; exact ⟨by norm_num, ht⟩)
    have hF : Measurable (fun ω : Ω => fun _ : Fin 1 => X ω) := by
      have hSigmaLe : shfSigma Z ≤ (inferInstance : MeasurableSpace Ω) := by
        dsimp [shfSigma]
        apply iSup_le
        intro s
        apply iSup_le
        intro u
        apply iSup_le
        intro hsu
        exact (hZ.1 s u hsu.1 hsu.2).comap_le
      have hXmeas : Measurable (Xfam 0 0 ψ) := by
        have hXmeasSub : Measurable[shfSigma Z] (Xfam 0 0 ψ) :=
          hXm 0 0 ψ (by norm_num) ht
        intro s hs
        exact hSigmaLe _ (hXmeasSub hs)
      exact measurable_pi_iff.mpr fun i => by simpa [X] using hXmeas
    have hY : AEMeasurable (fun ω : Ω => fun _ : Fin 1 => H t 0 ω ψ) P := by
      apply aemeasurable_pi_iff.mpr
      intro i
      let δseq : ℕ → ℝ := fun n => t / ((n : ℝ) + 2)
      have hδseqpos (n : ℕ) : 0 < δseq n := by
        dsimp [δseq]
        positivity
      have hδseqLt (n : ℕ) : δseq n < t := by
        dsimp [δseq]
        exact div_lt_self ht (by linarith : (1 : ℝ) < (n : ℝ) + 2)
      have hδtend : Tendsto δseq atTop (nhdsWithin 0 (Set.Ioi 0)) := by
        have hzero : Tendsto δseq atTop (𝓝 0) := by
          have hden : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) := by
            have hnatCast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
              tendsto_natCast_atTop_atTop
            have hnat : Tendsto (fun n : ℕ => (2 : ℝ) + (n : ℝ)) atTop atTop := by
              apply tendsto_atTop_mono (fun n => ?_) hnatCast
              linarith
            have hnat' : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
              simpa [add_comm] using hnat
            exact tendsto_inv_atTop_zero.comp hnat'
          simpa [δseq, div_eq_mul_inv] using hden.const_mul t
        exact tendsto_nhdsWithin_iff.mpr ⟨hzero,
          Filter.Eventually.of_forall hδseqpos⟩
      have hlim : TendstoInMeasure P
          (fun n ω => ∫ x, ψ x * kpzRegularized P Z t (δseq n) 0 x ω)
          atTop (fun ω => H t 0 ω ψ) := by
        exact (hH t ht 0 ψ).comp hδtend
      have hmeas (n : ℕ) : AEMeasurable
          (fun ω => ∫ x, ψ x * kpzRegularized P Z t (δseq n) 0 x ω) P :=
        aemeasurable_integral_kpzRegularized_endpoint ϑ P Z hZ t (δseq n)
          (hδseqLt n) (hδseqpos n) 0 ψ
      have hHscalar : AEMeasurable (fun ω => H t 0 ω ψ) P :=
        TendstoInMeasure.aemeasurable hmeas hlim
      simpa using hHscalar
    have hcoord : AEMeasurable (fun v : Fin 1 → ℝ => v 0)
        ((P.map (fun ω i => Xfam 0 0 ψ ω))) :=
      (measurable_pi_apply (0 : Fin 1)).aemeasurable
    have hcoord' : AEMeasurable (fun v : Fin 1 → ℝ => v 0)
        ((P.map (fun ω i => H t 0 ω ψ))) :=
      (measurable_pi_apply (0 : Fin 1)).aemeasurable
    have hcoordLaw := congrArg (fun ν : Measure (Fin 1 → ℝ) =>
      ν.map (fun v => v 0)) h
    simp only [sub_zero] at hcoordLaw
    rw [AEMeasurable.map_map_of_aemeasurable hcoord hF.aemeasurable,
      AEMeasurable.map_map_of_aemeasurable hcoord' hY] at hcoordLaw
    simpa [Function.comp_def, X] using hcoordLaw
  have hMemX : MemLp X 2 P := by
    have hsmall : ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0),
        eLpNorm (fun ω => avgLogField P Z r t ψ (fun _ => 1) ω - X ω) 2 P < 1 :=
      hConv.eventually (Iio_mem_nhds (by norm_num))
    have hrpos : ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < r := self_mem_nhdsWithin
    have hrt : ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0), r < t :=
      nhdsWithin_le_nhds (Iio_mem_nhds ht)
    obtain ⟨r, hsmallr, hr, hrt⟩ := (hsmall.and (hrpos.and hrt)).exists
    have hmemR := (avgLogField_one_memLp_and_mean_zero ϑ P Z hZ hsym hHeatStartLogInput hr hrt ψ).1
    have hmemDiff : MemLp
        (fun ω => avgLogField P Z r t ψ (fun _ => 1) ω - X ω) 2 P := by
      rw [memLp_iff]
      exact lt_trans hsmallr (by norm_num)
    have h := hmemR.sub hmemDiff
    have heq : (fun ω => (avgLogField P Z r t ψ (fun _ => 1) ω -
        (avgLogField P Z r t ψ (fun _ => 1) ω - X ω))) = X := by
      funext ω
      ring
    have h' : MemLp (fun ω => avgLogField P Z r t ψ (fun _ => 1) ω -
        (avgLogField P Z r t ψ (fun _ => 1) ω - X ω)) 2 P := by
      exact h
    rw [heq] at h'
    exact h'
  have hmeanX : (∫ ω, X ω ∂P) = 0 := by
    have hconst : Tendsto (fun _ : ℝ => ENNReal.ofReal |∫ ω, X ω ∂P|)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hConv
        (Filter.Eventually.of_forall fun _ => bot_le) ?_
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds ht)] with r hr hrt
      have hmemR := (avgLogField_one_memLp_and_mean_zero ϑ P Z hZ hsym hHeatStartLogInput hr hrt ψ).1
      have hmeanR := (avgLogField_one_memLp_and_mean_zero ϑ P Z hZ hsym hHeatStartLogInput hr hrt ψ).2
      let D : Ω → ℝ := fun ω => avgLogField P Z r t ψ (fun _ => 1) ω - X ω
      have hmemD : MemLp D 2 P := hmemR.sub hMemX
      have hDint : Integrable D P := hmemD.integrable (by norm_num)
      have hmeanD : (∫ ω, D ω ∂P) = -(∫ ω, X ω ∂P) := by
        dsimp [D]
        rw [integral_sub (hmemR.integrable (by norm_num))
          (hMemX.integrable (by norm_num)), hmeanR]
        simp
      have hL1 : eLpNorm D 1 P ≤ eLpNorm D 2 P := by
        have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
          (by norm_num : (1 : ℝ≥0∞) ≤ 2) hmemD.aestronglyMeasurable
        simpa using h
      have hL1top : eLpNorm D 1 P ≠ ⊤ :=
        ne_of_lt (lt_of_le_of_lt hL1 hmemD.eLpNorm_lt_top)
      have hnorm : |∫ ω, D ω ∂P| ≤ (eLpNorm D 1 P).toReal := by
        have h := (enorm_integral_le_lintegral_enorm (μ := P) D)
        rw [← eLpNorm_one_eq_lintegral_enorm hDint.aestronglyMeasurable] at h
        have hreal := ENNReal.toReal_mono hL1top h
        simpa [Real.norm_eq_abs] using hreal
      have hAbs : |∫ ω, D ω ∂P| = |∫ ω, X ω ∂P| := by
        rw [hmeanD]
        simp
      have h1 : (ENNReal.ofReal |∫ ω, X ω ∂P|) ≤ eLpNorm D 1 P := by
        calc
          ENNReal.ofReal |∫ ω, X ω ∂P| = ENNReal.ofReal |∫ ω, D ω ∂P| := by
            rw [hAbs]
          _ ≤ ENNReal.ofReal ((eLpNorm D 1 P).toReal) :=
            ENNReal.ofReal_le_ofReal hnorm
          _ = eLpNorm D 1 P := ENNReal.ofReal_toReal hL1top
      have hbound : ENNReal.ofReal |∫ ω, X ω ∂P| ≤ eLpNorm D 2 P :=
        h1.trans hL1
      simpa [D] using hbound
    have hzero := tendsto_nhds_unique hconst tendsto_const_nhds
    have habs : |∫ ω, X ω ∂P| = 0 := by
      exact le_antisymm (ENNReal.ofReal_eq_zero.mp hzero.symm) (abs_nonneg _)
    exact abs_eq_zero.mp habs
  refine ⟨X, hLawX, hMemX, hmeanX, hConv⟩

end Critical2DKPZ.NonGaussian

end
