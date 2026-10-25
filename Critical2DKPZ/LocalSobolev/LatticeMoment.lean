/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.LatticeCovarianceBounds
public import Critical2DKPZ.Analysis.Sobolev.LocalizedMoment
public import Critical2DKPZ.Analysis.Sobolev.FunctionBound
public import Critical2DKPZ.FutureProfiles.EndpointTranslation
public import Critical2DKPZ.CovarianceKernel.Envelope
import Critical2DKPZ.SHF.Limit.LocalFinite
import Critical2DKPZ.SHF.Tsai.Tech
import Mathlib.Tactic

/-! # Local negative Sobolev moments of the lattice field -/

public section

noncomputable section

open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal BoundedContinuousFunction

namespace Critical2DKPZ.LocalSobolev

private theorem kpzLattice_flat_translate (ϑ : ℝ) {N : ℕ} (hN : 0 < N)
    {t : ℝ} (hnt : 1 ≤ evenCeil ((N : ℝ) * t))
    (x : Plane) (ω : Disorder) :
    kpzLattice ϑ N t 0 x ω =
      kpzLattice ϑ N t 0 0 (fun p => ω (p.1, p.2 + latticePoint N x)) := by
  let m := evenCeil ((N : ℝ) * t)
  let z := latticePoint N x
  let β := criticalBeta ϑ N
  let τ : Disorder → Disorder := fun ω p => ω (p.1, p.2 + z)
  have hcomm (ω : Disorder) :
      PolymerCalculus.reversedDisorder m (τ ω) = τ (PolymerCalculus.reversedDisorder m ω) := by
    funext p
    rfl
  have hptp :
      pointToPlane β 0 (m - 1) z (PolymerCalculus.reversedDisorder m ω) =
        pointToPlane β 0 (m - 1) 0
          (PolymerCalculus.reversedDisorder m (τ ω)) := by
    rw [hcomm]
    simpa [z] using Polymer.pointToPlane_translate β 0 (m - 1) 0 z
      (PolymerCalculus.reversedDisorder m ω)
  have hcoord : (τ ω) (m, 0) = ω (m, z) := by
    simp [τ, z]
  rw [kpzLattice_flat_log_eq_timeReversedPlane ϑ hN t x ω (by simpa [m] using hnt),
    kpzLattice_flat_log_eq_timeReversedPlane ϑ hN t 0 (τ ω) (by simpa [m] using hnt)]
  have hsite0 : latticePoint N (0 : Plane) = 0 := by
    simp [latticePoint, nearestEven]
  rw [hptp, hsite0, ← hcoord]

private theorem memLp_kpzLattice_flat (ϑ : ℝ) {N : ℕ} (hN : 0 < N)
    {t : ℝ} (hnt : 1 ≤ evenCeil ((N : ℝ) * t))
    (x : Plane) : MemLp (fun ω => kpzLattice ϑ N t 0 x ω) 2 disorderLaw := by
  let m := evenCeil ((N : ℝ) * t)
  let z := latticePoint N x
  let β := criticalBeta ϑ N
  let rev := PolymerCalculus.reversedDisorder m
  let F : Disorder → ℝ := fun ω => Real.log (pointToPlane β 0 (m - 1) z (rev ω))
  let D : Disorder → ℝ := fun ω => β * ω (m, z)
  let c : ℝ := β ^ 2 / 2 + kpzLatticeCentring ϑ N t
  have hF : MemLp F 2 disorderLaw := by
    dsimp [F, rev, β, z, m]
    exact (memLp_log_pointToPlane _ _ _ _).comp_measurePreserving
      (PolymerCalculus.measurePreserving_reversedDisorder _)
  have hcoord := Gaussian.hasLaw_disorder_eval (m, z)
  have hcoordMem : MemLp (fun ω : Disorder => ω (m, z)) 2 disorderLaw :=
    hcoord.memLp (memLp_id_gaussianReal 2)
  have hD : MemLp D 2 disorderLaw := by
    dsimp [D]
    simpa only [mul_comm] using hcoordMem.const_mul β
  have hc : MemLp (fun _ : Disorder => c) 2 disorderLaw := memLp_const c
  have hrepr : (fun ω => kpzLattice ϑ N t 0 x ω) = fun ω => F ω + D ω - c := by
    funext ω
    dsimp [F, D, c, β, z, m, rev]
    rw [kpzLattice_flat_log_eq_timeReversedPlane ϑ hN t x ω (by simpa [m] using hnt)]
    ring
  rw [hrepr]
  exact (hF.add hD).sub hc

private theorem integral_kpzLattice_flat_zero (ϑ : ℝ) {N : ℕ} (hN : 0 < N)
    {t : ℝ} (hnt : 1 ≤ evenCeil ((N : ℝ) * t)) :
    (∫ ω, kpzLattice ϑ N t 0 0 ω ∂disorderLaw) = 0 := by
  let M : Disorder → ℝ := fun ω =>
    Real.log (∫ y, rescaledP2P ϑ N 0 t (y, 0) ω)
  let c := kpzLatticeCentring ϑ N t
  have hmem := memLp_kpzLattice_flat ϑ hN hnt (0 : Plane)
  have hdecomp (ω : Disorder) : kpzLattice ϑ N t 0 0 ω = M ω - c := by
    dsimp [M, c, kpzLattice]
    simp only [Real.exp_zero, one_mul]
  have hlogEq : M = fun ω => kpzLattice ϑ N t 0 0 ω + c := by
    funext ω
    rw [hdecomp ω]
    ring
  have hMmem : MemLp M 2 disorderLaw := by
    rw [hlogEq]
    exact hmem.add (memLp_const c)
  have hMInt := hMmem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hcInt : Integrable (fun _ : Disorder => c) disorderLaw := integrable_const _
  calc
    _ = ∫ ω, M ω - c ∂disorderLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => hdecomp ω
    _ = (∫ ω, M ω ∂disorderLaw) - ∫ ω, c ∂disorderLaw := integral_sub hMInt hcInt
    _ = 0 := by simp [M, c, kpzLatticeCentring]

private theorem integral_kpzLattice_flat_zero_at (ϑ : ℝ) {N : ℕ}
    (hN : 0 < N) {t : ℝ} (hnt : 1 ≤ evenCeil ((N : ℝ) * t))
    (x : Plane) :
    (∫ ω, kpzLattice ϑ N t 0 x ω ∂disorderLaw) = 0 := by
  let τ : Disorder → Disorder := fun ω p => ω (p.1, p.2 + latticePoint N x)
  have hmp : MeasurePreserving τ disorderLaw disorderLaw :=
    Gaussian.measurePreserving_disorder_translation (latticePoint N x)
  calc
    _ = ∫ ω, kpzLattice ϑ N t 0 0 (τ ω) ∂disorderLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω =>
        kpzLattice_flat_translate ϑ hN hnt x ω
    _ = ∫ ω, kpzLattice ϑ N t 0 0 ω ∂disorderLaw := by
      calc
        _ = ∫ ω, kpzLattice ϑ N t 0 0 ω ∂Measure.map τ disorderLaw := by
          apply (integral_map hmp.measurable.aemeasurable ?_).symm
          rw [hmp.map_eq]
          exact (memLp_kpzLattice_flat ϑ hN hnt (0 : Plane)).aestronglyMeasurable
        _ = _ := by rw [hmp.map_eq]
    _ = 0 := integral_kpzLattice_flat_zero ϑ hN hnt

private theorem integral_kpzLattice_flat_sq_eq_zeroSite (ϑ : ℝ) {N : ℕ}
    (hN : 0 < N) {t : ℝ} (hnt : 1 ≤ evenCeil ((N : ℝ) * t))
    (x : Plane) :
    (∫ ω, kpzLattice ϑ N t 0 x ω ^ 2 ∂disorderLaw) =
      ∫ ω, kpzLattice ϑ N t 0 0 ω ^ 2 ∂disorderLaw := by
  let τ : Disorder → Disorder := fun ω p => ω (p.1, p.2 + latticePoint N x)
  have htranslate (ω : Disorder) :
      kpzLattice ϑ N t 0 x ω = kpzLattice ϑ N t 0 0 (τ ω) := by
    simpa only [τ] using kpzLattice_flat_translate ϑ hN hnt x ω
  have hmp : MeasurePreserving τ disorderLaw disorderLaw :=
    Gaussian.measurePreserving_disorder_translation (latticePoint N x)
  calc
    _ = ∫ ω, kpzLattice ϑ N t 0 0 (τ ω) ^ 2 ∂disorderLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω =>
        congrArg (fun v : ℝ => v ^ 2) (htranslate ω)
    _ = _ := by
      calc
        _ = ∫ ω, kpzLattice ϑ N t 0 0 ω ^ 2 ∂Measure.map τ disorderLaw := by
          apply (integral_map (f := fun ω : Disorder => kpzLattice ϑ N t 0 0 ω ^ 2)
            hmp.measurable.aemeasurable ?_).symm
          rw [hmp.map_eq]
          exact (memLp_kpzLattice_flat ϑ hN hnt (0 : Plane)).aestronglyMeasurable.pow 2
        _ = _ := by rw [hmp.map_eq]

private theorem kpzLattice_flat_uniform_secondMoment (ϑ : ℝ) {N : ℕ}
    (hN : 0 < N) {t : ℝ} (hnt : 1 ≤ evenCeil ((N : ℝ) * t)) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x : Plane,
      (∫⁻ ω, ENNReal.ofReal (kpzLattice ϑ N t 0 x ω ^ 2) ∂disorderLaw) ≤ C := by
  let C : ℝ≥0∞ := ENNReal.ofReal
    (∫ ω, kpzLattice ϑ N t 0 0 ω ^ 2 ∂disorderLaw)
  have hmem := memLp_kpzLattice_flat ϑ hN hnt (0 : Plane)
  have hsquare : Integrable (fun ω => kpzLattice ϑ N t 0 0 ω ^ 2) disorderLaw :=
    hmem.integrable_sq
  have hCeq : C = ∫⁻ ω, ENNReal.ofReal (kpzLattice ϑ N t 0 0 ω ^ 2) ∂disorderLaw := by
    dsimp [C]
    exact ofReal_integral_eq_lintegral_ofReal hsquare
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    exact ENNReal.ofReal_lt_top
  · intro x
    have hmemx := memLp_kpzLattice_flat ϑ hN hnt x
    have hsquarex : Integrable (fun ω => kpzLattice ϑ N t 0 x ω ^ 2) disorderLaw :=
      hmemx.integrable_sq
    have hconvx := ofReal_integral_eq_lintegral_ofReal hsquarex
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)
    calc
      _ = ENNReal.ofReal (∫ ω, kpzLattice ϑ N t 0 x ω ^ 2 ∂disorderLaw) := hconvx.symm
      _ = C := by rw [integral_kpzLattice_flat_sq_eq_zeroSite ϑ hN hnt x]
      _ ≤ C := le_rfl

private theorem memLp_kpzLattice_flat_joint (ϑ : ℝ) {N : ℕ} (hN : 0 < N)
    {t : ℝ} :
    Measurable (fun p : Disorder × Plane => kpzLattice ϑ N t 0 p.2 p.1) := by
  let m := evenCeil ((N : ℝ) * t)
  let β := criticalBeta ϑ N
  let w : Site → (Fin m → Fin 4) → Site := fun x s => flatMassPathStart x s
  have hmass (ω : Disorder) (x : Plane) :
      (∫ y, rescaledP2P ϑ N 0 t (y, x) ω) =
        PolymerCalculus.finitePathMass β 0 m (w (latticePoint N x))
          flatMassPathCoeff ω := by
    exact integral_rescaledP2P_flat_eq_finitePathMass ϑ hN t x ω
      (evenCeil_even ((N : ℝ) * t))
  have hsite : Measurable (fun q : Site × Disorder =>
      Real.log (PolymerCalculus.finitePathMass β 0 m (w q.1)
        flatMassPathCoeff q.2)) := by
    apply measurable_from_prod_countable_right
    intro z
    exact PolymerCalculus.measurable_log_finitePathMass β 0 m (w z)
      flatMassPathCoeff
  have hmap : Measurable (fun p : Disorder × Plane => (latticePoint N p.2, p.1)) :=
    ((measurable_latticePoint N).comp measurable_snd).prodMk measurable_fst
  have hmassMeas : Measurable (fun p : Disorder × Plane =>
      Real.log (∫ y, rescaledP2P ϑ N 0 t (y, p.2) p.1)) := by
    have heq : (fun p : Disorder × Plane =>
        Real.log (∫ y, rescaledP2P ϑ N 0 t (y, p.2) p.1)) =
        (fun q : Site × Disorder =>
          Real.log (PolymerCalculus.finitePathMass β 0 m (w q.1)
            flatMassPathCoeff q.2)) ∘ (fun p : Disorder × Plane =>
              (latticePoint N p.2, p.1)) := by
      funext p
      rw [hmass p.1 p.2]
      rfl
    rw [heq]
    exact hsite.comp hmap
  have hrepr : (fun p : Disorder × Plane => kpzLattice ϑ N t 0 p.2 p.1) =
      fun p => Real.log (∫ y, rescaledP2P ϑ N 0 t (y, p.2) p.1) -
        kpzLatticeCentring ϑ N t := by
    funext p
    simp [kpzLattice]
  rw [hrepr]
  exact hmassMeas.sub_const _

private theorem locallyIntegrable_kpzLattice (ϑ : ℝ) (N : ℕ) (t : ℝ)
    (h₀ : Plane →ᵇ ℝ) (ω : Disorder) :
    LocallyIntegrable (fun x => kpzLattice ϑ N t h₀ x ω) volume := by
  classical
  let g : Site → ℝ := fun z =>
    Real.log (∫ y : Plane, Real.exp (h₀ y) *
      ((N / 4 : ℝ) * pointToPoint (criticalBeta ϑ N) 0
        (evenCeil ((N : ℝ) * t)) (latticePoint N y) z ω)) -
      kpzLatticeCentring ϑ N t
  have hmeasg : Measurable g := measurable_of_countable g
  have hfactor : (fun x : Plane => kpzLattice ϑ N t h₀ x ω) = g ∘ latticePoint N := by
    funext x
    simp [g, kpzLattice, rescaledP2P]
  have hmeas : Measurable (fun x : Plane => kpzLattice ϑ N t h₀ x ω) := by
    rw [hfactor]
    exact hmeasg.comp (measurable_latticePoint N)
  rw [locallyIntegrable_iff]
  intro K hK
  have hfinite := Critical2DKPZ.SHF.Limit.finite_latticePoint_image_of_bounded
    (N := N) hK.isBounded
  let values : Set ℝ := g '' (latticePoint N '' K)
  have hvfinite : values.Finite := hfinite.image g
  obtain ⟨M, hM⟩ := hvfinite.bddAbove
  obtain ⟨m, hm⟩ := hvfinite.bddBelow
  let B := max |M| |m|
  have hbound (x : Plane) (hx : x ∈ K) :
      ‖kpzLattice ϑ N t h₀ x ω‖ ≤ B := by
    have hvalue : kpzLattice ϑ N t h₀ x ω ∈ values := by
      rw [congrFun hfactor x]
      exact ⟨latticePoint N x, ⟨x, hx, rfl⟩, rfl⟩
    have hupper : kpzLattice ϑ N t h₀ x ω ≤ M := hM hvalue
    have hlower : m ≤ kpzLattice ϑ N t h₀ x ω := hm hvalue
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · dsimp [B]
      exact (neg_le_neg (le_max_right |M| |m|)).trans ((neg_abs_le m).trans hlower)
    · dsimp [B]
      exact hupper.trans (le_abs_self M |>.trans (le_max_left |M| |m|))
  have hInt : IntegrableOn (fun x : Plane => kpzLattice ϑ N t h₀ x ω) K volume := by
    apply Measure.integrableOn_of_bounded (μ := volume) (s := K)
    · exact ne_of_lt hK.measure_lt_top
    · exact hmeas.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      exact hbound x hx
  exact hInt

private theorem covarianceLogEnvelope_rpow_le_inv_sqrt (z : Plane) {p : ℝ}
    (hp : 0 < p) (hz : ‖z‖ ≤ 1) (hz0 : z ≠ 0) :
    CovarianceKernel.covarianceLogEnvelope z ^ p ≤
      (1 + 2 * p) ^ p * ‖z‖ ^ (-(1 / 2 : ℝ)) := by
  let u : ℝ := ‖z‖⁻¹
  let δ : ℝ := 1 / (2 * p)
  have hrpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hu : 1 ≤ u := by
    dsimp [u]
    exact (one_le_inv₀ hrpos).2 hz
  have hu0 : 0 ≤ u := le_trans (by norm_num) hu
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg hu
  have hprof : CovarianceKernel.covarianceLogEnvelope z =
      1 + Real.log (1 + Real.log u) := by
    change 1 + Real.log (1 + max 0 (Real.log u)) = _
    rw [max_eq_right hlogu]
  have hnested : Real.log (1 + Real.log u) ≤ Real.log u := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.log u by linarith)
    linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hinvδ : δ⁻¹ = 2 * p := by
    dsimp [δ]
    field_simp
  have hlogpow : Real.log u ≤ u ^ δ / δ := Real.log_le_rpow_div hu0 hδ
  have hupow : 1 ≤ u ^ δ := Real.one_le_rpow hu hδ.le
  have henv : CovarianceKernel.covarianceLogEnvelope z ≤
      (1 + 2 * p) * u ^ δ := by
    rw [hprof]
    calc
      1 + Real.log (1 + Real.log u) ≤ 1 + Real.log u := by linarith
      _ ≤ 1 + u ^ δ / δ := by linarith
      _ = 1 + (2 * p) * u ^ δ := by rw [div_eq_mul_inv, hinvδ]; ring
      _ ≤ (1 + 2 * p) * u ^ δ := by
        nlinarith only [hupow]
  have hpow := Real.rpow_le_rpow (le_of_lt (CovarianceKernel.covarianceLogEnvelope_pos z))
    henv hp.le
  calc
    CovarianceKernel.covarianceLogEnvelope z ^ p ≤ ((1 + 2 * p) * u ^ δ) ^ p := hpow
    _ = (1 + 2 * p) ^ p * u ^ (δ * p) := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hu0 _), ← Real.rpow_mul hu0]
    _ = (1 + 2 * p) ^ p * u ^ (1 / 2 : ℝ) := by
      rw [show δ * p = 1 / 2 by
        dsimp [δ]
        field_simp]
    _ = (1 + 2 * p) ^ p * ‖z‖ ^ (-(1 / 2 : ℝ)) := by
      have huEq : u ^ (1 / 2 : ℝ) = ‖z‖ ^ (-(1 / 2 : ℝ)) := by
        dsimp [u]
        rw [Real.inv_rpow hrpos.le, ← Real.rpow_neg hrpos.le]
      exact congrArg (fun v : ℝ => (1 + 2 * p) ^ p * v) huEq

private theorem integrableOn_covarianceLogEnvelope_rpow_ball {p R : ℝ}
    (hp : 0 < p) :
    IntegrableOn (fun z : Plane => CovarianceKernel.covarianceLogEnvelope z ^ p)
      (Metric.ball 0 R) volume := by
  let C := max ((1 + 2 * p) ^ p) (R ^ (1 / 2 : ℝ))
  have hC1 : (1 + 2 * p) ^ p ≤ C := le_max_left _ _
  have hCR : R ^ (1 / 2 : ℝ) ≤ C := le_max_right _ _
  have hmeas : AEStronglyMeasurable
      (fun z : Plane => CovarianceKernel.covarianceLogEnvelope z ^ p) volume := by
    exact ((by fun_prop [CovarianceKernel.covarianceLogEnvelope] :
      Measurable (fun z : Plane => CovarianceKernel.covarianceLogEnvelope z ^ p))
      ).aestronglyMeasurable
  have hdecay : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : Plane) R),
      ‖CovarianceKernel.covarianceLogEnvelope z ^ p‖ ≤ C * ‖z‖ ^ (-(1 / 2 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne (0 : Plane))] with z hzball hz0
    have hzNorm : ‖z‖ < R := by
      simpa [Metric.mem_ball, dist_zero_right] using hzball
    have hrpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg
        (le_of_lt (CovarianceKernel.covarianceLogEnvelope_pos z)) _)]
    by_cases hzle : ‖z‖ ≤ 1
    · exact (covarianceLogEnvelope_rpow_le_inv_sqrt z hp hzle hz0).trans
        (mul_le_mul_of_nonneg_right hC1 (Real.rpow_nonneg hrpos.le _))
    · have hone : 1 ≤ ‖z‖ := le_of_not_ge hzle
      have henv := CovarianceKernel.covarianceLogEnvelope_eq_one_of_one_le_norm z hone
      have hpow : CovarianceKernel.covarianceLogEnvelope z ^ p = 1 := by
        rw [henv, Real.one_rpow]
      rw [hpow]
      have hroot : ‖z‖ ^ (1 / 2 : ℝ) ≤ R ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (norm_nonneg _) hzNorm.le (by norm_num)
      have hrootC : ‖z‖ ^ (1 / 2 : ℝ) ≤ C := hroot.trans hCR
      have hrootPos : 0 < ‖z‖ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hrpos _
      have hratio : 1 ≤ C / ‖z‖ ^ (1 / 2 : ℝ) :=
        (one_le_div₀ hrootPos).2 hrootC
      rw [div_eq_mul_inv, ← Real.rpow_neg (norm_nonneg _) (1 / 2 : ℝ)] at hratio
      exact hratio
  exact integrableOn_ball_of_norm_le_rpow
    (by norm_num [Plane] : 1 ≤ Module.finrank ℝ Plane)
    (by norm_num [Plane] : (1 / 2 : ℝ) < Module.finrank ℝ Plane)
    hdecay hmeas

private theorem covarianceLogEnvelope_ge_one (z : Plane) :
    1 ≤ CovarianceKernel.covarianceLogEnvelope z := by
  unfold CovarianceKernel.covarianceLogEnvelope
  have hm : 0 ≤ max 0 (Real.log ‖z‖⁻¹) := le_max_left _ _
  have hl : 0 ≤ Real.log (1 + max 0 (Real.log ‖z‖⁻¹)) :=
    Real.log_nonneg (by linarith)
  linarith

private theorem lintegral_heatKernel_mul_covarianceLogEnvelope_le {p : ℝ}
    (hp : 1 < p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u : ℝ, 0 < u → ∀ x : Plane,
      (∫⁻ y : Plane, ENNReal.ofReal (heatKernel u (x - y)) *
        ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (x - y))) ≤
          ENNReal.ofReal (1 + A * u ^ (-1 / p)) := by
  let B : Set Plane := Metric.ball 0 1
  let cut : Plane → ℝ≥0∞ := B.indicator fun z =>
    ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope z)
  let M : ℝ≥0∞ := ∫⁻ z : Plane in B,
    ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope z ^ p)
  have hB : MeasurableSet B := measurableSet_ball
  have henvMeas : Measurable CovarianceKernel.covarianceLogEnvelope := by
    fun_prop [CovarianceKernel.covarianceLogEnvelope]
  have hcutMeas : Measurable cut := by
    exact (henvMeas.ennreal_ofReal).indicator hB
  have hcutPow : (fun z : Plane => cut z ^ p) = B.indicator
      (fun z => ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope z ^ p)) := by
    funext z
    by_cases hz : z ∈ B
    · have hpos := CovarianceKernel.covarianceLogEnvelope_pos z
      simp [cut, hz, ENNReal.ofReal_rpow_of_nonneg hpos.le (by linarith : 0 ≤ p)]
    · simp [cut, hz, ENNReal.zero_rpow_of_pos (by linarith : 0 < p)]
  have hIntEnv := integrableOn_covarianceLogEnvelope_rpow_ball
    (by linarith : 0 < p) (R := 1)
  have hconv : ENNReal.ofReal (∫ z : Plane in B,
      CovarianceKernel.covarianceLogEnvelope z ^ p) = M := by
    dsimp [M]
    exact ofReal_integral_eq_lintegral_ofReal hIntEnv
      (Filter.Eventually.of_forall fun z => Real.rpow_nonneg
        (le_of_lt (CovarianceKernel.covarianceLogEnvelope_pos z)) _)
  have hMtop : M < ⊤ := by
    rw [← hconv]
    exact ENNReal.ofReal_lt_top
  have hcutLp : (∫⁻ z : Plane, cut z ^ p) = M := by
    rw [hcutPow, lintegral_indicator hB]
  have hcutLower (z : Plane) :
      ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope z) ≤ 1 + cut z := by
    by_cases hz : z ∈ B
    · have hpos := CovarianceKernel.covarianceLogEnvelope_pos z
      have hcut : cut z = ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope z) := by
        simp [cut, hz]
      rw [hcut]
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) hpos.le]
      exact ENNReal.ofReal_le_ofReal (by linarith [covarianceLogEnvelope_ge_one z])
    · have hone : 1 ≤ ‖z‖ := by
        have hz' : ¬ ‖z‖ < 1 := by
          intro h
          exact hz (by simpa [B, Metric.mem_ball, dist_zero_right] using h)
        exact le_of_not_gt hz'
      rw [CovarianceKernel.covarianceLogEnvelope_eq_one_of_one_le_norm z hone]
      simp [cut, hz]
  obtain ⟨c, hc, hheat⟩ := Critical2DKPZ.SHF.Tsai.integral_heatKernel_mul_le hp
  let root : ℝ≥0∞ := M ^ (1 / p)
  have hrootTop : root < ⊤ := by
    dsimp [root]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hMtop.ne
  let D : ℝ := root.toReal
  have hrootEq : root = ENNReal.ofReal D := by
    dsimp [D]
    exact (ENNReal.ofReal_toReal hrootTop.ne).symm
  let A : ℝ := c * D
  have hAnonneg : 0 ≤ A := by
    dsimp [A, D]
    positivity
  refine ⟨A, hAnonneg, ?_⟩
  intro u hu x
  let shifted : Plane → ℝ≥0∞ := fun y => cut (x - y)
  have hshiftMeas : Measurable shifted := by
    exact hcutMeas.comp (measurable_const.sub measurable_id)
  have hmp : MeasurePreserving (fun y : Plane => x - y) volume volume :=
    volume.measurePreserving_sub_left x
  have hshiftLp : (∫⁻ y : Plane, shifted y ^ p) = M := by
    calc
      _ = ∫⁻ y : Plane, cut (x - y) ^ p := by simp [shifted]
      _ = ∫⁻ y : Plane, cut y ^ p :=
        hmp.lintegral_comp (ENNReal.continuous_rpow_const.measurable.comp hcutMeas)
      _ = M := hcutLp
  have hkernelMeas : Measurable (fun y : Plane => ENNReal.ofReal (heatKernel u (x - y))) := by
    exact ((measurable_heatKernel u).comp (measurable_const.sub measurable_id)).ennreal_ofReal
  have hmass : (∫⁻ y : Plane,
      ENNReal.ofReal (heatKernel u (x - y))) = ENNReal.ofReal 1 := by
    have hInt := hmp.integrable_comp_of_integrable (integrable_heatKernel hu)
    have hreal : ENNReal.ofReal (∫ y : Plane, heatKernel u (x - y)) =
        ∫⁻ y : Plane, ENNReal.ofReal (heatKernel u (x - y)) := by
      simpa only [Function.comp_apply] using
        (ofReal_integral_eq_lintegral_ofReal hInt
          (Filter.Eventually.of_forall fun y => heatKernel_nonneg hu.le _))
    rw [← hreal]
    have hkerEq : (fun y : Plane => heatKernel u (x - y)) =
        fun y => heatKernel u (y - x) := by
      funext y
      rw [show x - y = -(y - x) by abel, heatKernel_neg]
    rw [hkerEq, integral_heatKernel_sub hu x]
  have hsing := hheat u hu x shifted hshiftMeas
  have hfull : (∫⁻ y : Plane, ENNReal.ofReal (heatKernel u (x - y)) * shifted y) ≤
      ENNReal.ofReal (c * u ^ (-1 / p)) * root := by
    rw [hshiftLp] at hsing
    exact hsing
  have hsum : (∫⁻ y : Plane,
      ENNReal.ofReal (heatKernel u (x - y)) * ENNReal.ofReal 1 +
        ENNReal.ofReal (heatKernel u (x - y)) * shifted y) =
      ENNReal.ofReal 1 +
        ∫⁻ y : Plane, ENNReal.ofReal (heatKernel u (x - y)) * shifted y := by
    rw [lintegral_add_left (hkernelMeas.mul_const (ENNReal.ofReal 1))]
    simp only [ENNReal.ofReal_one, mul_one, hmass]
  have hbound : (∫⁻ y : Plane,
      ENNReal.ofReal (heatKernel u (x - y)) *
        ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (x - y))) ≤
      ENNReal.ofReal 1 + ENNReal.ofReal (c * u ^ (-1 / p)) * root := by
    calc
      _ ≤ ∫⁻ y : Plane,
          ENNReal.ofReal (heatKernel u (x - y)) * (ENNReal.ofReal 1 + shifted y) := by
            apply lintegral_mono
            intro y
            change ENNReal.ofReal (heatKernel u (x - y)) *
              ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (x - y)) ≤
                ENNReal.ofReal (heatKernel u (x - y)) *
                  (ENNReal.ofReal 1 + cut (x - y))
            calc
              _ = ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (x - y)) *
                  ENNReal.ofReal (heatKernel u (x - y)) := mul_comm _ _
              _ ≤ (ENNReal.ofReal 1 + cut (x - y)) *
                  ENNReal.ofReal (heatKernel u (x - y)) := by
                    simpa only [ENNReal.ofReal_one] using
                      (mul_le_mul_left (hcutLower (x - y))
                        (ENNReal.ofReal (heatKernel u (x - y))))
              _ = _ := mul_comm _ _
      _ = _ := by
        rw [show (fun y : Plane =>
            ENNReal.ofReal (heatKernel u (x - y)) * (ENNReal.ofReal 1 + shifted y)) =
            fun y => ENNReal.ofReal (heatKernel u (x - y)) * ENNReal.ofReal 1 +
              ENNReal.ofReal (heatKernel u (x - y)) * shifted y by
          funext y
          rw [mul_add]]
        rw [hsum]
      _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal (c * u ^ (-1 / p)) * root :=
        add_le_add le_rfl hfull
  rw [hrootEq, ← ENNReal.ofReal_mul (by positivity : 0 ≤ c * u ^ (-1 / p))] at hbound
  have hAeq : c * u ^ (-1 / p) * D = A * u ^ (-1 / p) := by
    dsimp [A]
    ring
  rw [hAeq, ← ENNReal.ofReal_add (by norm_num) (by positivity)] at hbound
  exact hbound

private theorem testFn_norm_data (χ : TestFn) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ x : Plane, ‖χ x‖ ≤ B) ∧
      Integrable (fun x : Plane => ‖χ x‖) volume := by
  have hK : IsCompact (tsupport χ) := χ.hasCompactSupport.isCompact
  have hImage : IsCompact ((fun x : Plane => ‖χ x‖) '' tsupport χ) :=
    hK.image χ.continuous.norm
  obtain ⟨M, hM⟩ := hImage.bddAbove
  refine ⟨max M 0, le_max_right _ _, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ tsupport χ
    · exact (hM ⟨x, hx, rfl⟩).trans (le_max_left _ _)
    · have hx0 : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hx0]
  · exact (χ.continuous.integrable_of_hasCompactSupport χ.hasCompactSupport).norm


private theorem lintegral_testFn_heatEnvelope_le (χ : TestFn) {p : ℝ}
    (hp : 1 < p) :
    ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧ (∀ y : Plane, ‖χ y‖ ≤ B) ∧
      ∀ u : ℝ, 0 < u → ∀ x : Plane,
        (∫⁻ y : Plane, ENNReal.ofReal ‖χ y‖ *
          (ENNReal.ofReal (heatKernel u (x - y)) *
            ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (x - y)))) ≤
          ENNReal.ofReal (B * (1 + A * u ^ (-1 / p))) := by
  obtain ⟨B, hB, hBbound, _⟩ := testFn_norm_data χ
  obtain ⟨A, hA, hheat⟩ := lintegral_heatKernel_mul_covarianceLogEnvelope_le hp
  refine ⟨B, A, hB, hA, hBbound, ?_⟩
  intro u hu x
  calc
    _ ≤ ∫⁻ y : Plane, ENNReal.ofReal B *
        (ENNReal.ofReal (heatKernel u (x - y)) *
          ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (x - y))) := by
          apply lintegral_mono
          intro y
          exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hBbound y)) _
    _ = ENNReal.ofReal B *
        ∫⁻ y : Plane, ENNReal.ofReal (heatKernel u (x - y)) *
          ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (x - y)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal B * ENNReal.ofReal (1 + A * u ^ (-1 / p)) := by
          calc
            _ = (∫⁻ y : Plane, ENNReal.ofReal (heatKernel u (x - y)) *
                ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (x - y))) *
                  ENNReal.ofReal B := mul_comm _ _
            _ ≤ ENNReal.ofReal (1 + A * u ^ (-1 / p)) * ENNReal.ofReal B :=
                  mul_le_mul_left (hheat u hu x) _
            _ = _ := mul_comm _ _
    _ = ENNReal.ofReal (B * (1 + A * u ^ (-1 / p))) := by
          rw [← ENNReal.ofReal_mul hB]

private theorem lintegral_testFn_pair_heatEnvelope_le (χ : TestFn) {p : ℝ}
    (hp : 1 < p) :
    ∃ B L A : ℝ, 0 ≤ B ∧ 0 ≤ L ∧ 0 ≤ A ∧
      ∀ u : ℝ, 0 < u →
        (∫⁻ q : Plane × Plane, ENNReal.ofReal ‖χ q.1‖ *
          (ENNReal.ofReal ‖χ q.2‖ *
            (ENNReal.ofReal (heatKernel (2 * u) (q.1 - q.2)) *
              ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (q.1 - q.2))))
            ∂volume.prod volume) ≤
          ENNReal.ofReal (L * B * (1 + A * (2 * u) ^ (-1 / p))) := by
  obtain ⟨_, _, _, hχInt⟩ := testFn_norm_data χ
  obtain ⟨B, A, hB, hA, hBbound, hinner⟩ := lintegral_testFn_heatEnvelope_le χ hp
  let L : ℝ := ∫ x : Plane, ‖χ x‖
  have hL : 0 ≤ L := by
    dsimp [L]
    exact integral_nonneg (fun x : Plane => norm_nonneg (χ x))
  have hLconv :
      (∫⁻ x : Plane, ENNReal.ofReal ‖χ x‖) = ENNReal.ofReal L := by
    dsimp [L]
    exact (ofReal_integral_eq_lintegral_ofReal hχInt
      (Filter.Eventually.of_forall fun x => norm_nonneg (χ x))
      ).symm
  refine ⟨B, L, A, hB, hL, hA, ?_⟩
  intro u hu
  have hχmeas : Measurable (fun x : Plane => ENNReal.ofReal ‖χ x‖) :=
    (χ.continuous.norm.measurable).ennreal_ofReal
  have hkernelMeas : Measurable (fun q : Plane × Plane =>
      ENNReal.ofReal (heatKernel (2 * u) (q.1 - q.2))) :=
    ((measurable_heatKernel (2 * u)).comp
      (measurable_fst.sub measurable_snd)).ennreal_ofReal
  have henvMeas : Measurable (fun q : Plane × Plane =>
      ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (q.1 - q.2))) := by
    fun_prop [CovarianceKernel.covarianceLogEnvelope]
  have hmeas : Measurable (fun q : Plane × Plane =>
      ENNReal.ofReal ‖χ q.1‖ *
        (ENNReal.ofReal ‖χ q.2‖ *
          (ENNReal.ofReal (heatKernel (2 * u) (q.1 - q.2)) *
            ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (q.1 - q.2))))) :=
    (hχmeas.comp measurable_fst).mul
      ((hχmeas.comp measurable_snd).mul (hkernelMeas.mul henvMeas))
  rw [lintegral_prod _ hmeas.aemeasurable]
  calc
    _ ≤ ∫⁻ x : Plane, ENNReal.ofReal ‖χ x‖ *
        ENNReal.ofReal (B * (1 + A * (2 * u) ^ (-1 / p))) := by
          apply lintegral_mono
          intro x
          change (∫⁻ y : Plane, ENNReal.ofReal ‖χ x‖ *
              (ENNReal.ofReal ‖χ y‖ *
                (ENNReal.ofReal (heatKernel (2 * u) (x - y)) *
                  ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (x - y))))) ≤
            ENNReal.ofReal ‖χ x‖ *
              ENNReal.ofReal (B * (1 + A * (2 * u) ^ (-1 / p)))
          have hpoint := hinner (2 * u) (mul_pos (by norm_num) hu) x
          calc
            _ = (∫⁻ y : Plane, ENNReal.ofReal ‖χ y‖ *
                (ENNReal.ofReal (heatKernel (2 * u) (x - y)) *
                  ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (x - y)))) *
                  ENNReal.ofReal ‖χ x‖ := by
                    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
                    rw [mul_comm (ENNReal.ofReal ‖χ x‖)]
            _ ≤ ENNReal.ofReal (B * (1 + A * (2 * u) ^ (-1 / p))) *
                ENNReal.ofReal ‖χ x‖ :=
                  mul_le_mul_left hpoint _
            _ = _ := mul_comm _ _
    _ = ENNReal.ofReal L *
        ENNReal.ofReal (B * (1 + A * (2 * u) ^ (-1 / p))) := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hLconv]
    _ = ENNReal.ofReal (L * B * (1 + A * (2 * u) ^ (-1 / p))) := by
          rw [← ENNReal.ofReal_mul hL]
          congr 1
          ring

private theorem kpzLattice_spatial_covariance_integral_le (ϑ : ℝ) {N : ℕ}
    {t : ℝ}
    (Ccov : ℝ) (hCcov : 0 ≤ Ccov)
    (hcov : ∀ x y : Plane, x ≠ y →
      0 ≤ ProbabilityTheory.covariance (fun ω => kpzLattice ϑ N t 0 x ω)
        (fun ω => kpzLattice ϑ N t 0 y ω) disorderLaw ∧
      ProbabilityTheory.covariance (fun ω => kpzLattice ϑ N t 0 x ω)
        (fun ω => kpzLattice ϑ N t 0 y ω) disorderLaw ≤
          Ccov * CovarianceKernel.covarianceLogEnvelope (x - y))
    (χ : TestFn) {p : ℝ} (B L A : ℝ)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hpair : ∀ u : ℝ, 0 < u →
      (∫⁻ q : Plane × Plane, ENNReal.ofReal ‖χ q.1‖ *
        (ENNReal.ofReal ‖χ q.2‖ *
          (ENNReal.ofReal (heatKernel (2 * u) (q.1 - q.2)) *
            ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (q.1 - q.2))))
        ∂volume.prod volume) ≤ ENNReal.ofReal (L * B * (1 + A * (2 * u) ^ (-1 / p)))) :
    ∀ u : ℝ, 0 < u →
        (∫ q : Plane × Plane,
          (heatKernel (2 * u) (q.1 - q.2) * (χ q.1 * χ q.2) *
            ProbabilityTheory.covariance (fun ω => kpzLattice ϑ N t 0 q.1 ω)
              (fun ω => kpzLattice ϑ N t 0 q.2 ω) disorderLaw)
          ∂volume.prod volume) ≤ (Ccov * (L * B)) * (1 + A * (2 * u) ^ (-1 / p)) := by
  have hneq : ∀ᵐ q : Plane × Plane ∂volume.prod volume, q.1 ≠ q.2 := by
    have hset : MeasurableSet {q : Plane × Plane | q.1 ≠ q.2} :=
      (isClosed_eq continuous_fst continuous_snd).measurableSet.compl
    rw [Measure.ae_prod_iff_ae_ae hset]
    filter_upwards [] with x
    filter_upwards [volume.ae_ne x] with y hy
    exact hy.symm
  intro u hu
  let f : Plane × Plane → ℝ := fun q =>
    heatKernel (2 * u) (q.1 - q.2) *
      (χ q.1 * χ q.2 * ProbabilityTheory.covariance
        (fun ω => kpzLattice ϑ N t 0 q.1 ω)
        (fun ω => kpzLattice ϑ N t 0 q.2 ω) disorderLaw)
  let pairWeight : Plane × Plane → ℝ≥0∞ := fun q =>
    ENNReal.ofReal ‖χ q.1‖ *
      (ENNReal.ofReal ‖χ q.2‖ *
        (ENNReal.ofReal (heatKernel (2 * u) (q.1 - q.2)) *
          ENNReal.ofReal (CovarianceKernel.covarianceLogEnvelope (q.1 - q.2)))
      )
  have hfieldBound (q : Plane × Plane) (hq : q.1 ≠ q.2) :
      ‖f q‖ ≤ Ccov * (‖χ q.1‖ * (‖χ q.2‖ *
        (heatKernel (2 * u) (q.1 - q.2) *
          CovarianceKernel.covarianceLogEnvelope (q.1 - q.2)))) := by
    let k := heatKernel (2 * u) (q.1 - q.2)
    let e := CovarianceKernel.covarianceLogEnvelope (q.1 - q.2)
    let c := ProbabilityTheory.covariance
      (fun ω => kpzLattice ϑ N t 0 q.1 ω)
      (fun ω => kpzLattice ϑ N t 0 q.2 ω) disorderLaw
    have hk : 0 ≤ k := by dsimp [k]; exact heatKernel_nonneg (by positivity) _
    have hc := hcov q.1 q.2 hq
    have hnorm : ‖f q‖ = k * (‖χ q.1‖ * (‖χ q.2‖ * c)) := by
      change |k * (χ q.1 * χ q.2 * c)| =
        k * (|χ q.1| * (|χ q.2| * c))
      rw [abs_mul, abs_of_nonneg hk, abs_mul, abs_mul, abs_of_nonneg hc.1]
      ring
    calc
      ‖f q‖ = k * (‖χ q.1‖ * (‖χ q.2‖ * c)) := hnorm
      _ ≤ k * (‖χ q.1‖ * (‖χ q.2‖ * (Ccov * e))) := by
        apply mul_le_mul_of_nonneg_left
        · have hmul := mul_le_mul_of_nonneg_left hc.2
            (mul_nonneg (norm_nonneg (χ q.1)) (norm_nonneg (χ q.2)))
          simpa [mul_assoc] using hmul
        · exact hk
      _ = Ccov * (‖χ q.1‖ * (‖χ q.2‖ * (k * e))) := by
        dsimp [k, e]
        ring
  have hnormAE : ∀ᵐ q : Plane × Plane ∂volume.prod volume,
      ENNReal.ofReal ‖f q‖ ≤ ENNReal.ofReal Ccov * pairWeight q := by
    filter_upwards [hneq] with q hq
    calc
      ENNReal.ofReal ‖f q‖ ≤ ENNReal.ofReal (Ccov *
          (‖χ q.1‖ * (‖χ q.2‖ *
            (heatKernel (2 * u) (q.1 - q.2) *
              CovarianceKernel.covarianceLogEnvelope (q.1 - q.2))))) :=
        ENNReal.ofReal_le_ofReal (hfieldBound q hq)
      _ = ENNReal.ofReal Ccov * pairWeight q := by
        dsimp [pairWeight]
        rw [ENNReal.ofReal_mul hCcov, ENNReal.ofReal_mul (abs_nonneg (χ q.1)),
          ENNReal.ofReal_mul (abs_nonneg (χ q.2)),
          ENNReal.ofReal_mul (heatKernel_nonneg (by positivity) _)]
  have hpairU := hpair u hu
  have hnormIntegral :
      (∫⁻ q : Plane × Plane, ENNReal.ofReal ‖f q‖ ∂volume.prod volume) ≤
        ENNReal.ofReal (Ccov * (L * B * (1 + A * (2 * u) ^ (-1 / p)))) := by
    calc
      _ ≤ ∫⁻ q : Plane × Plane, ENNReal.ofReal Ccov * pairWeight q
            ∂volume.prod volume := lintegral_mono_ae hnormAE
      _ = ENNReal.ofReal Ccov *
          ∫⁻ q : Plane × Plane, pairWeight q ∂volume.prod volume := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal Ccov *
          ENNReal.ofReal (L * B * (1 + A * (2 * u) ^ (-1 / p))) :=
            mul_le_mul_of_nonneg_left hpairU (by positivity)
      _ = ENNReal.ofReal (Ccov * (L * B * (1 + A * (2 * u) ^ (-1 / p)))) := by
            rw [← ENNReal.ofReal_mul hCcov]
  have hrealBound :
      ‖∫ q : Plane × Plane, f q ∂volume.prod volume‖ ≤
        Ccov * (L * B * (1 + A * (2 * u) ^ (-1 / p))) := by
    calc
      _ ≤ ENNReal.toReal
          (∫⁻ q : Plane × Plane, ENNReal.ofReal ‖f q‖ ∂volume.prod volume) :=
            norm_integral_le_lintegral_norm _
      _ ≤ Ccov * (L * B * (1 + A * (2 * u) ^ (-1 / p))) := by
            calc
              _ ≤ ENNReal.toReal
                  (ENNReal.ofReal
                    (Ccov * (L * B * (1 + A * (2 * u) ^ (-1 / p))))) :=
                  ENNReal.toReal_mono ENNReal.ofReal_ne_top hnormIntegral
              _ = _ := ENNReal.toReal_ofReal (by positivity)
  have hintegral :
      (∫ q : Plane × Plane, f q ∂volume.prod volume) ≤
        Ccov * (L * B * (1 + A * (2 * u) ^ (-1 / p))) := by
    calc
      _ ≤ |∫ q : Plane × Plane, f q ∂volume.prod volume| := le_abs_self _
      _ = ‖∫ q : Plane × Plane, f q ∂volume.prod volume‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ _ := hrealBound
  simpa [f, mul_assoc, mul_left_comm, mul_comm] using hintegral

private theorem lintegral_rpow_exp_neg_finite {s : ℝ} (hs : -1 < s) :
    (∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (u ^ s * Real.exp (-u))) < ⊤ := by
  have hInt : IntegrableOn (fun u : ℝ => u ^ s * Real.exp (-u)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_rpow hs (by norm_num : (0 : ℝ) < 1))
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)]
      fun u : ℝ => u ^ s * Real.exp (-u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hnonneg]
  exact ENNReal.ofReal_lt_top

private theorem kpzLattice_flat_negSobolev_moment_le_of
    (hVD : Smoothing.PropVDBound) (ϑ : ℝ) {t : ℝ} (ht : 0 < t)
    {a : ℝ} (ha : 0 < a) (χ : TestFn) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      ∫⁻ ω, localNegSobolevSq a
        (Distribution.ofFun ⊤ (fun x => kpzLattice ϑ N t 0 x ω) volume ⊤) χ
        ∂disorderLaw ≤ ENNReal.ofReal C := by
  let p : ℝ := max 2 (a⁻¹ + 1)
  have hp : 1 < p := by
    dsimp [p]
    linarith [le_max_left 2 (a⁻¹ + 1)]
  have hpa : 1 / p < a := by
    have hmax : a⁻¹ + 1 ≤ p := le_max_right _ _
    have hmul : 1 < a * p := by
      have hmul := mul_le_mul_of_nonneg_left hmax ha.le
      nlinarith [ha, mul_inv_cancel₀ ha.ne']
    rw [div_lt_iff₀ (lt_trans zero_lt_one hp)]
    exact hmul
  obtain ⟨Ccov, hcovN⟩ := kpzLattice_flat_covariance_le_of hVD ϑ
    (t₀ := t) (t₁ := t) ht
  obtain ⟨N₀, hcov₀⟩ := hcovN.exists
  let y₀ : Plane := EuclideanSpace.single 0 (1 : ℝ)
  have hxy₀ : (0 : Plane) ≠ y₀ := by
    intro h
    have hval := congrArg (fun x : Plane => x 0) h
    simp [y₀] at hval
  have hcov₀xy := hcov₀ t ⟨le_rfl, le_rfl⟩ (0 : Plane) y₀ hxy₀
  have hCcov : 0 ≤ Ccov := by
    obtain ⟨hpos, hupper⟩ := hcov₀xy
    have henv := CovarianceKernel.covarianceLogEnvelope_pos ((0 : Plane) - y₀)
    have hupper' :
        ProbabilityTheory.covariance (fun ω => kpzLattice ϑ N₀ t 0 0 ω)
          (fun ω => kpzLattice ϑ N₀ t 0 y₀ ω) disorderLaw ≤
            Ccov * CovarianceKernel.covarianceLogEnvelope ((0 : Plane) - y₀) := by
      simpa [CovarianceKernel.covarianceLogEnvelope] using hupper
    by_contra hneg
    have hCneg : Ccov < 0 := lt_of_not_ge hneg
    have hprod : Ccov * CovarianceKernel.covarianceLogEnvelope
        ((0 : Plane) - y₀) < 0 := mul_neg_of_neg_of_pos hCneg henv
    linarith
  obtain ⟨B, L, A, hB, hL, hA, hpairBase⟩ :=
    lintegral_testFn_pair_heatEnvelope_le χ hp
  let Cpair : ℝ := Ccov * (L * B)
  have hCpair : 0 ≤ Cpair := by dsimp [Cpair]; positivity
  let w0 : ℝ → ℝ := fun u => u ^ (a - 1) * Real.exp (-u)
  let w1 : ℝ → ℝ := fun u => u ^ (a - 1 - 1 / p) * Real.exp (-u)
  let K0 : ℝ≥0∞ := ∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (w0 u)
  let K1 : ℝ≥0∞ := ∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (w1 u)
  have hK0top : K0 < ⊤ := by
    dsimp [K0, w0]
    apply lintegral_rpow_exp_neg_finite
    linarith
  have hK1top : K1 < ⊤ := by
    dsimp [K1, w1]
    apply lintegral_rpow_exp_neg_finite
    linarith
  let R : ℝ≥0∞ := ENNReal.ofReal Cpair *
    (K0 + ENNReal.ofReal A * K1)
  have hRtop : R < ⊤ := by
    dsimp [R]
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    exact ENNReal.add_lt_top.mpr ⟨hK0top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK1top⟩
  let G : ℝ≥0∞ := ENNReal.ofReal ((Real.Gamma a)⁻¹)
  have hGtop : G < ⊤ := by
    dsimp [G]
    exact ENNReal.ofReal_lt_top
  let M : ℝ≥0∞ := G * R
  have hMtop : M < ⊤ := by
    dsimp [M]
    exact ENNReal.mul_lt_top hGtop hRtop
  have hNevent : ∀ᶠ N : ℕ in atTop, ⌈t⁻¹⌉₊ + 1 ≤ N :=
    eventually_ge_atTop (⌈t⁻¹⌉₊ + 1)
  refine ⟨M.toReal, ?_⟩
  filter_upwards [hcovN, hNevent] with N hcov hNlarge
  have hNpos : 0 < N := by omega
  have hceil : (⌈t⁻¹⌉₊ : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.le_trans (Nat.le_succ _) (by omega : ⌈t⁻¹⌉₊ + 1 ≤ N))
  have hceilLower : t⁻¹ ≤ (N : ℝ) := (Nat.le_ceil t⁻¹).trans hceil
  have hNt : 1 ≤ (N : ℝ) * t := by
    have hmul := mul_le_mul_of_nonneg_right hceilLower ht.le
    have hinv : t⁻¹ * t = 1 := inv_mul_cancel₀ ht.ne'
    nlinarith
  have hntReal : (1 : ℝ) ≤ (evenCeil ((N : ℝ) * t) : ℝ) :=
    hNt.trans (le_evenCeil ((N : ℝ) * t))
  have hnt : 1 ≤ evenCeil ((N : ℝ) * t) := by exact_mod_cast hntReal
  have hcov : ∀ x y : Plane, x ≠ y →
      0 ≤ ProbabilityTheory.covariance (fun ω => kpzLattice ϑ N t 0 x ω)
        (fun ω => kpzLattice ϑ N t 0 y ω) disorderLaw ∧
      ProbabilityTheory.covariance (fun ω => kpzLattice ϑ N t 0 x ω)
        (fun ω => kpzLattice ϑ N t 0 y ω) disorderLaw ≤
          Ccov * CovarianceKernel.covarianceLogEnvelope (x - y) := by
    intro x y hxy
    obtain ⟨hpos, hupper⟩ := hcov t ⟨le_rfl, le_rfl⟩ x y hxy
    exact ⟨hpos, by simpa [CovarianceKernel.covarianceLogEnvelope] using hupper⟩
  have hpairSpatial : ∀ u : ℝ, 0 < u →
      (∫ q : Plane × Plane,
        (heatKernel (2 * u) (q.1 - q.2) * (χ q.1 * χ q.2) *
          ProbabilityTheory.covariance (fun ω => kpzLattice ϑ N t 0 q.1 ω)
            (fun ω => kpzLattice ϑ N t 0 q.2 ω) disorderLaw)
        ∂volume.prod volume) ≤ Cpair * (1 + A * (2 * u) ^ (-1 / p)) := by
    simpa [Cpair, mul_assoc] using
      (kpzLattice_spatial_covariance_integral_le ϑ (N := N) (t := t)
        Ccov hCcov hcov χ B L A hB hL hA hpairBase)
  obtain ⟨Csecond, hCsecond, hsecond⟩ :=
    kpzLattice_flat_uniform_secondMoment ϑ hNpos hnt
  have hX : Measurable (fun p : Disorder × Plane => kpzLattice ϑ N t 0 p.2 p.1) :=
    memLp_kpzLattice_flat_joint ϑ hNpos
  have hXi : ∀ ω, LocallyIntegrable (fun x => kpzLattice ϑ N t 0 x ω) volume := by
    intro ω
    exact locallyIntegrable_kpzLattice ϑ N t 0 ω
  have hzero : ∀ x : Plane, (∫ ω, kpzLattice ϑ N t 0 x ω ∂disorderLaw) = 0 := by
    intro x
    exact integral_kpzLattice_flat_zero_at ϑ hNpos hnt x
  have hmomentEq :=
    lintegral_localNegSobolevSq_ofFun_eq_covariance_of_uniform_second_moment
      disorderLaw hX hXi χ hCsecond hsecond hzero ha
  have houter :
      (∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (w0 u) * ENNReal.ofReal
        (∫ q : Plane × Plane,
          (heatKernel (2 * u) (q.1 - q.2) * (χ q.1 * χ q.2) *
            ProbabilityTheory.covariance (fun ω => kpzLattice ϑ N t 0 q.1 ω)
              (fun ω => kpzLattice ϑ N t 0 q.2 ω) disorderLaw)
          ∂volume.prod volume)) ≤ R := by
    calc
      _ ≤ ∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal Cpair *
          (ENNReal.ofReal (w0 u) + ENNReal.ofReal A * ENNReal.ofReal (w1 u)) := by
            apply lintegral_mono_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
            have hu' : 0 < u := hu
            have hsp := hpairSpatial u hu'
            have hw0 : 0 ≤ w0 u := by
              dsimp [w0]
              exact mul_nonneg (Real.rpow_nonneg hu'.le _) (Real.exp_pos _).le
            have hpow : (2 * u) ^ (-1 / p) ≤ u ^ (-1 / p) := by
              have hp0 : 0 < p := lt_trans one_pos hp
              have hpinv : 0 < 1 / p := one_div_pos.mpr hp0
              have hpowExp : (-1 : ℝ) / p = -(1 / p) := by ring
              exact Real.rpow_le_rpow_of_nonpos hu' (by nlinarith) (by
                rw [hpowExp]
                exact neg_nonpos.mpr hpinv.le)
            have hpower : w0 u * u ^ (-1 / p) = w1 u := by
              dsimp [w0, w1]
              calc
                u ^ (a - 1) * Real.exp (-u) * u ^ (-1 / p) =
                    (u ^ (a - 1) * u ^ (-1 / p)) * Real.exp (-u) := by ring
                _ = u ^ ((a - 1) + (-1 / p)) * Real.exp (-u) := by
                  rw [← Real.rpow_add hu']
                _ = u ^ (a - 1 - 1 / p) * Real.exp (-u) := by
                  congr 1
                  congr 1
                  ring
            have hreal : w0 u *
                (∫ q : Plane × Plane,
                  (heatKernel (2 * u) (q.1 - q.2) * (χ q.1 * χ q.2) *
                    ProbabilityTheory.covariance (fun ω => kpzLattice ϑ N t 0 q.1 ω)
                      (fun ω => kpzLattice ϑ N t 0 q.2 ω) disorderLaw)
                  ∂volume.prod volume) ≤ Cpair * (w0 u + A * w1 u) := by
              have hterm : 1 + A * (2 * u) ^ (-1 / p) ≤
                  1 + A * u ^ (-1 / p) := by
                gcongr
              calc
                _ ≤ w0 u * (Cpair * (1 + A * (2 * u) ^ (-1 / p))) :=
                  mul_le_mul_of_nonneg_left hsp hw0
                _ ≤ w0 u * (Cpair * (1 + A * u ^ (-1 / p))) := by
                  apply mul_le_mul_of_nonneg_left
                  · exact mul_le_mul_of_nonneg_left hterm hCpair
                  · exact hw0
                _ = Cpair * (w0 u + A * (w0 u * u ^ (-1 / p))) := by ring
                _ = Cpair * (w0 u + A * w1 u) := by rw [hpower]
            have hw1 : 0 ≤ w1 u := by
              dsimp [w1]
              exact mul_nonneg (Real.rpow_nonneg hu'.le _) (Real.exp_pos _).le
            have hAw1 : 0 ≤ A * w1 u := mul_nonneg hA hw1
            calc
              _ = ENNReal.ofReal (w0 u *
                  (∫ q : Plane × Plane,
                    (heatKernel (2 * u) (q.1 - q.2) * (χ q.1 * χ q.2) *
                      ProbabilityTheory.covariance (fun ω => kpzLattice ϑ N t 0 q.1 ω)
                        (fun ω => kpzLattice ϑ N t 0 q.2 ω) disorderLaw)
                    ∂volume.prod volume)) := by rw [← ENNReal.ofReal_mul hw0]
              _ ≤ ENNReal.ofReal (Cpair * (w0 u + A * w1 u)) :=
                ENNReal.ofReal_le_ofReal hreal
              _ = ENNReal.ofReal Cpair *
                  (ENNReal.ofReal (w0 u) + ENNReal.ofReal A * ENNReal.ofReal (w1 u)) := by
                rw [ENNReal.ofReal_mul hCpair, ENNReal.ofReal_add hw0 hAw1,
                  ENNReal.ofReal_mul hA]
      _ = R := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_left (by fun_prop : Measurable (fun u : ℝ => ENNReal.ofReal (w0 u)))]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hMofReal : ENNReal.ofReal M.toReal = M := ENNReal.ofReal_toReal hMtop.ne
  have houter' :
      (∫⁻ u : ℝ in Ioi 0,
        ENNReal.ofReal (u ^ (a - 1) * Real.exp (-u)) * ENNReal.ofReal
          (∫ q : Plane × Plane,
            (heatKernel (2 * u) (q.1 - q.2) * (χ q.1 * χ q.2) *
              ProbabilityTheory.covariance (fun ω => kpzLattice ϑ N t 0 q.1 ω)
                (fun ω => kpzLattice ϑ N t 0 q.2 ω) disorderLaw)
            ∂volume.prod volume)) ≤ R := by
    simpa [w0] using houter
  rw [hmomentEq]
  change G * (∫⁻ u : ℝ in Ioi 0,
      ENNReal.ofReal (u ^ (a - 1) * Real.exp (-u)) * ENNReal.ofReal
        (∫ q : Plane × Plane,
          (heatKernel (2 * u) (q.1 - q.2) * (χ q.1 * χ q.2) *
            ProbabilityTheory.covariance (fun ω => kpzLattice ϑ N t 0 q.1 ω)
              (fun ω => kpzLattice ϑ N t 0 q.2 ω) disorderLaw)
          ∂volume.prod volume)) ≤ ENNReal.ofReal M.toReal
  calc
    _ ≤ G * R := mul_le_mul_of_nonneg_left houter' bot_le
    _ = M := rfl
    _ = ENNReal.ofReal M.toReal := hMofReal.symm

private theorem integrable_rescaledP2P_flat_spatial (ϑ : ℝ) {N : ℕ}
    (hN : 0 < N) (t : ℝ) (x : Plane) (ω : Disorder) :
    Integrable (fun y : Plane => rescaledP2P ϑ N 0 t (y, x) ω) volume := by
  let n := evenCeil ((N : ℝ) * t)
  have hnEven : Even n := by simpa [n] using evenCeil_even ((N : ℝ) * t)
  have hcoeff : ∀ q : (Fin n → Fin 4) × (Fin n → Fin 4),
      0 ≤ flatMassPathCoeff q := by
    intro q
    dsimp [flatMassPathCoeff]
    split_ifs <;> positivity
  have hcoeffPos : ∃ q : (Fin n → Fin 4) × (Fin n → Fin 4),
      0 < flatMassPathCoeff q := by
    let s : Fin n → Fin 4 := fun _ => 0
    refine ⟨(s, s), ?_⟩
    simp [flatMassPathCoeff, s]
  have hmassPos := PolymerCalculus.finitePathMass_pos (criticalBeta ϑ N) 0 n
    (fun s => flatMassPathStart (latticePoint N x) s) hcoeff hcoeffPos ω
  have hmassEq := integral_rescaledP2P_flat_eq_finitePathMass ϑ hN t x ω hnEven
  by_contra hnot
  rw [integral_undef hnot] at hmassEq
  exact (ne_of_gt hmassPos) hmassEq.symm

private theorem kpzLattice_initialShift_bound (ϑ : ℝ) {N : ℕ}
    (hN : 0 < N) (t : ℝ) (h₀ : Plane →ᵇ ℝ) (x : Plane) (ω : Disorder) :
    |kpzLattice ϑ N t h₀ x ω - kpzLattice ϑ N t 0 x ω| ≤ ‖h₀‖ := by
  let f : Plane → ℝ := fun y => rescaledP2P ϑ N 0 t (y, x) ω
  let zh : ℝ := ∫ y : Plane, Real.exp (h₀ y) * f y
  let z0 : ℝ := ∫ y : Plane, f y
  have hfInt : Integrable f volume := by
    exact integrable_rescaledP2P_flat_spatial ϑ hN t x ω
  have hfNonneg : ∀ y, 0 ≤ f y := by
    intro y
    dsimp [f]
    simpa [rescaledP2P] using
      mul_nonneg (by positivity : 0 ≤ (N : ℝ) / 4)
        (Polymer.pointToPoint_nonneg (criticalBeta ϑ N) 0
          (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * 0))
          (latticePoint N y) (latticePoint N x) ω)
  have hcoeff : ∀ q : (Fin (evenCeil ((N : ℝ) * t)) → Fin 4) ×
      (Fin (evenCeil ((N : ℝ) * t)) → Fin 4), 0 ≤
        flatMassPathCoeff q := by
    intro q
    dsimp [flatMassPathCoeff]
    split_ifs <;> positivity
  have hcoeffPos : ∃ q : (Fin (evenCeil ((N : ℝ) * t)) → Fin 4) ×
      (Fin (evenCeil ((N : ℝ) * t)) → Fin 4), 0 < flatMassPathCoeff q := by
    let s : Fin (evenCeil ((N : ℝ) * t)) → Fin 4 := fun _ => 0
    refine ⟨(s, s), ?_⟩
    simp [flatMassPathCoeff, s]
  have hz0Pos : 0 < z0 := by
    dsimp [z0, f]
    rw [integral_rescaledP2P_flat_eq_finitePathMass ϑ hN t x ω
      (evenCeil_even ((N : ℝ) * t))]
    exact PolymerCalculus.finitePathMass_pos (criticalBeta ϑ N) 0
      (evenCeil ((N : ℝ) * t))
      (fun s => flatMassPathStart (latticePoint N x) s) hcoeff hcoeffPos ω
  let c := ‖h₀‖
  have hexpUpper (y : Plane) : Real.exp (h₀ y) ≤ Real.exp c := by
    apply Real.exp_le_exp.mpr
    exact (abs_le.mp (h₀.norm_coe_le_norm y)).2
  have hexpLower (y : Plane) : Real.exp (-c) ≤ Real.exp (h₀ y) := by
    apply Real.exp_le_exp.mpr
    exact (abs_le.mp (h₀.norm_coe_le_norm y)).1
  let upper : Plane → ℝ := fun y => Real.exp c * f y
  let lower : Plane → ℝ := fun y => Real.exp (-c) * f y
  have hupperInt : Integrable upper volume := by
    dsimp [upper]
    exact hfInt.const_mul (Real.exp c)
  have hlowerInt : Integrable lower volume := by
    dsimp [lower]
    exact hfInt.const_mul (Real.exp (-c))
  have hweightedAES : AEStronglyMeasurable (fun y => Real.exp (h₀ y) * f y) volume := by
    exact (Real.continuous_exp.comp h₀.continuous).measurable.aestronglyMeasurable.mul
      hfInt.aestronglyMeasurable
  have hweightedInt : Integrable (fun y => Real.exp (h₀ y) * f y) volume := by
    refine hupperInt.mono' hweightedAES ?_
    filter_upwards [] with y
    have hnonneg := hfNonneg y
    simpa [upper, abs_of_nonneg hnonneg] using
      mul_le_mul_of_nonneg_right (hexpUpper y) hnonneg
  have hupper : zh ≤ ∫ y, upper y := by
    dsimp [zh, upper]
    exact integral_mono hweightedInt hupperInt (fun y =>
      mul_le_mul_of_nonneg_right (hexpUpper y) (hfNonneg y))
  have hlower : ∫ y, lower y ≤ zh := by
    dsimp [zh, lower]
    exact integral_mono hlowerInt hweightedInt (fun y =>
      mul_le_mul_of_nonneg_right (hexpLower y) (hfNonneg y))
  have hupper' : zh ≤ Real.exp c * z0 := by
    calc
      zh ≤ ∫ y, upper y := hupper
      _ = Real.exp c * z0 := by
        simp only [upper]
        rw [integral_const_mul]
  have hlower' : Real.exp (-c) * z0 ≤ zh := by
    calc
      Real.exp (-c) * z0 = ∫ y, lower y := by
        simp only [lower]
        rw [integral_const_mul]
      _ ≤ zh := hlower
  have hzhPos : 0 < zh := lt_of_lt_of_le
    (mul_pos (Real.exp_pos _) hz0Pos) hlower'
  have hlogLower := Real.log_le_log (mul_pos (Real.exp_pos _) hz0Pos) hlower'
  have hlogUpper := Real.log_le_log hzhPos hupper'
  have hlogLower' : -c + Real.log z0 ≤ Real.log zh := by
    rw [Real.log_mul (Real.exp_pos (-c)).ne' hz0Pos.ne', Real.log_exp] at hlogLower
    exact hlogLower
  have hlogUpper' : Real.log zh ≤ c + Real.log z0 := by
    rw [Real.log_mul (Real.exp_pos c).ne' hz0Pos.ne', Real.log_exp] at hlogUpper
    exact hlogUpper
  have hrepr : kpzLattice ϑ N t h₀ x ω - kpzLattice ϑ N t 0 x ω =
      Real.log zh - Real.log z0 := by
    simp [kpzLattice, zh, z0, f]
  rw [hrepr, abs_le]
  constructor <;> linarith [hlogLower', hlogUpper']

private theorem kpzLattice_shift_local_energy_le (ϑ : ℝ) {N : ℕ}
    (hN : 0 < N) (t : ℝ) (h₀ : Plane →ᵇ ℝ) (χ : TestFn) (ω : Disorder)
    {a : ℝ} (ha : 0 ≤ a) :
    localNegSobolevSq a
        (Distribution.ofFun ⊤
          (fun x => kpzLattice ϑ N t h₀ x ω - kpzLattice ϑ N t 0 x ω) volume ⊤) χ ≤
      ENNReal.ofReal (‖h₀‖ ^ 2) *
        ∫⁻ x : Plane, ENNReal.ofReal (χ x ^ 2) := by
  let D : Plane → ℝ := fun x =>
    kpzLattice ϑ N t h₀ x ω - kpzLattice ϑ N t 0 x ω
  have hDloc : LocallyIntegrable D volume := by
    dsimp [D]
    exact (locallyIntegrable_kpzLattice ϑ N t h₀ ω).sub
      (locallyIntegrable_kpzLattice ϑ N t 0 ω)
  have hD : ∀ x : Plane, |D x| ≤ ‖h₀‖ := by
    intro x
    exact kpzLattice_initialShift_bound ϑ hN t h₀ x ω
  calc
    _ ≤ ∫⁻ x : Plane, ENNReal.ofReal ((χ x * D x) ^ 2) :=
      localNegSobolevSq_ofFun_le_lintegral ha hDloc χ
    _ ≤ ∫⁻ x : Plane, ENNReal.ofReal (‖h₀‖ ^ 2) * ENNReal.ofReal (χ x ^ 2) := by
      apply lintegral_mono
      intro x
      change ENNReal.ofReal ((χ x * D x) ^ 2) ≤
        ENNReal.ofReal (‖h₀‖ ^ 2) * ENNReal.ofReal (χ x ^ 2)
      rw [← ENNReal.ofReal_mul (sq_nonneg ‖h₀‖)]
      apply ENNReal.ofReal_le_ofReal
      have hDsq : |D x| ^ 2 ≤ ‖h₀‖ ^ 2 := by
        have habs := abs_nonneg (D x)
        have hnorm := norm_nonneg h₀
        nlinarith [hD x]
      have hprod : |χ x| ^ 2 * |D x| ^ 2 ≤
          ‖h₀‖ ^ 2 * |χ x| ^ 2 :=
        calc
          _ ≤ |χ x| ^ 2 * ‖h₀‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hDsq (sq_nonneg (|χ x|))
          _ = _ := by ring
      calc
        (χ x * D x) ^ 2 = |χ x| ^ 2 * |D x| ^ 2 := by
          rw [← sq_abs, abs_mul, mul_pow]
        _ ≤ ‖h₀‖ ^ 2 * |χ x| ^ 2 := hprod
        _ = ‖h₀‖ ^ 2 * χ x ^ 2 := by rw [sq_abs]
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The expected localized negative Sobolev energy of the centered lattice field is uniformly bounded at large scales. -/
theorem kpzLattice_negSobolev_moment_le_of (hVD : Smoothing.PropVDBound) (ϑ : ℝ)
    {t : ℝ} (ht : 0 < t) (h₀ : Plane →ᵇ ℝ) {a : ℝ} (ha : 0 < a)
    (χ : TestFn) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      ∫⁻ ω, localNegSobolevSq a
          (Distribution.ofFun ⊤ (fun x => kpzLattice ϑ N t h₀ x ω) volume ⊤) χ
          ∂disorderLaw ≤ ENNReal.ofReal C := by
  obtain ⟨B, hB0, hBχ, hBint⟩ := testFn_norm_data χ
  let c : ℝ := ‖h₀‖
  let Mχ : ℝ≥0∞ := ∫⁻ x : Plane, ENNReal.ofReal ‖χ x‖
  let K : ℝ≥0∞ := ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal B * Mχ)
  have hc : 0 ≤ c := by exact norm_nonneg _
  have hMχtop : Mχ < ⊤ := by
    have heq : Mχ = ENNReal.ofReal (∫ x : Plane, ‖χ x‖) := by
      dsimp [Mχ]
      simpa only [Real.norm_eq_abs] using
        (ofReal_integral_eq_lintegral_ofReal hBint
          (Filter.Eventually.of_forall fun x => norm_nonneg (χ x))).symm
    rw [heq]
    exact ENNReal.ofReal_lt_top
  have hKtop : K < ⊤ := by
    dsimp [K]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hMχtop)
  have hDenergy (N : ℕ) (hN : 0 < N) (ω : Disorder) :
      localNegSobolevSq a
          (Distribution.ofFun ⊤
            (fun x => kpzLattice ϑ N t h₀ x ω - kpzLattice ϑ N t 0 x ω) volume ⊤) χ ≤ K := by
    calc
      _ ≤ ENNReal.ofReal (c ^ 2) *
            ∫⁻ x : Plane, ENNReal.ofReal (χ x ^ 2) :=
        kpzLattice_shift_local_energy_le ϑ hN t h₀ χ ω ha.le
      _ ≤ ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal B * Mχ) := by
        have hchi : ∫⁻ x : Plane, ENNReal.ofReal (χ x ^ 2) ≤
            ENNReal.ofReal B * Mχ := by
          calc
            _ ≤ ∫⁻ x : Plane, ENNReal.ofReal B * ENNReal.ofReal ‖χ x‖ := by
              apply lintegral_mono
              intro x
              change ENNReal.ofReal (χ x ^ 2) ≤
                ENNReal.ofReal B * ENNReal.ofReal ‖χ x‖
              rw [← ENNReal.ofReal_mul hB0]
              apply ENNReal.ofReal_le_ofReal
              have hχ : |χ x| ≤ B := by
                simpa only [Real.norm_eq_abs] using hBχ x
              have hbound : χ x ^ 2 ≤ B * |χ x| := by
                rw [← sq_abs]
                nlinarith [abs_nonneg (χ x)]
              simpa [Real.norm_eq_abs, mul_comm] using hbound
            _ = ENNReal.ofReal B * Mχ := by
              dsimp [Mχ]
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        calc
          _ ≤ ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal B * Mχ) :=
            mul_le_mul_of_nonneg_left hchi bot_le
          _ = K := rfl
  obtain ⟨Cflat, hflat⟩ :=
    kpzLattice_flat_negSobolev_moment_le_of hVD ϑ ht ha χ
  let C₀ : ℝ := max Cflat 0
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hflat' : ∀ᶠ N : ℕ in atTop,
      ∫⁻ ω, localNegSobolevSq a
        (Distribution.ofFun ⊤ (fun x => kpzLattice ϑ N t 0 x ω) volume ⊤) χ
        ∂disorderLaw ≤ ENNReal.ofReal C₀ := by
    filter_upwards [hflat] with N hN
    exact hN.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  refine ⟨2 * (C₀ + K.toReal), ?_⟩
  filter_upwards [hflat', eventually_ge_atTop 1] with N hflat hN
  have hNpos : 0 < N := by omega
  let Xh : Disorder → Plane → ℝ := fun ω x => kpzLattice ϑ N t h₀ x ω
  let X0 : Disorder → Plane → ℝ := fun ω x => kpzLattice ϑ N t 0 x ω
  let XD : Disorder → Plane → ℝ := fun ω x => Xh ω x - X0 ω x
  have hXhi : ∀ ω, LocallyIntegrable (Xh ω) volume := by
    intro ω
    exact locallyIntegrable_kpzLattice ϑ N t h₀ ω
  have hX0i : ∀ ω, LocallyIntegrable (X0 ω) volume := by
    intro ω
    exact locallyIntegrable_kpzLattice ϑ N t 0 ω
  have hXDi : ∀ ω, LocallyIntegrable (XD ω) volume := by
    intro ω
    exact (hXhi ω).sub (hX0i ω)
  have hTsplit (ω : Disorder) :
      Distribution.ofFun ⊤ (Xh ω) volume ⊤ =
        Distribution.ofFun ⊤ (X0 ω) volume ⊤ +
          Distribution.ofFun ⊤ (XD ω) volume ⊤ := by
    have hsum : Xh ω = X0 ω + XD ω := by
      funext x
      simp [Xh, X0, XD]
    rw [hsum, Distribution.ofFun_add ((hX0i ω).locallyIntegrableOn _)
      ((hXDi ω).locallyIntegrableOn _)]
  have hpoint (ω : Disorder) :
      localNegSobolevSq a (Distribution.ofFun ⊤ (Xh ω) volume ⊤) χ ≤
        2 * (K + localNegSobolevSq a (Distribution.ofFun ⊤ (X0 ω) volume ⊤) χ) := by
    rw [hTsplit ω]
    let E0 := localNegSobolevENorm a (Distribution.ofFun ⊤ (X0 ω) volume ⊤) χ
    let ED := localNegSobolevENorm a (Distribution.ofFun ⊤ (XD ω) volume ⊤) χ
    have htri : localNegSobolevENorm a
        (Distribution.ofFun ⊤ (X0 ω) volume ⊤ + Distribution.ofFun ⊤ (XD ω) volume ⊤) χ ≤
          E0 + ED := by
      exact localNegSobolevENorm_add_le a _ _ χ
    have hpow : (E0 + ED) ^ (2 : ℝ) ≤
        2 * (E0 ^ (2 : ℝ) + ED ^ (2 : ℝ)) := by
      have h := ENNReal.rpow_add_le_mul_rpow_add_rpow E0 ED
        (p := (2 : ℝ)) (by norm_num)
      rw [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at h
      simpa only [ENNReal.rpow_two] using h
    have hE0sq : E0 ^ (2 : ℝ) =
        localNegSobolevSq a (Distribution.ofFun ⊤ (X0 ω) volume ⊤) χ := by
      dsimp [E0]
      rw [ENNReal.rpow_two, localNegSobolevENorm_sq]
    have hEDsq : ED ^ (2 : ℝ) =
        localNegSobolevSq a (Distribution.ofFun ⊤ (XD ω) volume ⊤) χ := by
      dsimp [ED]
      rw [ENNReal.rpow_two, localNegSobolevENorm_sq]
    calc
      _ = localNegSobolevENorm a
          (Distribution.ofFun ⊤ (X0 ω) volume ⊤ + Distribution.ofFun ⊤ (XD ω) volume ⊤) χ ^ 2 :=
        (localNegSobolevENorm_sq a _ χ).symm
      _ ≤ (E0 + ED) ^ (2 : ℝ) := by
        simpa only [ENNReal.rpow_two] using
          (ENNReal.rpow_le_rpow htri (by norm_num : (0 : ℝ) ≤ 2))
      _ ≤ 2 * (E0 ^ (2 : ℝ) + ED ^ (2 : ℝ)) := hpow
      _ ≤ 2 * (localNegSobolevSq a (Distribution.ofFun ⊤ (X0 ω) volume ⊤) χ + K) := by
        rw [hE0sq, hEDsq]
        exact mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (by simpa [XD, Xh, X0] using hDenergy N hNpos ω)) bot_le
      _ = 2 * (K + localNegSobolevSq a (Distribution.ofFun ⊤ (X0 ω) volume ⊤) χ) := by
        congr 1
        exact add_comm _ _
  calc
    _ ≤ ∫⁻ ω, 2 * (K + localNegSobolevSq a
        (Distribution.ofFun ⊤ (X0 ω) volume ⊤) χ) ∂disorderLaw := by
      apply lintegral_mono
      intro ω
      exact hpoint ω
    _ = 2 * (K + ∫⁻ ω, localNegSobolevSq a
          (Distribution.ofFun ⊤ (X0 ω) volume ⊤) χ ∂disorderLaw) := by
      rw [lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
        lintegral_add_left (measurable_const : Measurable (fun _ : Disorder => K))]
      simp
    _ ≤ 2 * (K + ENNReal.ofReal C₀) := by
      exact mul_le_mul_of_nonneg_left (add_le_add_right hflat K) bot_le
    _ = ENNReal.ofReal (2 * (C₀ + K.toReal)) := by
      calc
        _ = 2 * (ENNReal.ofReal K.toReal + ENNReal.ofReal C₀) := by
          rw [ENNReal.ofReal_toReal hKtop.ne]
        _ = 2 * ENNReal.ofReal (K.toReal + C₀) := by
          rw [← ENNReal.ofReal_add ENNReal.toReal_nonneg hC₀]
        _ = ENNReal.ofReal (2 * (K.toReal + C₀)) := by
          have htwo : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
          rw [htwo, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        _ = _ := by
          congr 1
          ring

end Critical2DKPZ.LocalSobolev

end
