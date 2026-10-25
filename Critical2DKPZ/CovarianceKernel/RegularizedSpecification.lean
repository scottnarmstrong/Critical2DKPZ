/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.CovarianceFubini
public import Critical2DKPZ.JointConvergence.LogHeatFieldMeasurability
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Moments.Covariance
import Mathlib.Tactic

/-! # Covariance specification for the regularized field -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open scoped BoundedContinuousFunction Topology

universe u

namespace Critical2DKPZ.CovarianceKernel

/-- A homeomorphic pushforward of a locally finite measure is locally finite. -/
theorem locallyFinite_map_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y] [BorelSpace Y]
    (e : X ≃ₜ Y) (μ : Measure X) (hμ : IsLocallyFiniteMeasure μ) :
    IsLocallyFiniteMeasure (μ.map e) := by
  refine ⟨fun y => ?_⟩
  rcases (hμ.finiteAtNhds (e.symm y)).exists_mem_basis
      (nhds_basis_opens (e.symm y)) with ⟨U, ⟨hmem, hUopen⟩, hUfinite⟩
  refine ⟨e '' U, (e.isOpenMap U hUopen).mem_nhds ?_, ?_⟩
  · exact ⟨e.symm y, hmem, e.apply_symm_apply y⟩
  · rw [Measure.map_apply e.continuous.measurable (e.isOpenMap U hUopen).measurableSet]
    have hpre : e ⁻¹' (e '' U) = U := by
      ext x
      constructor
      · rintro ⟨x', hx', heq⟩
        exact e.injective heq ▸ hx'
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [hpre]
    exact hUfinite

/-- A jointly a.e. measurable field can be replaced on a spatial null set by a measurable field
whose pointwise moment and mean identities hold everywhere. -/
theorem measurable_field_modification_of_pointwise_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω × Plane → ℝ) (hX : AEStronglyMeasurable X (P.prod volume))
    (B : ℝ) (hB : 0 ≤ B)
    (hMom : ∀ x : Plane, MemLp (fun ω => X (ω, x)) 2 P ∧
      Integrable (fun ω => X (ω, x) ^ 2) P ∧
      (∫ ω, X (ω, x) ^ 2 ∂P) ≤ B)
    (hZero : ∀ x : Plane, (∫ ω, X (ω, x) ∂P) = 0) :
    ∃ Y : Ω × Plane → ℝ, Measurable Y ∧ X =ᵐ[P.prod volume] Y ∧
      (∀ x : Plane, MemLp (fun ω => Y (ω, x)) 2 P ∧
        Integrable (fun ω => Y (ω, x) ^ 2) P ∧
        (∫ ω, Y (ω, x) ^ 2 ∂P) ≤ B ∧
        (∫ ω, Y (ω, x) ∂P) = 0) ∧
      ∃ N : Set Plane, MeasurableSet N ∧ volume N = 0 ∧
        ∀ x ∉ N, (fun ω => Y (ω, x)) =ᵐ[P] fun ω => X (ω, x) := by
  classical
  let hXAEM := hX.aemeasurable
  let X₀ : Ω × Plane → ℝ := hXAEM.mk X
  have hX₀meas : Measurable X₀ := hXAEM.measurable_mk
  have hXX₀ : X =ᵐ[P.prod volume] X₀ := hXAEM.ae_eq_mk
  have hXX₀swap : (fun p : Plane × Ω => X (p.2, p.1)) =ᵐ[volume.prod P]
      fun p => X₀ (p.2, p.1) := by
    simpa [Function.comp_def, Prod.swap] using
      (measurePreserving_swap (μ := volume) (ν := P)).quasiMeasurePreserving.ae_eq_comp hXX₀
  have hsections : ∀ᵐ x ∂volume,
      (fun ω => X (ω, x)) =ᵐ[P] fun ω => X₀ (ω, x) := by
    exact ae_ae_of_ae_prod hXX₀swap
  let bad : Set Plane := {x | ¬ ((fun ω => X (ω, x)) =ᵐ[P] fun ω => X₀ (ω, x))}
  have hbadnull : volume bad = 0 := by
    apply (ae_iff).mp
    filter_upwards [hsections] with x hx
    simpa only [bad, not_not] using hx
  obtain ⟨N, hbadN, hNmeas, hNzero⟩ := exists_measurable_superset_of_null hbadnull
  let Y : Ω × Plane → ℝ := fun p => if p.2 ∈ N then 0 else X₀ p
  have hYmeas : Measurable Y := by
    dsimp [Y]
    exact Measurable.ite (hNmeas.preimage measurable_snd) measurable_const hX₀meas
  have hNae : ∀ᵐ x ∂volume, x ∉ N := by
    rw [ae_iff]
    simpa using hNzero
  have hNprod : ∀ᵐ p ∂P.prod volume, p.2 ∉ N := by
    have hset : MeasurableSet {p : Ω × Plane | p.2 ∉ N} :=
      hNmeas.compl.preimage measurable_snd
    rw [ae_prod_iff_ae_ae hset]
    filter_upwards [] with ω
    exact hNae
  have hXY : Y =ᵐ[P.prod volume] X := by
    filter_upwards [hNprod, hXX₀] with p hpN hpEq
    simp [Y, hpN]
    exact hpEq.symm
  have hYsection (x : Plane) (hxN : x ∉ N) :
      (fun ω => Y (ω, x)) =ᵐ[P] fun ω => X (ω, x) := by
    have hxBad : x ∉ bad := fun hx => hxN (hbadN hx)
    have hxRep : (fun ω => X (ω, x)) =ᵐ[P] fun ω => X₀ (ω, x) := by
      by_contra h
      exact hxBad h
    filter_upwards [hxRep] with ω hω
    simp [Y, hxN]
    exact hω.symm
  refine ⟨Y, hYmeas, hXY.symm, ?_, ⟨N, hNmeas, hNzero, ?_⟩⟩
  intro x
  by_cases hxN : x ∈ N
  · have hmem : MemLp (fun ω => Y (ω, x)) 2 P := by simp [Y, hxN]
    have hsquare : Integrable (fun ω => Y (ω, x) ^ 2) P := by simp [Y, hxN]
    have hmean : (∫ ω, Y (ω, x) ∂P) = 0 := by simp [Y, hxN]
    exact ⟨hmem, hsquare, by simpa [Y, hxN] using hB, hmean⟩
  · have hEq := hYsection x hxN
    have hmem : MemLp (fun ω => Y (ω, x)) 2 P := MemLp.ae_eq hEq.symm (hMom x).1
    have hEqSq : (fun ω => Y (ω, x) ^ 2) =ᵐ[P] fun ω => X (ω, x) ^ 2 :=
      hEq.mono fun ω hω => congrArg (fun r : ℝ => r ^ 2) hω
    have hsquare : Integrable (fun ω => Y (ω, x) ^ 2) P :=
      (hMom x).2.1.congr hEqSq.symm
    have hbound : (∫ ω, Y (ω, x) ^ 2 ∂P) ≤ B := by
      rw [integral_congr_ae hEqSq]
      exact (hMom x).2.2
    have hmean : (∫ ω, Y (ω, x) ∂P) = 0 := by
      rw [integral_congr_ae hEq]
      exact hZero x
    exact ⟨hmem, hsquare, hbound, hmean⟩
  intro x hxN
  exact hYsection x hxN

/-- Two pairs of square-integrable random variables that agree almost everywhere have the same
covariance. -/
theorem covariance_congr_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X X' Y Y' : Ω → ℝ}
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hX' : MemLp X' 2 P) (hY' : MemLp Y' 2 P)
    (hXX' : X =ᵐ[P] X') (hYY' : Y =ᵐ[P] Y') :
    cov[X, Y; P] = cov[X', Y'; P] := by
  rw [covariance_eq_sub hX hY, covariance_eq_sub hX' hY']
  have hprod : (fun ω => X ω * Y ω) =ᵐ[P] fun ω => X' ω * Y' ω := hXX'.mul hYY'
  congr 1
  · exact integral_congr_ae hprod
  · rw [integral_congr_ae hXX', integral_congr_ae hYY']

/-- The regularized field has a jointly measurable version in its probability and spatial
variables. -/
theorem kpzRegularized_joint_aestronglyMeasurable_of
    (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) :
    AEStronglyMeasurable
      (fun p : Ω × Plane => kpzRegularized P Z t δ 0 p.2 p.1) (P.prod volume) := by
  let T : ℝ := t - δ
  let M : Ω → Measure (Plane × Plane) := fun ω => Z 0 T ω
  let S : Ω → Measure (Plane × Plane) := fun ω => (M ω).map Prod.swap
  let c : ℝ := ∫ ω, swappedHeatStartLog Z t δ 0 ω ∂P
  have hTpos : 0 < T := by dsimp [T]; linarith
  have hMmeas : Measurable M := hZ.1 0 T le_rfl hTpos
  have hSmeas : Measurable S := by
    exact (Measure.measurable_map Prod.swap measurable_swap).comp hMmeas
  have hSlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (S ω) := by
    filter_upwards [hZ.2.1 0 T le_rfl hTpos] with ω hω
    exact locallyFinite_map_homeomorph (Homeomorph.prodComm Plane Plane) (M ω) hω.1
  have hVmeas : AEMeasurable
      (fun q : Plane × Ω => swappedHeatStartLog Z t δ q.1 q.2) (volume.prod P) := by
    have h := JointConvergence.aemeasurable_log_heatPairing_joint P S hSmeas hSlocal
      δ hδ (fun _ : Plane => (1 : ℝ)) measurable_const (fun _ => by norm_num)
    simpa [swappedHeatStartLog, S, M, T] using h
  have hVswap : AEStronglyMeasurable
      (fun p : Ω × Plane => swappedHeatStartLog Z t δ p.2 p.1) (P.prod volume) := by
    simpa only [Function.comp_def, Prod.swap] using
      hVmeas.aestronglyMeasurable.comp_measurePreserving
        (measurePreserving_swap (μ := P) (ν := volume))
  let X : Ω × Plane → ℝ := fun p => kpzRegularized P Z t δ 0 p.2 p.1
  have hXstrong : AEStronglyMeasurable X (P.prod volume) := by
    have hbase : AEStronglyMeasurable
        (fun p : Ω × Plane => swappedHeatStartLog Z t δ p.2 p.1 - c) (P.prod volume) :=
      hVswap.sub aestronglyMeasurable_const
    apply hbase.congr
    filter_upwards [] with p
    exact (congrFun (kpzRegularized_eq_swappedHeatStartLog_sub_mean P Z p.2) p.1).symm
  simpa only [X] using hXstrong

/-- The regularized covariance is translation invariant and its test-function pairing is the
corresponding integral against the difference kernel. -/
theorem regCovKernel_spec_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : LocalSobolev.ShfSymmetriesAt ϑ P Z)
    (hrevL : SmallScales.ShfReversalLawAt P Z)
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) :
    (∀ x y : Plane, cov[kpzRegularized P Z t δ 0 x, kpzRegularized P Z t δ 0 y; P] =
      regCovKernel P Z t δ (x - y)) ∧
    ∀ f g : TestFn,
      cov[fun ω => ∫ x, f x * kpzRegularized P Z t δ 0 x ω,
          fun ω => ∫ x, g x * kpzRegularized P Z t δ 0 x ω; P] =
        ∫ p : Plane × Plane, f p.1 * g p.2 * regCovKernel P Z t δ (p.1 - p.2) := by
  classical
  let c : ℝ := ∫ ω, swappedHeatStartLog Z t δ 0 ω ∂P
  let X : Ω × Plane → ℝ := fun p => kpzRegularized P Z t δ 0 p.2 p.1
  obtain ⟨B, hB, hMom⟩ := kpzRegularized_uniform_second_moment_of
    ϑ P Z hZ hsym hrevL hδ hδt
  have hlogMem : MemLp (swappedHeatStartLog Z t δ 0) 2 P :=
    swappedHeatStartLog_memLp_two_of ϑ P Z hZ hsym hrevL hδ hδt 0
  have hmean0 : (∫ ω, kpzRegularized P Z t δ 0 0 ω ∂P) = 0 := by
    rw [kpzRegularized_eq_swappedHeatStartLog_sub_mean P Z 0]
    rw [integral_sub (hlogMem.integrable (by norm_num)) (integrable_const c)]
    simp [c]
  have hzero (x : Plane) :
      (∫ ω, kpzRegularized P Z t δ 0 x ω ∂P) = 0 := by
    have hident := kpzRegularized_identDistrib_translate_of
      ϑ P Z hZ hsym hδ hδt x x
    have hident0 : IdentDistrib (kpzRegularized P Z t δ 0 x)
        (kpzRegularized P Z t δ 0 0) P P := by
      simpa only [sub_self] using hident
    exact hident0.integral_eq.trans hmean0
  have hXstrong : AEStronglyMeasurable X (P.prod volume) := by
    simpa only [X] using
      kpzRegularized_joint_aestronglyMeasurable_of ϑ P Z hZ hδ hδt
  have hMomX (x : Plane) :
      MemLp (fun ω => X (ω, x)) 2 P ∧
        Integrable (fun ω => X (ω, x) ^ 2) P ∧
        (∫ ω, X (ω, x) ^ 2 ∂P) ≤ B := by
    have hm := hMom x
    have heq : (fun ω => X (ω, x)) = kpzRegularized P Z t δ 0 x := by
      funext ω
      rfl
    rw [heq]
    exact ⟨hm.1, hm.2.1, le_of_eq hm.2.2⟩
  have hzeroX (x : Plane) : (∫ ω, X (ω, x) ∂P) = 0 := by
    simpa only [X] using hzero x
  obtain ⟨Y, hYmeas, hXY, hYmom, hN, hNmeas, hNzero, hNsection⟩ :=
    measurable_field_modification_of_pointwise_moments P X hXstrong B hB hMomX hzeroX
  let Yfield : Ω → Plane → ℝ := fun ω x => Y (ω, x)
  have hYmem (x : Plane) : MemLp (fun ω => Y (ω, x)) 2 P := (hYmom x).1
  have hYsq (x : Plane) : Integrable (fun ω => Y (ω, x) ^ 2) P ∧
      (∫ ω, Y (ω, x) ^ 2 ∂P) ≤ B := ⟨(hYmom x).2.1, (hYmom x).2.2.1⟩
  have hYzero (x : Plane) : (∫ ω, Y (ω, x) ∂P) = 0 := (hYmom x).2.2.2
  have hNae : ∀ᵐ x ∂volume, x ∉ hN := by
    rw [ae_iff]
    simpa using hNzero
  have hSectionCov (x y : Plane) (hx : x ∉ hN) (hy : y ∉ hN) :
      cov[fun ω => Y (ω, x), fun ω => Y (ω, y); P] =
        regCovKernel P Z t δ (x - y) := by
    calc
      cov[fun ω => Y (ω, x), fun ω => Y (ω, y); P] =
          cov[kpzRegularized P Z t δ 0 x, kpzRegularized P Z t δ 0 y; P] :=
        covariance_congr_ae P (hYmem x) (hYmem y) (hMom x).1 (hMom y).1
          (hNsection x hx) (hNsection y hy)
      _ = cov[kpzRegularized P Z t δ 0 (x - y), kpzRegularized P Z t δ 0 0; P] :=
        kpzRegularized_covariance_translate_of ϑ P Z hZ hsym hrevL hδ hδt x y
      _ = regCovKernel P Z t δ (x - y) := by
        rw [covariance_comm]
        rfl
  constructor
  · intro x y
    calc
      cov[kpzRegularized P Z t δ 0 x, kpzRegularized P Z t δ 0 y; P] =
          cov[kpzRegularized P Z t δ 0 (x - y), kpzRegularized P Z t δ 0 0; P] :=
        kpzRegularized_covariance_translate_of ϑ P Z hZ hsym hrevL hδ hδt x y
      _ = regCovKernel P Z t δ (x - y) := by
        rw [covariance_comm]
        rfl
  · intro f g
    have hYjoint : Measurable (fun p : Ω × Plane => Yfield p.1 p.2) := by
      simpa only [Yfield] using hYmeas
    have hfmeas (f : TestFn) : Measurable f := f.continuous.measurable
    have hfAbs (f : TestFn) : Integrable (fun x => |f x|) volume :=
      (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport).norm
    obtain ⟨hFYmem, hGYmem, _hKernelInt, hCovY⟩ := covariance_test_integral_eq_of
      P Yfield hYjoint hYmem B hYsq hYzero f g
        (hfmeas f) (hfmeas g) (hfAbs f) (hfAbs g)
    let UF : Ω → ℝ := fun ω => ∫ x, f x * kpzRegularized P Z t δ 0 x ω
    let UG : Ω → ℝ := fun ω => ∫ x, g x * kpzRegularized P Z t δ 0 x ω
    let VY : Ω → ℝ := fun ω => ∫ x, f x * Yfield ω x
    let WY : Ω → ℝ := fun ω => ∫ x, g x * Yfield ω x
    have hXYsections : ∀ᵐ ω ∂P, ∀ᵐ x ∂volume, X (ω, x) = Y (ω, x) :=
      Measure.ae_ae_of_ae_prod hXY
    have hUFae : UF =ᵐ[P] VY := by
      filter_upwards [hXYsections] with ω hω
      apply integral_congr_ae
      filter_upwards [hω] with x hx
      simpa [UF, VY, Yfield, X] using congrArg (fun r : ℝ => f x * r) hx
    have hUGae : UG =ᵐ[P] WY := by
      filter_upwards [hXYsections] with ω hω
      apply integral_congr_ae
      filter_upwards [hω] with x hx
      simpa [UG, WY, Yfield, X] using congrArg (fun r : ℝ => g x * r) hx
    have hVYmem : MemLp VY 2 P := by
      simpa [VY, Yfield, Function.uncurry_apply_pair] using hFYmem
    have hWYmem : MemLp WY 2 P := by
      simpa [WY, Yfield, Function.uncurry_apply_pair] using hGYmem
    have hUFmem : MemLp UF 2 P := MemLp.ae_eq hUFae.symm hVYmem
    have hUGmem : MemLp UG 2 P := MemLp.ae_eq hUGae.symm hWYmem
    have hCovRaw : cov[UF, UG; P] = cov[VY, WY; P] :=
      covariance_congr_ae P hUFmem hUGmem hVYmem hWYmem hUFae hUGae
    have hNfst : ∀ᵐ p : Plane × Plane ∂(volume.prod volume), p.1 ∉ hN := by
      change ∀ᵐ p : Plane × Plane ∂(volume.prod volume), p.1 ∈ hNᶜ
      rw [ae_prod_iff_ae_ae (hNmeas.compl.preimage measurable_fst)]
      filter_upwards [hNae] with x hx
      filter_upwards [] with _
      simpa using hx
    have hNsnd : ∀ᵐ p : Plane × Plane ∂(volume.prod volume), p.2 ∉ hN := by
      change ∀ᵐ p : Plane × Plane ∂(volume.prod volume), p.2 ∈ hNᶜ
      rw [ae_prod_iff_ae_ae (hNmeas.compl.preimage measurable_snd)]
      filter_upwards [] with x
      simpa using hNae
    have hKernelAE :
        (fun p : Plane × Plane => f p.1 * g p.2 *
            cov[fun ω => Y (ω, p.1), fun ω => Y (ω, p.2); P]) =ᵐ[volume.prod volume]
          fun p => f p.1 * g p.2 * regCovKernel P Z t δ (p.1 - p.2) := by
      filter_upwards [hNfst, hNsnd] with p hp hp'
      exact congrArg (fun q : ℝ => f p.1 * g p.2 * q) (hSectionCov p.1 p.2 hp hp')
    calc
      cov[UF, UG; P] = cov[VY, WY; P] := hCovRaw
      _ = ∫ p : Plane × Plane,
          f p.1 * g p.2 * cov[fun ω => Y (ω, p.1), fun ω => Y (ω, p.2); P] := hCovY
      _ = ∫ p : Plane × Plane, f p.1 * g p.2 * regCovKernel P Z t δ (p.1 - p.2) :=
        integral_congr_ae hKernelAE

end Critical2DKPZ.CovarianceKernel

end
