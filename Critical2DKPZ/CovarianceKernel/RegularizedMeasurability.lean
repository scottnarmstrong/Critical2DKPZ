/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.RegularizedSpecification
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Moments.Covariance

/-! # Almost everywhere measurability of regularized covariance kernels -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction Topology

universe u

namespace Critical2DKPZ.CovarianceKernel

/-- The spatial regularized covariance kernel is almost everywhere measurable. -/
theorem regCovKernel_aemeasurable_of
    (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : LocalSobolev.ShfSymmetriesAt ϑ P Z)
    (hrevL : SmallScales.ShfReversalLawAt P Z)
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) :
    AEMeasurable (fun z => regCovKernel P Z t δ z) volume := by
  classical
  let X : Ω × Plane → ℝ := fun p => kpzRegularized P Z t δ 0 p.2 p.1
  have hXstrong : AEStronglyMeasurable X (P.prod volume) := by
    simpa only [X] using
      kpzRegularized_joint_aestronglyMeasurable_of ϑ P Z hZ hδ hδt
  obtain ⟨B, hB, hMom⟩ := kpzRegularized_uniform_second_moment_of
    ϑ P Z hZ hsym hrevL hδ hδt
  let c : ℝ := ∫ ω, swappedHeatStartLog Z t δ 0 ω ∂P
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
  obtain ⟨Y, hYmeas, hXY, hYmom, N, hNmeas, hNzero, hNsection⟩ :=
    measurable_field_modification_of_pointwise_moments P X hXstrong B hB hMomX hzeroX
  let Yfield : Ω → Plane → ℝ := fun ω x => Y (ω, x)
  have hYmem (x : Plane) : MemLp (fun ω => Y (ω, x)) 2 P := (hYmom x).1
  have hYzero (x : Plane) : (∫ ω, Y (ω, x) ∂P) = 0 := (hYmom x).2.2.2
  have hNae : ∀ᵐ x ∂volume, x ∉ N := by
    rw [ae_iff]
    simpa using hNzero
  obtain ⟨y, hy⟩ := hNae.exists
  have hPres : MeasurePreserving (fun z : Plane => z + y) volume volume :=
    measurePreserving_add_right volume y
  have hshiftNull : volume ((fun z : Plane => z + y) ⁻¹' N) = 0 := by
    calc
      volume ((fun z : Plane => z + y) ⁻¹' N) = (volume.map (fun z : Plane => z + y)) N := by
        rw [Measure.map_apply hPres.measurable hNmeas]
      _ = volume N := congrArg (fun μ : Measure Plane => μ N) hPres.map_eq
      _ = 0 := hNzero
  have hshift : ∀ᵐ z ∂volume, z + y ∉ N := by
    have hbad : {z : Plane | ¬ z + y ∉ N} = (fun z : Plane => z + y) ⁻¹' N := by
      ext z
      simp
    rw [ae_iff, hbad]
    exact hshiftNull
  let F : Plane × Ω → ℝ := fun p => Yfield p.2 (p.1 + y) * Yfield p.2 y
  have hYswap : Measurable (fun p : Plane × Ω => Yfield p.2 p.1) := by
    simpa only [Yfield, Function.comp_def, Prod.swap] using hYmeas.comp measurable_swap
  have hFmeas : Measurable F := by
    dsimp [F]
    exact (hYswap.comp (by fun_prop : Measurable (fun p : Plane × Ω => (p.1 + y, p.2)))).mul
      (hYswap.comp (by fun_prop : Measurable (fun p : Plane × Ω => (y, p.2))))
  let G : Plane → ℝ := fun z => ∫ ω, F (z, ω) ∂P
  have hGmeas : Measurable G := by
    exact hFmeas.stronglyMeasurable.integral_prod_right'.measurable
  have hG_eq (z : Plane) (hz : z + y ∉ N) :
      G z = regCovKernel P Z t δ z := by
    let x : Plane := z + y
    have hcovY : cov[fun ω => Y (ω, x), fun ω => Y (ω, y); P] =
        cov[kpzRegularized P Z t δ 0 x, kpzRegularized P Z t δ 0 y; P] :=
      covariance_congr_ae P (hYmem x) (hYmem y)
        (hMom x).1 (hMom y).1 (hNsection x hz) (hNsection y hy)
    have hprod : cov[fun ω => Y (ω, x), fun ω => Y (ω, y); P] =
        ∫ ω, Y (ω, x) * Y (ω, y) ∂P := by
      rw [covariance_eq_sub (hYmem x) (hYmem y), hYzero x, hYzero y]
      simp
    have htranslate := kpzRegularized_covariance_translate_of
      ϑ P Z hZ hsym hrevL hδ hδt x y
    have hdiff : x - y = z := by dsimp [x]; abel
    calc
      G z = ∫ ω, Y (ω, x) * Y (ω, y) ∂P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        simp [F, Yfield, x]
      _ = cov[fun ω => Y (ω, x), fun ω => Y (ω, y); P] := hprod.symm
      _ = cov[kpzRegularized P Z t δ 0 x, kpzRegularized P Z t δ 0 y; P] := hcovY
      _ = cov[kpzRegularized P Z t δ 0 z, kpzRegularized P Z t δ 0 0; P] := by
        rw [htranslate, hdiff]
      _ = regCovKernel P Z t δ z := by
        rw [covariance_comm]
        rfl
  have hEq : (fun z => regCovKernel P Z t δ z) =ᵐ[volume] G := by
    filter_upwards [hshift] with z hz
    exact (hG_eq z hz).symm
  exact hGmeas.aemeasurable.congr hEq.symm

end Critical2DKPZ.CovarianceKernel

end
