/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.PointwiseMoments
public import Critical2DKPZ.Assembly.RegularizedInvariance
public import Critical2DKPZ.SHF.Symmetries.DenseTransport

/-! # Rotation covariance of the regularized KPZ field -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction Topology

namespace Critical2DKPZ.CovarianceKernel

/-- The covariance kernel of the regularized field inherits rotation invariance from the stochastic heat flow. -/
theorem regCovKernel_rotation_of_shfSymmetries
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : LocalSobolev.ShfSymmetriesAt ϑ P Z)
    (hrevL : SmallScales.ShfReversalLawAt P Z)
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t)
    (R : Plane ≃ₗᵢ[ℝ] Plane)
    (hdet : LinearMap.det (R.toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1)
    (z : Plane) :
    regCovKernel P Z t δ z = regCovKernel P Z t δ (R.symm z) := by
  let ZR : ℝ → ℝ → Ω → Measure (Plane × Plane) := fun s u ω =>
    (Z s u ω).map (fun p => (R p.1, R p.2))
  let T : ℝ := t - δ
  have hT : 0 < T := by dsimp [T]; linarith
  have hZR : IsCriticalSHF ϑ P ZR := by
    simpa [ZR] using hsym.2.1 R hdet
  let xloc : Fin 2 → Plane := ![0, z]
  let Q : (Fin 2 → Measure (Plane × Plane)) → Fin 2 → ℝ := fun m i =>
    Real.log (∫ p, heatKernel δ (p.1 - xloc i) ∂((m i).map Prod.swap))
  have hQ : Measurable Q := by
    apply measurable_pi_iff.mpr
    intro i
    change Measurable (fun m : Fin 2 → Measure (Plane × Plane) =>
      Real.log (∫ p, heatKernel δ (p.1 - xloc i) ∂((m i).map Prod.swap)))
    exact (measurable_log_heatPairingMeasure δ hδ (xloc i)).comp
      ((Measure.measurable_map Prod.swap measurable_swap).comp (measurable_pi_apply i))
  let M : Ω → Fin 2 → Measure (Plane × Plane) := fun ω _ => Z 0 T ω
  let MR : Ω → Fin 2 → Measure (Plane × Plane) := fun ω _ => ZR 0 T ω
  have hM : Measurable M := by
    apply measurable_pi_iff.mpr
    intro i
    exact hZ.1 0 T le_rfl hT
  have hMR : Measurable MR := by
    apply measurable_pi_iff.mpr
    intro i
    exact hZR.1 0 T le_rfl hT
  have hZlaw := SHF.Symmetries.isCriticalSHF_fdd_eq ϑ P P Z ZR hZ hZR 2
    (fun _ => 0) (fun _ => T) (by
      intro i
      exact ⟨le_rfl, hT⟩)
  have hQlaw : P.map (fun ω => Q (M ω)) = P.map (fun ω => Q (MR ω)) := by
    calc
      P.map (fun ω => Q (M ω)) = (P.map M).map Q :=
        (AEMeasurable.map_map_of_aemeasurable (μ := P)
          hQ.aemeasurable hM.aemeasurable).symm
      _ = (P.map MR).map Q := by rw [hZlaw]
      _ = P.map (fun ω => Q (MR ω)) :=
        AEMeasurable.map_map_of_aemeasurable (μ := P)
          hQ.aemeasurable hMR.aemeasurable
  let V : Ω → Fin 2 → ℝ := fun ω => Q (M ω)
  let VR : Ω → Fin 2 → ℝ := fun ω => Q (MR ω)
  have hVlaw : P.map V = P.map VR := by exact hQlaw
  have hcovLaw : cov[fun v : Fin 2 → ℝ => v 0, fun v => v 1; P.map V] =
      cov[fun v : Fin 2 → ℝ => v 0, fun v => v 1; P.map VR] :=
    congrArg (fun μ : Measure (Fin 2 → ℝ) =>
      cov[fun v : Fin 2 → ℝ => v 0, fun v => v 1; μ]) hVlaw
  have hcovV : cov[fun v : Fin 2 → ℝ => v 0, fun v => v 1; P.map V] =
      cov[fun ω => V ω 0, fun ω => V ω 1; P] :=
    ProbabilityTheory.covariance_map_fun (measurable_pi_apply 0).aestronglyMeasurable
      (measurable_pi_apply 1).aestronglyMeasurable (hQ.comp hM).aemeasurable
  have hcovVR : cov[fun v : Fin 2 → ℝ => v 0, fun v => v 1; P.map VR] =
      cov[fun ω => VR ω 0, fun ω => VR ω 1; P] :=
    ProbabilityTheory.covariance_map_fun (measurable_pi_apply 0).aestronglyMeasurable
      (measurable_pi_apply 1).aestronglyMeasurable (hQ.comp hMR).aemeasurable
  have hcoordV0 : (fun ω => V ω 0) = swappedHeatStartLog Z t δ 0 := by
    funext ω
    simp [V, Q, M, xloc, swappedHeatStartLog, T]
  have hcoordV1 : (fun ω => V ω 1) = swappedHeatStartLog Z t δ z := by
    funext ω
    simp [V, Q, M, xloc, swappedHeatStartLog, T]
  have hcoordVR0 : (fun ω => VR ω 0) = swappedHeatStartLog ZR t δ 0 := by
    funext ω
    simp [VR, Q, MR, xloc, swappedHeatStartLog, T]
  have hcoordVR1 : (fun ω => VR ω 1) = swappedHeatStartLog ZR t δ z := by
    funext ω
    simp [VR, Q, MR, xloc, swappedHeatStartLog, T]
  have hlogs :
      cov[swappedHeatStartLog Z t δ 0, swappedHeatStartLog Z t δ z; P] =
      cov[swappedHeatStartLog ZR t δ 0, swappedHeatStartLog ZR t δ z; P] := by
    calc
      cov[swappedHeatStartLog Z t δ 0, swappedHeatStartLog Z t δ z; P] =
          cov[fun ω => V ω 0, fun ω => V ω 1; P] := by rw [hcoordV0, hcoordV1]
      _ = cov[fun ω => VR ω 0, fun ω => VR ω 1; P] := hcovV.symm.trans (hcovLaw.trans hcovVR)
      _ = cov[swappedHeatStartLog ZR t δ 0, swappedHeatStartLog ZR t δ z; P] := by
            rw [hcoordVR0, hcoordVR1]
  have hlogMem (w : Plane) : MemLp (swappedHeatStartLog Z t δ w) 2 P :=
    swappedHeatStartLog_memLp_two_of ϑ P Z hZ hsym hrevL hδ hδt w
  have hvecIdent : IdentDistrib V VR P P :=
    ⟨(hQ.comp hM).aemeasurable, (hQ.comp hMR).aemeasurable, hVlaw⟩
  have hlogMemR (i : Fin 2) : MemLp (fun ω => VR ω i) 2 P := by
    have hIdent := hvecIdent.comp (measurable_pi_apply i)
    have hbase : MemLp (fun ω => V ω i) 2 P := by
      fin_cases i
      · change MemLp (fun ω => V ω 0) 2 P
        rw [hcoordV0]
        exact hlogMem 0
      · change MemLp (fun ω => V ω 1) 2 P
        rw [hcoordV1]
        exact hlogMem z
    exact hIdent.memLp_snd hbase
  let F : Plane → Ω → ℝ := fun w => kpzRegularized P Z t δ 0 w
  let FR : Plane → Ω → ℝ := fun w => kpzRegularized P ZR t δ 0 w
  have hcenterZ (w₁ w₂ : Plane) :
      cov[F w₁, F w₂; P] =
        cov[swappedHeatStartLog Z t δ w₁, swappedHeatStartLog Z t δ w₂; P] := by
    have heq₁ : F w₁ = kpzRegularized P Z t δ 0 w₁ := rfl
    have heq₂ : F w₂ = kpzRegularized P Z t δ 0 w₂ := rfl
    rw [heq₁, heq₂, kpzRegularized_eq_swappedHeatStartLog_sub_mean P Z w₁,
      kpzRegularized_eq_swappedHeatStartLog_sub_mean P Z w₂]
    rw [covariance_sub_const_left ((hlogMem w₁).integrable (by norm_num)),
      covariance_sub_const_right ((hlogMem w₂).integrable (by norm_num))]
  have hcenterR :
      cov[FR 0, FR z; P] = cov[swappedHeatStartLog ZR t δ 0,
        swappedHeatStartLog ZR t δ z; P] := by
    have heq₁ : FR 0 = kpzRegularized P ZR t δ 0 0 := rfl
    have heq₂ : FR z = kpzRegularized P ZR t δ 0 z := rfl
    rw [heq₁, heq₂, kpzRegularized_eq_swappedHeatStartLog_sub_mean P ZR 0,
      kpzRegularized_eq_swappedHeatStartLog_sub_mean P ZR z]
    have hmem0 : MemLp (swappedHeatStartLog ZR t δ 0) 2 P := by
      rw [← hcoordVR0]
      exact hlogMemR 0
    have hmem1 : MemLp (swappedHeatStartLog ZR t δ z) 2 P := by
      rw [← hcoordVR1]
      exact hlogMemR 1
    rw [covariance_sub_const_left (hmem0.integrable (by norm_num)),
      covariance_sub_const_right (hmem1.integrable (by norm_num))]
  have hFmem (w : Plane) : MemLp (F w) 2 P :=
    kpzRegularized_point_memLp_two_of ϑ P Z hZ hsym hrevL hδ hδt w
  let cZ : ℝ := ∫ ω, Real.log (shfPairing Z 0 (t - δ) (fun _ => 1)
    (fun y => heatKernel δ y) ω) ∂P
  let cZR : ℝ := ∫ ω, Real.log (shfPairing ZR 0 (t - δ) (fun _ => 1)
    (fun y => heatKernel δ y) ω) ∂P
  let d : ℝ := cZ - cZR
  have hFrot0 : FR 0 = fun ω => F 0 ω + d := by
    funext ω
    have h := Assembly.kpzRegularized_compAffine_pointwise P Z t δ 0 R 0 ω
    have h' : FR 0 ω = F 0 ω + cZ - cZR := by
      simpa [FR, F, ZR, cZ, cZR] using h
    change FR 0 ω = F 0 ω + (cZ - cZR)
    rw [h']
    ring
  have hFrotz : FR z = fun ω => F (R.symm z) ω + d := by
    funext ω
    have h := Assembly.kpzRegularized_compAffine_pointwise P Z t δ 0 R z ω
    have h' : FR z ω = F (R.symm z) ω + cZ - cZR := by
      simpa [FR, F, ZR, cZ, cZR] using h
    change FR z ω = F (R.symm z) ω + (cZ - cZR)
    rw [h']
    ring
  have htrans : cov[FR 0, FR z; P] = cov[F 0, F (R.symm z); P] := by
    rw [hFrot0, hFrotz]
    rw [covariance_add_const_left ((hFmem 0).integrable (by norm_num)) d,
      covariance_add_const_right ((hFmem (R.symm z)).integrable (by norm_num)) d]
  calc
    regCovKernel P Z t δ z = cov[F 0, F z; P] := rfl
    _ = cov[FR 0, FR z; P] := (hcenterZ 0 z).trans (hlogs.trans hcenterR.symm)
    _ = cov[F 0, F (R.symm z); P] := htrans
    _ = regCovKernel P Z t δ (R.symm z) := rfl

end Critical2DKPZ.CovarianceKernel

end
