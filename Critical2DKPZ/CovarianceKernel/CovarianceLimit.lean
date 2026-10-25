/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.PointwiseMoments
import Mathlib.Probability.Moments.Covariance
import Mathlib.Tactic

/-! # Translation covariance for regularized flat fields -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction Topology

namespace Critical2DKPZ.CovarianceKernel

private theorem integral_heatKernel_translate_swap (δ : ℝ) (x z : Plane)
    (μ : Measure (Plane × Plane)) :
    (∫ p, heatKernel δ (p.1 - x) ∂((μ.map (fun p => (p.1 + z, p.2 + z))).map Prod.swap)) =
      ∫ p, heatKernel δ (p.1 - (x - z)) ∂(μ.map Prod.swap) := by
  let τ : Plane × Plane → Plane × Plane := fun p => (p.1 + z, p.2 + z)
  let f : Plane × Plane → ℝ := fun p => heatKernel δ (p.1 - x)
  have hτ : Measurable τ := by dsimp [τ]; fun_prop
  have hf : Measurable f := by
    dsimp [f]
    exact (measurable_heatKernel δ).comp (measurable_fst.sub_const x)
  have h1 : (∫ p, f p ∂((μ.map τ).map Prod.swap)) =
      ∫ p, f (Prod.swap p) ∂(μ.map τ) :=
    integral_map (μ := μ.map τ) measurable_swap.aemeasurable
      hf.aestronglyMeasurable
  have h2 : (∫ p, f (Prod.swap p) ∂(μ.map τ)) =
      ∫ p, f (Prod.swap (τ p)) ∂μ :=
    integral_map (μ := μ) hτ.aemeasurable
      (hf.comp measurable_swap).aestronglyMeasurable
  have h3 : (∫ p, heatKernel δ (p.1 - (x - z)) ∂(μ.map Prod.swap)) =
      ∫ p, heatKernel δ ((Prod.swap p).1 - (x - z)) ∂μ :=
    integral_map (μ := μ) measurable_swap.aemeasurable
      ((measurable_heatKernel δ).comp (measurable_fst.sub_const (x - z))).aestronglyMeasurable
  calc
    (∫ p, heatKernel δ (p.1 - x) ∂((μ.map τ).map Prod.swap)) =
        ∫ p, f (Prod.swap p) ∂(μ.map τ) := by simpa [f] using h1
    _ = ∫ p, f (Prod.swap (τ p)) ∂μ := h2
    _ = ∫ p, heatKernel δ ((Prod.swap p).1 - (x - z)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with p
      change heatKernel δ ((Prod.swap (τ p)).1 - x) =
        heatKernel δ ((Prod.swap p).1 - (x - z))
      have harg : (Prod.swap (τ p)).1 - x = (Prod.swap p).1 - (x - z) := by
        simp [τ]
        abel
      rw [harg]
    _ = ∫ p, heatKernel δ (p.1 - (x - z)) ∂(μ.map Prod.swap) := h3.symm


/-- Joint translation invariance of the swapped heat-start logarithms preserves their covariance. -/
theorem swappedHeatStartLog_covariance_translate_of
    {Ω : Type*} [MeasurableSpace Ω] (ϑ : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : LocalSobolev.ShfSymmetriesAt ϑ P Z)
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (x y z : Plane) :
    cov[swappedHeatStartLog Z t δ x, swappedHeatStartLog Z t δ y; P] =
      cov[swappedHeatStartLog Z t δ (x - z), swappedHeatStartLog Z t δ (y - z); P] := by
  let T : ℝ := t - δ
  let τ : Plane × Plane → Plane × Plane := fun p => (p.1 + z, p.2 + z)
  let M : Ω → Measure (Plane × Plane) := fun ω => Z 0 T ω
  let Mz : Ω → Measure (Plane × Plane) := fun ω => (M ω).map τ
  let Qx : Measure (Plane × Plane) → ℝ := fun μ =>
    Real.log (∫ p, heatKernel δ (p.1 - x) ∂μ)
  let Qy : Measure (Plane × Plane) → ℝ := fun μ =>
    Real.log (∫ p, heatKernel δ (p.1 - y) ∂μ)
  let F : Measure (Plane × Plane) → ℝ × ℝ := fun μ =>
    (Qx (μ.map Prod.swap), Qy (μ.map Prod.swap))
  have hTpos : 0 < T := by dsimp [T]; linarith
  have hMmeas : Measurable M := hZ.1 0 T le_rfl hTpos
  have hτ : Measurable τ := by dsimp [τ]; fun_prop
  have hMzmeas : Measurable Mz := (Measure.measurable_map τ hτ).comp hMmeas
  have hQx : Measurable Qx := by
    dsimp [Qx]
    exact measurable_log_heatPairingMeasure δ hδ x
  have hQy : Measurable Qy := by
    dsimp [Qy]
    exact measurable_log_heatPairingMeasure δ hδ y
  have hF : Measurable F := by
    dsimp [F]
    exact Measurable.prodMk (hQx.comp (Measure.measurable_map Prod.swap measurable_swap))
      (hQy.comp (Measure.measurable_map Prod.swap measurable_swap))
  have hLaw := shfInterval_translate_law_of ϑ P Z hZ hsym z hTpos
  have hPairLaw : P.map (fun ω => F (M ω)) = P.map (fun ω => F (Mz ω)) := by
    calc
      P.map (fun ω => F (M ω)) = (P.map M).map F :=
        (AEMeasurable.map_map_of_aemeasurable (μ := P)
          hF.aemeasurable hMmeas.aemeasurable).symm
      _ = (P.map Mz).map F := by rw [hLaw]
      _ = P.map (fun ω => F (Mz ω)) :=
        AEMeasurable.map_map_of_aemeasurable (μ := P)
          hF.aemeasurable hMzmeas.aemeasurable
  have hXmap : cov[Prod.fst, Prod.snd; P.map (fun ω => F (M ω))] =
      cov[fun ω => swappedHeatStartLog Z t δ x ω,
        fun ω => swappedHeatStartLog Z t δ y ω; P] := by
    have h := ProbabilityTheory.covariance_map_fun
      (μ := P) (X := Prod.fst) (Y := Prod.snd)
      (Z := fun ω => F (M ω))
      measurable_fst.aestronglyMeasurable measurable_snd.aestronglyMeasurable
      ((hF.comp hMmeas).aemeasurable)
    simpa [F, Qx, Qy, M, T, swappedHeatStartLog] using h
  have hYmap : cov[Prod.fst, Prod.snd; P.map (fun ω => F (Mz ω))] =
      cov[fun ω => swappedHeatStartLog Z t δ (x - z) ω,
        fun ω => swappedHeatStartLog Z t δ (y - z) ω; P] := by
    have h := ProbabilityTheory.covariance_map_fun
      (μ := P) (X := Prod.fst) (Y := Prod.snd)
      (Z := fun ω => F (Mz ω))
      measurable_fst.aestronglyMeasurable measurable_snd.aestronglyMeasurable
      ((hF.comp hMzmeas).aemeasurable)
    have hqx (ω : Ω) : Qx ((Mz ω).map Prod.swap) =
        swappedHeatStartLog Z t δ (x - z) ω := by
      dsimp [Qx, Mz, M, τ]
      unfold swappedHeatStartLog
      exact congrArg Real.log
        (integral_heatKernel_translate_swap δ x z (Z 0 T ω))
    have hqy (ω : Ω) : Qy ((Mz ω).map Prod.swap) =
        swappedHeatStartLog Z t δ (y - z) ω := by
      dsimp [Qy, Mz, M, τ]
      unfold swappedHeatStartLog
      exact congrArg Real.log
        (integral_heatKernel_translate_swap δ y z (Z 0 T ω))
    simpa only [F, hqx, hqy] using h
  calc
    cov[swappedHeatStartLog Z t δ x, swappedHeatStartLog Z t δ y; P] =
        cov[Prod.fst, Prod.snd; P.map (fun ω => F (M ω))] := hXmap.symm
    _ = cov[Prod.fst, Prod.snd; P.map (fun ω => F (Mz ω))] := by rw [hPairLaw]
    _ = cov[swappedHeatStartLog Z t δ (x - z),
        swappedHeatStartLog Z t δ (y - z); P] := hYmap

/-- Translation invariance of the SHF implies that the covariance of the centered regularized
field depends only on the difference of its spatial arguments. -/
theorem kpzRegularized_covariance_translate_of
    {Ω : Type*} [MeasurableSpace Ω] (ϑ : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : LocalSobolev.ShfSymmetriesAt ϑ P Z)
    (hrevL : SmallScales.ShfReversalLawAt P Z)
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (x y : Plane) :
    cov[kpzRegularized P Z t δ 0 x, kpzRegularized P Z t δ 0 y; P] =
      cov[kpzRegularized P Z t δ 0 (x - y), kpzRegularized P Z t δ 0 0; P] := by
  let c : ℝ := ∫ ω, swappedHeatStartLog Z t δ 0 ω ∂P
  have hfield (w : Plane) : kpzRegularized P Z t δ 0 w =
      fun ω => swappedHeatStartLog Z t δ w ω - c := by
    simpa [c] using kpzRegularized_eq_swappedHeatStartLog_sub_mean P Z w
  have hmem (w : Plane) : MemLp (swappedHeatStartLog Z t δ w) 2 P :=
    swappedHeatStartLog_memLp_two_of ϑ P Z hZ hsym hrevL hδ hδt w
  have hcov (u v : Plane) :
      cov[kpzRegularized P Z t δ 0 u, kpzRegularized P Z t δ 0 v; P] =
        cov[swappedHeatStartLog Z t δ u, swappedHeatStartLog Z t δ v; P] := by
    rw [hfield u, hfield v]
    rw [covariance_sub_const_left ((hmem u).integrable (by norm_num)) c]
    exact covariance_sub_const_right ((hmem v).integrable (by norm_num)) c
  calc
    cov[kpzRegularized P Z t δ 0 x, kpzRegularized P Z t δ 0 y; P] =
        cov[swappedHeatStartLog Z t δ x, swappedHeatStartLog Z t δ y; P] := hcov x y
    _ = cov[swappedHeatStartLog Z t δ (x - y), swappedHeatStartLog Z t δ 0; P] :=
      by simpa only [sub_self] using
        swappedHeatStartLog_covariance_translate_of ϑ P Z hZ hsym hδ hδt x y y
    _ = cov[kpzRegularized P Z t δ 0 (x - y), kpzRegularized P Z t δ 0 0; P] :=
      (hcov (x - y) 0).symm

/-- The centered regularized field has a spatially translation-invariant one-point law. -/
theorem kpzRegularized_identDistrib_translate_of
    {Ω : Type*} [MeasurableSpace Ω] (ϑ : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : LocalSobolev.ShfSymmetriesAt ϑ P Z)
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (x z : Plane) :
    IdentDistrib (kpzRegularized P Z t δ 0 x)
      (kpzRegularized P Z t δ 0 (x - z)) P P := by
  let T : ℝ := t - δ
  let τ : Plane × Plane → Plane × Plane := fun p => (p.1 + z, p.2 + z)
  let M : Ω → Measure (Plane × Plane) := fun ω => Z 0 T ω
  let Mz : Ω → Measure (Plane × Plane) := fun ω => (M ω).map τ
  let Q : Plane → Measure (Plane × Plane) → ℝ := fun w μ =>
    Real.log (∫ p, heatKernel δ (p.1 - w) ∂(μ.map Prod.swap))
  let c : ℝ := ∫ ω, Q 0 (M ω) ∂P
  have hTpos : 0 < T := by dsimp [T]; linarith
  have hMmeas : Measurable M := hZ.1 0 T le_rfl hTpos
  have hτ : Measurable τ := by dsimp [τ]; fun_prop
  have hMzmeas : Measurable Mz := (Measure.measurable_map τ hτ).comp hMmeas
  have hQmeas (w : Plane) : Measurable (Q w) := by
    dsimp [Q]
    exact (measurable_log_heatPairingMeasure δ hδ w).comp
      (Measure.measurable_map Prod.swap measurable_swap)
  have hLaw := shfInterval_translate_law_of ϑ P Z hZ hsym z hTpos
  have hMapLaw : P.map (fun ω => Q x (M ω)) = P.map (fun ω => Q x (Mz ω)) := by
    calc
      P.map (fun ω => Q x (M ω)) = (P.map M).map (Q x) :=
        (AEMeasurable.map_map_of_aemeasurable (μ := P)
          (hQmeas x).aemeasurable hMmeas.aemeasurable).symm
      _ = (P.map Mz).map (Q x) := by rw [hLaw]
      _ = P.map (fun ω => Q x (Mz ω)) :=
        AEMeasurable.map_map_of_aemeasurable (μ := P)
          (hQmeas x).aemeasurable hMzmeas.aemeasurable
  have hshift (ω : Ω) : Q x (Mz ω) = Q (x - z) (M ω) := by
    dsimp [Q, Mz, M, τ]
    exact congrArg Real.log (integral_heatKernel_translate_swap δ x z (Z 0 T ω))
  have hPointLaw : P.map (fun ω => Q x (M ω)) =
      P.map (fun ω => Q (x - z) (M ω)) := by
    rw [hMapLaw, Measure.map_congr (Filter.Eventually.of_forall hshift)]
  have hQid : IdentDistrib (fun ω => Q x (M ω))
      (fun ω => Q (x - z) (M ω)) P P :=
    ⟨(hQmeas x).comp hMmeas |>.aemeasurable,
      (hQmeas (x - z)).comp hMmeas |>.aemeasurable, hPointLaw⟩
  have hfield (w : Plane) : kpzRegularized P Z t δ 0 w =
      fun ω => Q w (M ω) - c := by
    simpa [Q, M, c, T, swappedHeatStartLog] using
      kpzRegularized_eq_swappedHeatStartLog_sub_mean P Z w
  have hshifted := hQid.comp (measurable_sub_const c)
  rw [hfield x, hfield (x - z)]
  change IdentDistrib ((fun r : ℝ => r - c) ∘ (fun ω => Q x (M ω)))
    ((fun r : ℝ => r - c) ∘ (fun ω => Q (x - z) (M ω))) P P
  exact hshifted

/-- The pointwise second moment of the regularized flat field is finite and independent of its
spatial center. -/
theorem kpzRegularized_uniform_second_moment_of
    {Ω : Type*} [MeasurableSpace Ω] (ϑ : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : LocalSobolev.ShfSymmetriesAt ϑ P Z)
    (hrevL : SmallScales.ShfReversalLawAt P Z)
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Plane,
      MemLp (kpzRegularized P Z t δ 0 x) 2 P ∧
        Integrable (fun ω => kpzRegularized P Z t δ 0 x ω ^ 2) P ∧
        (∫ ω, kpzRegularized P Z t δ 0 x ω ^ 2 ∂P) = B := by
  let X : Plane → Ω → ℝ := fun x => kpzRegularized P Z t δ 0 x
  have hmem0 : MemLp (X 0) 2 P :=
    kpzRegularized_point_memLp_two_of ϑ P Z hZ hsym hrevL hδ hδt 0
  refine ⟨∫ ω, X 0 ω ^ 2 ∂P, integral_nonneg (fun ω => sq_nonneg (X 0 ω)), ?_⟩
  intro x
  have hident : IdentDistrib (X x) (X 0) P P := by
    simpa [X, sub_self] using
      kpzRegularized_identDistrib_translate_of ϑ P Z hZ hsym hδ hδt x x
  have hmemx : MemLp (X x) 2 P := by
    exact hident.symm.memLp_snd hmem0
  have hsqx := hmemx.integrable_sq
  have hs0 := hmem0.integrable_sq
  have hpow := hident.comp (measurable_id.pow_const 2)
  have hsqeq : (∫ ω, X x ω ^ 2 ∂P) = ∫ ω, X 0 ω ^ 2 ∂P := by
    simpa [X] using hpow.integral_eq
  exact ⟨hmemx, hsqx, hsqeq.trans rfl⟩

end Critical2DKPZ.CovarianceKernel

end
