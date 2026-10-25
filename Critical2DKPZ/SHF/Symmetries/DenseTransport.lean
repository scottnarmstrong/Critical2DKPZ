/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.Defs
public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.RandomMeasure.PlanePairInterface
public import Critical2DKPZ.SHF.Tsai.Products
public import Critical2DKPZ.SHF.Tsai.TensorMoments
public import Critical2DKPZ.SHF.DeltaBose.SpatialTransport
public import Critical2DKPZ.SHF.DeltaBose.EndpointSymmetry
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Critical2DKPZ.SHF.Symmetries.DenseTransportHelpers
public import Critical2DKPZ.SHF.Symmetries.DenseTransportComposition
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Dense-time SHF law transport and symmetry lemmas -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Tsai
open scoped Topology ENNReal CompactlySupported

namespace Critical2DKPZ.SHF.Symmetries

private def configTranslate (n : ℕ) (z : Plane) :
    DeltaBose.Configuration n ≃ᵐ DeltaBose.Configuration n :=
  MeasurableEquiv.piCongrRight (fun _ : Fin n => MeasurableEquiv.addRight z)

private def configLinearIsometry (n : ℕ) (R : Plane ≃ₗᵢ[ℝ] Plane) :
    DeltaBose.Configuration n ≃ᵐ DeltaBose.Configuration n :=
  MeasurableEquiv.piCongrRight (fun _ : Fin n => R.toHomeomorph.toMeasurableEquiv)

private theorem measurePreserving_configTranslate (n : ℕ) (z : Plane) :
    MeasurePreserving (configTranslate n z) volume volume := by
  exact volume_preserving_pi fun _ : Fin n => measurePreserving_add_right volume z

private theorem measurePreserving_configLinearIsometry (n : ℕ)
    (R : Plane ≃ₗᵢ[ℝ] Plane) :
    MeasurePreserving (configLinearIsometry n R) volume volume := by
  exact volume_preserving_pi fun _ : Fin n => R.measurePreserving

private theorem memLp_translate {g : Plane → ℝ} (z : Plane) (hg : MemLp g 2) :
    MemLp (fun x => g (x + z)) 2 := by
  have h := hg.comp_measurePreserving (measurePreserving_add_right volume z)
  simpa only [Function.comp_def] using h

private theorem memLp_linearIsometry {g : Plane → ℝ}
    (R : Plane ≃ₗᵢ[ℝ] Plane) (hg : MemLp g 2) :
    MemLp (fun x => g (R x)) 2 := by
  have h := hg.comp_measurePreserving R.measurePreserving
  simpa only [Function.comp_def] using h

private theorem integral_momentKernel_translate (n : ℕ) (θ h : ℝ)
    (z : Plane) (g g' : Fin n → Plane → ℝ) :
    (∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
      (∏ i, g i (x i + z)) * (DeltaBose.momentKernel n θ h x y).toReal *
        ∏ i, g' i (y i + z)) =
    ∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
      (∏ i, g i (x i)) * (DeltaBose.momentKernel n θ h x y).toReal *
        ∏ i, g' i (y i) := by
  let T := configTranslate n z
  let F : DeltaBose.Configuration n → DeltaBose.Configuration n → ℝ := fun x y =>
    (∏ i, g i (x i)) * (DeltaBose.momentKernel n θ h x y).toReal * ∏ i, g' i (y i)
  have hT : ∀ x, (T x : DeltaBose.Configuration n) = fun i => x i + z := by
    intro x
    funext i
    rfl
  have hKernel (x y : DeltaBose.Configuration n) :
      DeltaBose.momentKernel n θ h (T x) (T y) =
        DeltaBose.momentKernel n θ h x y := by
    rw [hT, hT]
    exact DeltaBose.momentKernel_translate n θ h x y z
  have hPoint (x y : DeltaBose.Configuration n) :
      (∏ i, g i (x i + z)) * (DeltaBose.momentKernel n θ h x y).toReal *
          ∏ i, g' i (y i + z) = F (T x) (T y) := by
    rw [hT, hT, ← hKernel]
    rfl
  calc
    _ = ∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
        F (T x) (T y) := by
      apply integral_congr_ae
      filter_upwards [] with x
      apply integral_congr_ae
      filter_upwards [] with y
      exact hPoint x y
    _ = ∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
        F (T x) y := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (measurePreserving_configTranslate n z).integral_comp' (F (T x))
    _ = ∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
        F x y := by
      exact (measurePreserving_configTranslate n z).integral_comp' (fun x => ∫ y, F x y)

private theorem integral_momentKernel_linearIsometry (n : ℕ) (θ h : ℝ)
    (R : Plane ≃ₗᵢ[ℝ] Plane) (g g' : Fin n → Plane → ℝ) :
    (∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
      (∏ i, g i (R (x i))) * (DeltaBose.momentKernel n θ h x y).toReal *
        ∏ i, g' i (R (y i))) =
    ∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
      (∏ i, g i (x i)) * (DeltaBose.momentKernel n θ h x y).toReal *
        ∏ i, g' i (y i) := by
  let T := configLinearIsometry n R
  let F : DeltaBose.Configuration n → DeltaBose.Configuration n → ℝ := fun x y =>
    (∏ i, g i (x i)) * (DeltaBose.momentKernel n θ h x y).toReal * ∏ i, g' i (y i)
  have hT : ∀ x, (T x : DeltaBose.Configuration n) = fun i => R (x i) := by
    intro x
    funext i
    rfl
  have hKernel (x y : DeltaBose.Configuration n) :
      DeltaBose.momentKernel n θ h (T x) (T y) =
        DeltaBose.momentKernel n θ h x y := by
    rw [hT, hT]
    exact DeltaBose.momentKernel_linearIsometry n R θ h x y
  have hPoint (x y : DeltaBose.Configuration n) :
      (∏ i, g i (R (x i))) * (DeltaBose.momentKernel n θ h x y).toReal *
          ∏ i, g' i (R (y i)) = F (T x) (T y) := by
    rw [hT, hT, ← hKernel]
    rfl
  calc
    _ = ∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
        F (T x) (T y) := by
      apply integral_congr_ae
      filter_upwards [] with x
      apply integral_congr_ae
      filter_upwards [] with y
      exact hPoint x y
    _ = ∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
        F (T x) y := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (measurePreserving_configLinearIsometry n R).integral_comp' (F (T x))
    _ = ∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
        F x y := by
      exact (measurePreserving_configLinearIsometry n R).integral_comp'
        (fun x => ∫ y, F x y)

private theorem integrable_pairing_map_translate (z : Plane)
    (μ : Measure (Plane × Plane)) (g g' : Plane → ℝ)
    (hI : Integrable (fun p : Plane × Plane => g (p.1 + z) * g' (p.2 + z)) μ) :
    Integrable (fun p : Plane × Plane => g p.1 * g' p.2)
      (μ.map (pairTranslateMeas z)) ∧
    ∫ p, g p.1 * g' p.2 ∂(μ.map (pairTranslateMeas z)) =
      ∫ p, g (p.1 + z) * g' (p.2 + z) ∂μ := by
  let e := pairTranslateMeas z
  let F : Plane × Plane → ℝ := fun p => g p.1 * g' p.2
  have hsource : Integrable (fun p => F (e p)) μ := by
    simpa [F, e, pairTranslateMeas, pairTranslate] using hI
  have htarget : Integrable F (μ.map e) := (integrable_map_equiv e F).2 hsource
  refine ⟨htarget, ?_⟩
  calc
    ∫ p, F p ∂(μ.map e) = ∫ p, F (e p) ∂μ :=
      integral_map e.measurable.aemeasurable htarget.aestronglyMeasurable
    _ = ∫ p, g (p.1 + z) * g' (p.2 + z) ∂μ := by
      apply integral_congr_ae
      filter_upwards with p
      rfl

private theorem momentClause_map_translate {θ : ℝ} {D : Set ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)}
    (hZ : IsDenseSHF θ D P Z) (z : Plane) :
    ∀ n : ℕ, 1 ≤ n → n ≤ 4 → ∀ s ∈ D, ∀ t ∈ D, s < t →
      ∀ g g' : Fin n → Plane → ℝ, (∀ i, MemLp (g i) 2) → (∀ i, MemLp (g' i) 2) →
        (∀ᵐ ω ∂P, ∀ i, Integrable
          (fun p : Plane × Plane => g i p.1 * g' i p.2)
          ((Z s t ω).map (pairTranslateMeas z))) ∧
        Integrable (fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2 ∂
          ((Z s t ω).map (pairTranslateMeas z))) P ∧
        ∫ ω, ∏ i, (∫ p, g i p.1 * g' i p.2 ∂
          ((Z s t ω).map (pairTranslateMeas z))) ∂P =
          ∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
            (∏ i, g i (x i)) * (DeltaBose.momentKernel n θ (t - s) x y).toReal *
              ∏ i, g' i (y i) := by
  intro n hn hn4 s hs t ht hst g g' hg hg'
  let gT : Fin n → Plane → ℝ := fun i x => g i (x + z)
  let g'T : Fin n → Plane → ℝ := fun i x => g' i (x + z)
  have hgT : ∀ i, MemLp (gT i) 2 := fun i => memLp_translate z (hg i)
  have hg'T : ∀ i, MemLp (g'T i) 2 := fun i => memLp_translate z (hg' i)
  have hsource := hZ.2.2.2 n hn hn4 s hs t ht hst gT g'T hgT hg'T
  rcases hsource with ⟨hInt, hProdInt, hMean⟩
  have hPairEq : (fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2 ∂
      ((Z s t ω).map (pairTranslateMeas z))) =ᵐ[P]
      fun ω => ∏ i, ∫ p, gT i p.1 * g'T i p.2 ∂Z s t ω := by
    filter_upwards [hInt] with ω hω
    apply Finset.prod_congr rfl
    intro i hi
    exact (integrable_pairing_map_translate z (Z s t ω) (g i) (g' i) (hω i)).2
  have hMean' : ∫ ω, ∏ i, (∫ p, g i p.1 * g' i p.2 ∂
      ((Z s t ω).map (pairTranslateMeas z))) ∂P =
      ∫ ω, ∏ i, (∫ p, gT i p.1 * g'T i p.2 ∂Z s t ω) ∂P := by
    exact integral_congr_ae hPairEq
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hInt] with ω hω
    intro i
    exact (integrable_pairing_map_translate z (Z s t ω) (g i) (g' i) (hω i)).1
  · exact hProdInt.congr hPairEq.symm
  · calc
      ∫ ω, ∏ i, (∫ p, g i p.1 * g' i p.2 ∂
          ((Z s t ω).map (pairTranslateMeas z))) ∂P =
        ∫ ω, ∏ i, (∫ p, gT i p.1 * g'T i p.2 ∂Z s t ω) ∂P := hMean'
      _ = ∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
          (∏ i, gT i (x i)) * (DeltaBose.momentKernel n θ (t - s) x y).toReal *
            ∏ i, g'T i (y i) := hMean
      _ = ∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
          (∏ i, g i (x i)) * (DeltaBose.momentKernel n θ (t - s) x y).toReal *
            ∏ i, g' i (y i) := integral_momentKernel_translate n θ (t - s) z g g'

private theorem momentClause_map_linearIsometry {θ : ℝ} {D : Set ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)}
    (hZ : IsDenseSHF θ D P Z) (R : Plane ≃ₗᵢ[ℝ] Plane) :
    ∀ n : ℕ, 1 ≤ n → n ≤ 4 → ∀ s ∈ D, ∀ t ∈ D, s < t →
      ∀ g g' : Fin n → Plane → ℝ, (∀ i, MemLp (g i) 2) → (∀ i, MemLp (g' i) 2) →
        (∀ᵐ ω ∂P, ∀ i, Integrable
          (fun p : Plane × Plane => g i p.1 * g' i p.2)
          ((Z s t ω).map (pairLinearIsometryMeas R))) ∧
        Integrable (fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2 ∂
          ((Z s t ω).map (pairLinearIsometryMeas R))) P ∧
        ∫ ω, ∏ i, (∫ p, g i p.1 * g' i p.2 ∂
          ((Z s t ω).map (pairLinearIsometryMeas R))) ∂P =
          ∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
            (∏ i, g i (x i)) * (DeltaBose.momentKernel n θ (t - s) x y).toReal *
              ∏ i, g' i (y i) := by
  intro n hn hn4 s hs t ht hst g g' hg hg'
  let gR : Fin n → Plane → ℝ := fun i x => g i (R x)
  let g'R : Fin n → Plane → ℝ := fun i x => g' i (R x)
  have hgR : ∀ i, MemLp (gR i) 2 := fun i => memLp_linearIsometry R (hg i)
  have hg'R : ∀ i, MemLp (g'R i) 2 := fun i => memLp_linearIsometry R (hg' i)
  have hsource := hZ.2.2.2 n hn hn4 s hs t ht hst gR g'R hgR hg'R
  rcases hsource with ⟨hInt, hProdInt, hMean⟩
  have hPairEq : (fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2 ∂
      ((Z s t ω).map (pairLinearIsometryMeas R))) =ᵐ[P]
      fun ω => ∏ i, ∫ p, gR i p.1 * g'R i p.2 ∂Z s t ω := by
    filter_upwards [hInt] with ω hω
    apply Finset.prod_congr rfl
    intro i hi
    exact (integrable_pairing_map_linearIsometry R (Z s t ω) (g i) (g' i)
      (hω i)).2
  have hMean' : ∫ ω, ∏ i, (∫ p, g i p.1 * g' i p.2 ∂
      ((Z s t ω).map (pairLinearIsometryMeas R))) ∂P =
      ∫ ω, ∏ i, (∫ p, gR i p.1 * g'R i p.2 ∂Z s t ω) ∂P :=
    integral_congr_ae hPairEq
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hInt] with ω hω
    intro i
    exact (integrable_pairing_map_linearIsometry R (Z s t ω) (g i) (g' i)
      (hω i)).1
  · exact hProdInt.congr hPairEq.symm
  · calc
      ∫ ω, ∏ i, (∫ p, g i p.1 * g' i p.2 ∂
          ((Z s t ω).map (pairLinearIsometryMeas R))) ∂P =
        ∫ ω, ∏ i, (∫ p, gR i p.1 * g'R i p.2 ∂Z s t ω) ∂P := hMean'
      _ = ∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
          (∏ i, gR i (x i)) * (DeltaBose.momentKernel n θ (t - s) x y).toReal *
            ∏ i, g'R i (y i) := hMean
      _ = ∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
          (∏ i, g i (x i)) * (DeltaBose.momentKernel n θ (t - s) x y).toReal *
            ∏ i, g' i (y i) :=
          integral_momentKernel_linearIsometry n θ (t - s) R g g'

private theorem smoothedProductPairing_map_translate (z : Plane)
    (μ ν : Measure (Plane × Plane)) [SFinite μ] [SFinite ν] (w : Plane → ℝ)
    (hw : Continuous w) (f : C_c(Plane × Plane, ℝ)) :
    smoothedProductPairing (μ.map (pairTranslateMeas z)) w
      (ν.map (pairTranslateMeas z)) f =
    smoothedProductPairing μ w ν (pairTranslateTest z f) := by
  let e := pairTranslateMeas z
  let E := e.prodCongr e
  let F : ((Plane × Plane) × (Plane × Plane)) → ℝ :=
    fun q => f (q.1.1, q.2.2) * w (q.1.2 - q.2.1)
  have hmap : (μ.map e).prod (ν.map e) = (μ.prod ν).map E := by
    exact Measure.map_prod_map μ ν e.measurable e.measurable
  have hFcont : Continuous F := by
    dsimp [F]
    fun_prop
  unfold smoothedProductPairing
  rw [hmap]
  calc
    ∫ q, F q ∂(Measure.map E (μ.prod ν)) = ∫ q, F (E q) ∂(μ.prod ν) :=
      integral_map E.measurable.aemeasurable
        (hFcont.measurable.aestronglyMeasurable)
    _ = ∫ q, (pairTranslateTest z f) (q.1.1, q.2.2) * w (q.1.2 - q.2.1) ∂(μ.prod ν) := by
      apply integral_congr_ae
      filter_upwards with q
      have hEapply : E q = ((q.1.1 + z, q.1.2 + z), (q.2.1 + z, q.2.2 + z)) := by
        change (e q.1, e q.2) = _
        rw [pairTranslateMeas_apply, pairTranslateMeas_apply]
      rw [hEapply]
      dsimp [F]
      rw [pairTranslateTest_apply, add_sub_add_right_eq_sub]

private theorem smoothedProductWellDefined_map_translate (z : Plane)
    (μ ν : Measure (Plane × Plane)) [SFinite μ] [SFinite ν]
    (w : Plane → ℝ)
    (hdef : SmoothedProductWellDefined μ w ν) :
    SmoothedProductWellDefined (μ.map (pairTranslateMeas z)) w
      (ν.map (pairTranslateMeas z)) := by
  intro f
  let e := pairTranslateMeas z
  let E := e.prodCongr e
  let F : ((Plane × Plane) × (Plane × Plane)) → ℝ :=
    fun q => f (q.1.1, q.2.2) * w (q.1.2 - q.2.1)
  have hmap : (μ.map e).prod (ν.map e) = (μ.prod ν).map E := by
    exact Measure.map_prod_map μ ν e.measurable e.measurable
  have hsource : Integrable (fun q => F (E q)) (μ.prod ν) := by
    have h := hdef (pairTranslateTest z f)
    apply h.congr
    filter_upwards [] with q
    have hEapply : E q = ((q.1.1 + z, q.1.2 + z), (q.2.1 + z, q.2.2 + z)) := by
      change (e q.1, e q.2) = _
      rw [pairTranslateMeas_apply, pairTranslateMeas_apply]
    rw [hEapply]
    dsimp [F]
    rw [pairTranslateTest_apply, add_sub_add_right_eq_sub]
  rw [hmap]
  exact (integrable_map_equiv E F).2 hsource

private theorem criticalSHF_pairing_law {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (ϑ : ℝ) (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) (hZ' : IsCriticalSHF ϑ P' Z')
    (k : ℕ) (s t : Fin k → ℝ) (hst : ∀ i, 0 ≤ s i ∧ s i < t i)
    (φ : Fin k → C_c(Plane × Plane, ℝ)) :
    P.map (fun ω i => ∫ p, φ i p ∂Z (s i) (t i) ω) =
      P'.map (fun ω i => ∫ p, φ i p ∂Z' (s i) (t i) ω) := by
  let ψ : Fin k → C_c(Plane, ℝ) := fun _ => 0
  let first : (Fin k → ℝ × ℝ) → Fin k → ℝ := fun x i => (x i).1
  let hfirst : Continuous first := continuous_pi fun i =>
    (continuous_apply i).fst
  have hlimZ := hZ.2.2 k s t hst φ ψ
  have hlimZ' := hZ'.2.2 k s t hst φ ψ
  have hprojZ := hlimZ.continuous_comp hfirst
  have hprojZ' := hlimZ'.continuous_comp hfirst
  have hlaw := tendstoInDistribution_unique
    (fun N ω => first (fun i =>
      ((∫ p, φ i p * rescaledP2P ϑ N (s i) (t i) p ω),
        (∫ x, ψ i x * rescaledP2Plane ϑ N (s i) (t i) x ω)))) hprojZ hprojZ'
  simpa only [Function.comp_def, first] using hlaw


private theorem exists_stage_for_finite_family {ι : Type*} [Fintype ι]
    (Dm : ℕ → Set ℝ) (hmono : Monotone Dm) (t : ι → ℝ)
    (hmem : ∀ i, t i ∈ ⋃ m, Dm m) : ∃ m, ∀ i, t i ∈ Dm m := by
  classical
  choose mi hmi using fun i => Set.mem_iUnion.mp (hmem i)
  refine ⟨∑ i, mi i, ?_⟩
  intro i
  apply hmono ?_ (hmi i)
  exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)

/-- Translate the spatial endpoints of every random measure in a dense-time SHF. -/
theorem isDenseSHF_map_translate {θ : ℝ} {D : Set ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)}
    (hZ : IsDenseSHF θ D P Z) (z : Plane) :
    IsDenseSHF θ D P fun s t ω => (Z s t ω).map fun p => (p.1 + z, p.2 + z) := by
  rcases hZ with ⟨hpair, hcomp, hindep, hmom⟩
  have hmap : (fun p : Plane × Plane => (p.1 + z, p.2 + z)) = pairTranslateMeas z := by
    funext p
    exact (pairTranslateMeas_apply z p).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs t ht hst
    rcases measurable_aeLocallyFinite_pairTranslate P (Z s t)
      (hpair s hs t ht hst).1 (hpair s hs t ht hst).2 z with ⟨hmeas, hLF⟩
    exact ⟨by simpa only [hmap] using hmeas, by simpa only [hmap] using hLF⟩
  · intro t₀ ht₀ t₁ ht₁ t₂ ht₂ h01 h12
    rcases hcomp t₀ ht₀ t₁ ht₁ t₂ ht₂ h01 h12 with ⟨w, hw, hdef, hlim⟩
    refine ⟨w, hw, ?_, ?_⟩
    · intro ℓ
      filter_upwards [hdef ℓ, (hpair t₀ ht₀ t₁ ht₁ h01).2,
        (hpair t₁ ht₁ t₂ ht₂ h12).2] with ω hω hLF₁ hLF₂
      let _ : IsLocallyFiniteMeasure (Z t₀ t₁ ω) := hLF₁
      let _ : IsLocallyFiniteMeasure (Z t₁ t₂ ω) := hLF₂
      exact smoothedProductWellDefined_map_translate z (Z t₀ t₁ ω) (Z t₁ t₂ ω)
        (w ℓ) hω
    · intro f
      have hleft : ∀ ℓ, (fun ω =>
          smoothedProductPairing ((Z t₀ t₁ ω).map (pairTranslateMeas z)) (w ℓ)
            ((Z t₁ t₂ ω).map (pairTranslateMeas z)) f -
          ∫ p, f p ∂((Z t₀ t₂ ω).map (pairTranslateMeas z))) =ᵐ[P]
          fun ω => smoothedProductPairing (Z t₀ t₁ ω) (w ℓ) (Z t₁ t₂ ω)
            (pairTranslateTest z f) -
          ∫ p, pairTranslateTest z f p ∂(Z t₀ t₂ ω) := by
        intro ℓ
        filter_upwards [(hpair t₀ ht₀ t₁ ht₁ h01).2,
          (hpair t₁ ht₁ t₂ ht₂ h12).2, (hpair t₀ ht₀ t₂ ht₂ (lt_trans h01 h12)).2]
          with ω hLF₁ hLF₂ hLF₀
        let _ : IsLocallyFiniteMeasure (Z t₀ t₁ ω) := hLF₁
        let _ : IsLocallyFiniteMeasure (Z t₁ t₂ ω) := hLF₂
        let _ : IsLocallyFiniteMeasure (Z t₀ t₂ ω) := hLF₀
        rw [smoothedProductPairing_map_translate z (Z t₀ t₁ ω) (Z t₁ t₂ ω)
          (w ℓ) (hw.2.1 ℓ) f]
        rw [(integral_pairTranslateTest_map z (Z t₀ t₂ ω) f).2]
      exact TendstoInMeasure.congr
        (fun ℓ => by simpa only [← hmap] using (hleft ℓ).symm) EventuallyEq.rfl
        (hlim (pairTranslateTest z f))
  · intro k t hstrict ht
    have h := iIndepFun_map_pairTranslate (hindep k t hstrict ht) z
    simpa only [Function.comp_def, hmap] using h
  · simpa only [hmap] using
      momentClause_map_translate ⟨hpair, hcomp, hindep, hmom⟩ z

/-- Push every random measure in a dense-time SHF through a common linear isometry. -/
theorem isDenseSHF_map_linearIsometry {θ : ℝ} {D : Set ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)}
    (hZ : IsDenseSHF θ D P Z) (R : Plane ≃ₗᵢ[ℝ] Plane) :
    IsDenseSHF θ D P fun s t ω => (Z s t ω).map fun p => (R p.1, R p.2) := by
  rcases hZ with ⟨hpair, hcomp, hindep, hmom⟩
  have hmap : (fun p : Plane × Plane => (R p.1, R p.2)) = pairLinearIsometryMeas R := by
    funext p
    exact (pairLinearIsometryMeas_apply R p).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs t ht hst
    rcases measurable_aeLocallyFinite_pairLinearIsometry P (Z s t)
      (hpair s hs t ht hst).1 (hpair s hs t ht hst).2 R with ⟨hmeas, hLF⟩
    exact ⟨by simpa only [hmap] using hmeas, by simpa only [hmap] using hLF⟩
  · intro t₀ ht₀ t₁ ht₁ t₂ ht₂ h01 h12
    rcases hcomp t₀ ht₀ t₁ ht₁ t₂ ht₂ h01 h12 with ⟨w, hw, hdef, hlim⟩
    let wR := mollifierLinearIsometry R w
    have hwR : IsL2ApplicableMollifier wR := isL2ApplicableMollifier_linearIsometry hw R
    refine ⟨wR, hwR, ?_, ?_⟩
    · intro ℓ
      filter_upwards [hdef ℓ, (hpair t₀ ht₀ t₁ ht₁ h01).2,
        (hpair t₁ ht₁ t₂ ht₂ h12).2] with ω hω hLF₁ hLF₂
      let _ : IsLocallyFiniteMeasure (Z t₀ t₁ ω) := hLF₁
      let _ : IsLocallyFiniteMeasure (Z t₁ t₂ ω) := hLF₂
      exact smoothedProductWellDefined_map_linearIsometry R (Z t₀ t₁ ω) (Z t₁ t₂ ω)
        (w ℓ) hω
    · intro f
      have hleft : ∀ ℓ, (fun ω =>
          smoothedProductPairing ((Z t₀ t₁ ω).map (pairLinearIsometryMeas R)) (wR ℓ)
            ((Z t₁ t₂ ω).map (pairLinearIsometryMeas R)) f -
          ∫ p, f p ∂((Z t₀ t₂ ω).map (pairLinearIsometryMeas R))) =ᵐ[P]
          fun ω => smoothedProductPairing (Z t₀ t₁ ω) (w ℓ) (Z t₁ t₂ ω)
            (pairLinearIsometryTest R f) -
          ∫ p, pairLinearIsometryTest R f p ∂(Z t₀ t₂ ω) := by
        intro ℓ
        filter_upwards [(hpair t₀ ht₀ t₁ ht₁ h01).2,
          (hpair t₁ ht₁ t₂ ht₂ h12).2, (hpair t₀ ht₀ t₂ ht₂ (lt_trans h01 h12)).2]
          with ω hLF₁ hLF₂ hLF₀
        let _ : IsLocallyFiniteMeasure (Z t₀ t₁ ω) := hLF₁
        let _ : IsLocallyFiniteMeasure (Z t₁ t₂ ω) := hLF₂
        let _ : IsLocallyFiniteMeasure (Z t₀ t₂ ω) := hLF₀
        change smoothedProductPairing ((Z t₀ t₁ ω).map (pairLinearIsometryMeas R))
            (fun x => w ℓ (R.symm x)) ((Z t₁ t₂ ω).map (pairLinearIsometryMeas R)) f -
          ∫ p, f p ∂((Z t₀ t₂ ω).map (pairLinearIsometryMeas R)) = _
        rw [smoothedProductPairing_map_linearIsometry R (Z t₀ t₁ ω) (Z t₁ t₂ ω)
          (w ℓ) (hw.2.1 ℓ) f]
        rw [(integral_pairLinearIsometryTest_map R (Z t₀ t₂ ω) f).2]
      exact TendstoInMeasure.congr
        (fun ℓ => by simpa only [← hmap] using (hleft ℓ).symm) EventuallyEq.rfl
        (hlim (pairLinearIsometryTest R f))
  · intro k t hstrict ht
    have h := iIndepFun_map_pairLinearIsometry (hindep k t hstrict ht) R
    simpa only [Function.comp_def, hmap] using h
  · simpa only [hmap] using
      momentClause_map_linearIsometry ⟨hpair, hcomp, hindep, hmom⟩ R

/-- Reverse time intervals and exchange the two endpoints of every random measure. -/
theorem isDenseSHF_reverse {θ : ℝ} {D : Set ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)}
    (hZ : IsDenseSHF θ D P Z) (T : ℝ) :
    IsDenseSHF θ {s | T - s ∈ D} P fun s t ω => (Z (T - t) (T - s) ω).map Prod.swap := by
  rcases hZ with ⟨hpair, hcomp, hindep, hmom⟩
  have hmap : (fun p : Plane × Plane => Prod.swap p) = pairSwapMeas := by
    funext p
    exact (pairSwapMeas_apply p).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs t ht hst
    change T - s ∈ D at hs
    change T - t ∈ D at ht
    have hsource := hpair (T - t) ht (T - s) hs (by linarith)
    rcases measurable_aeLocallyFinite_pairSwap P (Z (T - t) (T - s))
      hsource.1 hsource.2 with ⟨hmeas, hLF⟩
    exact ⟨by simpa only [hmap] using hmeas, by simpa only [hmap] using hLF⟩
  · intro t₀ ht₀ t₁ ht₁ t₂ ht₂ h01 h12
    change T - t₀ ∈ D at ht₀
    change T - t₁ ∈ D at ht₁
    change T - t₂ ∈ D at ht₂
    let r₀ := T - t₂
    let r₁ := T - t₁
    let r₂ := T - t₀
    have hr₀ : r₀ ∈ D := ht₂
    have hr₁ : r₁ ∈ D := ht₁
    have hr₂ : r₂ ∈ D := ht₀
    have hr01 : r₀ < r₁ := by dsimp [r₀, r₁]; linarith
    have hr12 : r₁ < r₂ := by dsimp [r₁, r₂]; linarith
    rcases hcomp r₀ hr₀ r₁ hr₁ r₂ hr₂ hr01 hr12 with ⟨w, hw, hdef, hlim⟩
    have hmoll (ℓ : ℕ) : mollifierReverse w ℓ = (fun x => w ℓ (-x)) := rfl
    let wRev := mollifierReverse w
    have hwRev : IsL2ApplicableMollifier wRev := isL2ApplicableMollifier_reverse hw
    refine ⟨wRev, hwRev, ?_, ?_⟩
    · intro ℓ
      filter_upwards [hdef ℓ,
        (hpair r₁ hr₁ r₂ hr₂ hr12).2,
        (hpair r₀ hr₀ r₁ hr₁ hr01).2] with ω hω hLF₁ hLF₂
      let _ : IsLocallyFiniteMeasure (Z r₁ r₂ ω) := hLF₁
      let _ : IsLocallyFiniteMeasure (Z r₀ r₁ ω) := hLF₂
      exact smoothedProductWellDefined_map_pairSwap (Z r₁ r₂ ω) (Z r₀ r₁ ω)
        (w ℓ) hω
    · intro f
      have hleft : ∀ ℓ, (fun ω =>
          smoothedProductPairing ((Z r₁ r₂ ω).map pairSwapMeas)
            (fun x => w ℓ (-x)) ((Z r₀ r₁ ω).map pairSwapMeas) f -
          ∫ p, f p ∂((Z r₀ r₂ ω).map pairSwapMeas)) =ᵐ[P]
          fun ω => smoothedProductPairing (Z r₀ r₁ ω) (w ℓ) (Z r₁ r₂ ω)
            (pairSwapTest f) - ∫ p, pairSwapTest f p ∂(Z r₀ r₂ ω) := by
        intro ℓ
        filter_upwards [(hpair r₁ hr₁ r₂ hr₂ hr12).2,
          (hpair r₀ hr₀ r₁ hr₁ hr01).2,
          (hpair r₀ hr₀ r₂ hr₂ (lt_trans hr01 hr12)).2] with ω hLF₁ hLF₂ hLF₀
        let _ : IsLocallyFiniteMeasure (Z r₁ r₂ ω) := hLF₁
        let _ : IsLocallyFiniteMeasure (Z r₀ r₁ ω) := hLF₂
        let _ : IsLocallyFiniteMeasure (Z r₀ r₂ ω) := hLF₀
        rw [smoothedProductPairing_map_pairSwap (Z r₁ r₂ ω) (Z r₀ r₁ ω)
          (w ℓ) (hw.2.1 ℓ) f]
        rw [(integral_pairSwapTest_map (Z r₀ r₂ ω) f).2]
      exact TendstoInMeasure.congr
        (fun ℓ => by
          simpa only [← hmap, r₀, r₁, r₂, wRev, hmoll] using (hleft ℓ).symm)
        EventuallyEq.rfl
        (hlim (pairSwapTest f))
  · intro k t hstrict ht
    let u : Fin (k + 1) → ℝ := fun j => T - t (Fin.rev j)
    have huStrict : StrictMono u := by
      intro i j hij
      dsimp [u]
      have hrev : Fin.rev j < Fin.rev i := Fin.rev_lt_rev.mpr hij
      have htRev : t (Fin.rev j) < t (Fin.rev i) := hstrict hrev
      linarith
    have huMem : ∀ j, u j ∈ D := fun j => by
      dsimp [u]
      exact ht (Fin.rev j)
    have hsource := hindep k u huStrict huMem
    have hrevInd := hsource.precomp Fin.rev_injective
    have hswapInd := iIndepFun_map_pairSwap hrevInd
    have hrevLeft (i : Fin k) : Fin.rev ((Fin.rev i).castSucc) = i.succ := by
      apply Fin.ext
      simp only [Fin.val_rev, Fin.val_castSucc, Fin.val_succ]
      omega
    have hrevRight (i : Fin k) : Fin.rev ((Fin.rev i).succ) = i.castSucc := by
      apply Fin.ext
      simp only [Fin.val_rev, Fin.val_succ, Fin.val_castSucc]
      omega
    have huLeft (i : Fin k) : u (Fin.rev i).castSucc = T - t i.succ := by
      dsimp [u]
      rw [hrevLeft]
    have huRight (i : Fin k) : u (Fin.rev i).succ = T - t i.castSucc := by
      dsimp [u]
      rw [hrevRight]
    simpa only [Function.comp_def, huLeft, huRight, hmap] using hswapInd
  · intro n hn hn4 s hs t ht hst g g' hg hg'
    change T - s ∈ D at hs
    change T - t ∈ D at ht
    have hgap : (T - s) - (T - t) = t - s := by linarith
    have h := momentClause_map_pairSwap ⟨hpair, hcomp, hindep, hmom⟩ n hn hn4
      (T - t) ht (T - s) hs (by linarith) g g' hg hg'
    simpa only [hmap, hgap] using h

/-- The SHF conditions on an increasing union of time sets follow from the conditions on each member of the union. -/
theorem isDenseSHF_of_iUnion {θ : ℝ} {D : Set ℝ} (Dm : ℕ → Set ℝ) (hmono : Monotone Dm)
    (hD : D ⊆ ⋃ m, Dm m) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)} (h : ∀ m, IsDenseSHF θ (Dm m) P Z) :
    IsDenseSHF θ D P Z := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs t ht hst
    rcases Set.mem_iUnion.mp (hD hs) with ⟨ms, hms⟩
    rcases Set.mem_iUnion.mp (hD ht) with ⟨mt, hmt⟩
    exact (h (max ms mt)).1 s (hmono (Nat.le_max_left _ _) hms) t
      (hmono (Nat.le_max_right _ _) hmt) hst
  · intro t₀ ht₀ t₁ ht₁ t₂ ht₂ h01 h12
    rcases Set.mem_iUnion.mp (hD ht₀) with ⟨m₀, hm₀⟩
    rcases Set.mem_iUnion.mp (hD ht₁) with ⟨m₁, hm₁⟩
    rcases Set.mem_iUnion.mp (hD ht₂) with ⟨m₂, hm₂⟩
    let m := max m₀ (max m₁ m₂)
    have hm₀' : t₀ ∈ Dm m := hmono (Nat.le_max_left m₀ (max m₁ m₂)) hm₀
    have hm₁' : t₁ ∈ Dm m := hmono
      (le_trans (Nat.le_max_left m₁ m₂) (Nat.le_max_right m₀ (max m₁ m₂))) hm₁
    have hm₂' : t₂ ∈ Dm m := hmono
      (le_trans (Nat.le_max_right m₁ m₂) (Nat.le_max_right m₀ (max m₁ m₂))) hm₂
    exact (h m).2.1 t₀ hm₀' t₁ hm₁' t₂ hm₂' h01 h12
  · intro k t hstrict ht
    obtain ⟨m, hm⟩ := exists_stage_for_finite_family Dm hmono t (fun i => hD (ht i))
    exact (h m).2.2.1 k t hstrict hm
  · intro n hn hn4 s hs t ht hst g g' hg hg'
    rcases Set.mem_iUnion.mp (hD hs) with ⟨ms, hms⟩
    rcases Set.mem_iUnion.mp (hD ht) with ⟨mt, hmt⟩
    exact (h (max ms mt)).2.2.2 n hn hn4 s (hmono (Nat.le_max_left _ _) hms) t
      (hmono (Nat.le_max_right _ _) hmt) hst g g' hg hg'

/-- The SHF definition determines the joint laws of finitely many measure coordinates. -/
theorem isCriticalSHF_fdd_eq (ϑ : ℝ) {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) (hZ' : IsCriticalSHF ϑ P' Z') (k : ℕ)
    (s t : Fin k → ℝ) (hst : ∀ i, 0 ≤ s i ∧ s i < t i) :
    P.map (fun ω i => Z (s i) (t i) ω) = P'.map (fun ω i => Z' (s i) (t i) ω) := by
  have hlf : ∀ᵐ ω ∂P, ∀ i, IsLocallyFiniteMeasure (Z (s i) (t i) ω) := by
    apply ae_all_iff.2
    intro i
    exact (hZ.2.1 (s i) (t i) (hst i).1 (hst i).2).mono fun ω hω => hω.1
  have hlf' : ∀ᵐ ω ∂P', ∀ i, IsLocallyFiniteMeasure (Z' (s i) (t i) ω) := by
    apply ae_all_iff.2
    intro i
    exact (hZ'.2.1 (s i) (t i) (hst i).1 (hst i).2).mono fun ω hω => hω.1
  exact RandomMeasure.map_eq_of_pairing_laws P P' k
    (fun i ω => Z (s i) (t i) ω) (fun i ω => Z' (s i) (t i) ω)
    (fun i => hZ.1 (s i) (t i) (hst i).1 (hst i).2)
    (fun i => hZ'.1 (s i) (t i) (hst i).1 (hst i).2) hlf hlf'
    (fun m f => criticalSHF_pairing_law ϑ P P' Z Z' hZ hZ' m
      (fun j => s ((f j).1)) (fun j => t ((f j).1))
      (fun j => hst ((f j).1)) (fun j => (f j).2))

/-- Translate all times by a common amount without changing the dense-time axioms. -/
private theorem ae_nullSecondCoordinateMeasure_of_fdd {θ : ℝ} {D : Set ℝ}
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)}
    {Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane)}
    (hZ : IsDenseSHF θ D P Z)
    (hmeas : ∀ s ∈ D, ∀ t ∈ D, s < t → Measurable (Z' s t))
    (hfdd : ∀ (k : ℕ) (s t : Fin k → ℝ),
      (∀ i, s i ∈ D ∧ t i ∈ D ∧ s i < t i) →
      P.map (fun ω i => Z (s i) (t i) ω) = P'.map (fun ω i => Z' (s i) (t i) ω))
    {s t : ℝ} (hs : s ∈ D) (ht : t ∈ D) (hst : s < t)
    {A : Set Plane} (hA : MeasurableSet A) (hA0 : volume A = 0) :
    ∀ᵐ ω ∂P', (Z' s t ω) (Set.univ ×ˢ A) = 0 := by
  let T := s + t
  let Dr : Set ℝ := {u | T - u ∈ D}
  let Y : ℝ → ℝ → Ω → Measure (Plane × Plane) :=
    fun u v ω => (Z (T - v) (T - u) ω).map Prod.swap
  let Y' : ℝ → ℝ → Ω' → Measure (Plane × Plane) :=
    fun u v ω => (Z' (T - v) (T - u) ω).map Prod.swap
  have hY : IsDenseSHF θ Dr P Y := by
    simpa only [Y, T, Dr, add_sub_cancel_right] using isDenseSHF_reverse hZ T
  have hmeasY : ∀ u ∈ Dr, ∀ v ∈ Dr, u < v → Measurable (Y' u v) := by
    intro u hu v hv huv
    have htu : T - u ∈ D := hu
    have htv : T - v ∈ D := hv
    have htvLt : T - v < T - u := by linarith
    exact (Measure.measurable_map Prod.swap measurable_swap).comp
      (hmeas (T - v) htv (T - u) htu htvLt)
  have hfddY : ∀ (k : ℕ) (u v : Fin k → ℝ),
      (∀ i, u i ∈ Dr ∧ v i ∈ Dr ∧ u i < v i) →
      P.map (fun ω i => Y (u i) (v i) ω) = P'.map (fun ω i => Y' (u i) (v i) ω) := by
    intro k u v huv
    let F : Ω → Fin k → Measure (Plane × Plane) := fun ω i => Z (T - v i) (T - u i) ω
    let F' : Ω' → Fin k → Measure (Plane × Plane) := fun ω i => Z' (T - v i) (T - u i) ω
    let S : Measure (Plane × Plane) → Measure (Plane × Plane) := fun μ => μ.map Prod.swap
    let Svec : (Fin k → Measure (Plane × Plane)) → Fin k → Measure (Plane × Plane) :=
      fun m i => S (m i)
    have hF : Measurable F := by
      apply measurable_pi_iff.mpr
      intro i
      exact (hZ.1 _ (huv i).2.1 _ (huv i).1 (by linarith [(huv i).2.2])).1
    have hF' : Measurable F' := by
      apply measurable_pi_iff.mpr
      intro i
      exact hmeas _ (huv i).2.1 _ (huv i).1 (by linarith [(huv i).2.2])
    have hS : Measurable S := Measure.measurable_map Prod.swap measurable_swap
    have hSvec : Measurable Svec := by
      apply measurable_pi_iff.mpr
      intro i
      exact hS.comp (measurable_pi_apply i)
    have hLaw := hfdd k (fun i => T - v i) (fun i => T - u i) fun i => by
      exact ⟨(huv i).2.1, (huv i).1, by linarith [(huv i).2.2]⟩
    calc
      P.map (fun ω i => Y (u i) (v i) ω) = (P.map F).map Svec := by
        change P.map (Svec ∘ F) = _
        exact (Measure.map_map hSvec hF).symm
      _ = (P'.map F').map Svec := by rw [hLaw]
      _ = P'.map (fun ω i => Y' (u i) (v i) ω) := by
        change _ = P'.map (Svec ∘ F')
        exact Measure.map_map hSvec hF'
  have hleft := ae_nullCoordinateMeasure_of_fdd hY hmeasY hfddY
    (s := T - t) (t := T - s) (by simp [Dr, T, ht]) (by simp [Dr, T, hs])
    (by linarith) hA hA0
  have hpre : Prod.swap ⁻¹' (A ×ˢ (Set.univ : Set Plane)) =
      (Set.univ : Set Plane) ×ˢ A := by
    ext p
    change ((p.2, p.1) ∈ A ×ˢ Set.univ) ↔ p ∈ Set.univ ×ˢ A
    simp only [Set.mem_prod, Set.mem_univ, true_and, and_true]
  have htime₁ : T - (T - s) = s := by dsimp [T]; ring
  have htime₂ : T - (T - t) = t := by dsimp [T]; ring
  filter_upwards [hleft] with ω hω
  change ((Z' (T - (T - s)) (T - (T - t)) ω).map Prod.swap)
    (A ×ˢ (Set.univ : Set Plane)) = 0 at hω
  rw [Measure.map_apply measurable_swap (hA.prod MeasurableSet.univ), hpre] at hω
  simpa only [htime₁, htime₂] using hω

private theorem integral_momentKernel_congr_ae {n : ℕ} {θ τ : ℝ}
    (g g' g₀ g₀' : Fin n → Plane → ℝ)
    (hg : ∀ i, g i =ᵐ[volume] g₀ i) (hg' : ∀ i, g' i =ᵐ[volume] g₀' i) :
    (∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
      (∏ i, g i (x i)) * (DeltaBose.momentKernel n θ τ x y).toReal * ∏ i, g' i (y i)) =
    (∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
      (∏ i, g₀ i (x i)) * (DeltaBose.momentKernel n θ τ x y).toReal * ∏ i, g₀' i (y i)) := by
  let C := DeltaBose.Configuration n
  have heval (i : Fin n) :
      Measure.QuasiMeasurePreserving (fun x : C => x i) (volume : Measure C) volume := by
    simpa only [C, volume_pi] using
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => (volume : Measure Plane)) i)
  have hx (i : Fin n) : (fun xy : C × C => g i (xy.1 i)) =ᵐ[volume.prod volume]
      fun xy => g₀ i (xy.1 i) := by
    convert Measure.QuasiMeasurePreserving.ae_eq_comp
      ((heval i).comp (Measure.quasiMeasurePreserving_fst
        (μ := (volume : Measure C)) (ν := (volume : Measure C)))) (hg i) using 1 <;> rfl
  have hy (i : Fin n) : (fun xy : C × C => g' i (xy.2 i)) =ᵐ[volume.prod volume]
      fun xy => g₀' i (xy.2 i) := by
    convert Measure.QuasiMeasurePreserving.ae_eq_comp
      ((heval i).comp (Measure.quasiMeasurePreserving_snd
        (μ := (volume : Measure C)) (ν := (volume : Measure C)))) (hg' i) using 1 <;> rfl
  have hprod : ∀ᵐ xy : C × C ∂(volume.prod volume),
      (∀ i, g i (xy.1 i) = g₀ i (xy.1 i)) ∧
      (∀ i, g' i (xy.2 i) = g₀' i (xy.2 i)) := by
    have hxa : ∀ᵐ xy : C × C ∂(volume.prod volume), ∀ i,
        g i (xy.1 i) = g₀ i (xy.1 i) := ae_all_iff.2 hx
    have hya : ∀ᵐ xy : C × C ∂(volume.prod volume), ∀ i,
        g' i (xy.2 i) = g₀' i (xy.2 i) := ae_all_iff.2 hy
    filter_upwards [hxa, hya] with xy hxa hya
    exact ⟨hxa, hya⟩
  have hEq : (fun xy : C × C =>
      (∏ i, g i (xy.1 i)) * (DeltaBose.momentKernel n θ τ xy.1 xy.2).toReal *
        ∏ i, g' i (xy.2 i)) =ᵐ[volume.prod volume] fun xy =>
      (∏ i, g₀ i (xy.1 i)) * (DeltaBose.momentKernel n θ τ xy.1 xy.2).toReal *
        ∏ i, g₀' i (xy.2 i) := by
    filter_upwards [hprod] with xy hxy
    have hxprod : (∏ i, g i (xy.1 i)) = ∏ i, g₀ i (xy.1 i) :=
      Finset.prod_congr rfl fun i _ => hxy.1 i
    have hyprod : (∏ i, g' i (xy.2 i)) = ∏ i, g₀' i (xy.2 i) :=
      Finset.prod_congr rfl fun i _ => hxy.2 i
    rw [hxprod, hyprod]
  have hEqX : ∀ᵐ x : C ∂volume,
      (fun y : C => (∏ i, g i (x i)) *
        (DeltaBose.momentKernel n θ τ x y).toReal * ∏ i, g' i (y i)) =ᵐ[volume]
      fun y => (∏ i, g₀ i (x i)) *
        (DeltaBose.momentKernel n θ τ x y).toReal * ∏ i, g₀' i (y i) := by
    exact Measure.ae_ae_of_ae_prod hEq
  apply integral_congr_ae
  filter_upwards [hEqX] with x hx
  exact integral_congr_ae hx

private theorem momentClause_of_fdd_eq {θ : ℝ} {D : Set ℝ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)}
    {Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane)}
    (hZ : IsDenseSHF θ D P Z)
    (hmeas : ∀ s ∈ D, ∀ t ∈ D, s < t → Measurable (Z' s t))
    (hfdd : ∀ (k : ℕ) (s t : Fin k → ℝ),
      (∀ i, s i ∈ D ∧ t i ∈ D ∧ s i < t i) →
      P.map (fun ω i => Z (s i) (t i) ω) = P'.map (fun ω i => Z' (s i) (t i) ω)) :
    ∀ n : ℕ, 1 ≤ n → n ≤ 4 → ∀ s ∈ D, ∀ t ∈ D, s < t →
      ∀ g g' : Fin n → Plane → ℝ, (∀ i, MemLp (g i) 2) → (∀ i, MemLp (g' i) 2) →
        (∀ᵐ ω ∂P', ∀ i, Integrable
          (fun p : Plane × Plane => g i p.1 * g' i p.2) (Z' s t ω)) ∧
        Integrable (fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2 ∂Z' s t ω) P' ∧
        ∫ ω, ∏ i, ∫ p, g i p.1 * g' i p.2 ∂Z' s t ω ∂P' =
          ∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
            (∏ i, g i (x i)) * (DeltaBose.momentKernel n θ (t - s) x y).toReal *
              ∏ i, g' i (y i) := by
  intro n hn hn4 s hs t ht hst g g' hg hg'
  let g₀ : Fin n → Plane → ℝ := fun i => (hg i).aestronglyMeasurable.mk (g i)
  let g₀' : Fin n → Plane → ℝ := fun i => (hg' i).aestronglyMeasurable.mk (g' i)
  have hgm : ∀ i, Measurable (g₀ i) := fun i => (hg i).aestronglyMeasurable.measurable_mk
  have hgm' : ∀ i, Measurable (g₀' i) := fun i => (hg' i).aestronglyMeasurable.measurable_mk
  have hgeq : ∀ i, g i =ᵐ[volume] g₀ i := fun i => (hg i).aestronglyMeasurable.ae_eq_mk
  have hgeq' : ∀ i, g' i =ᵐ[volume] g₀' i := fun i => (hg' i).aestronglyMeasurable.ae_eq_mk
  have hgmLp : ∀ i, MemLp (g₀ i) 2 := by
    intro i
    exact (memLp_congr_ae (hgeq i)).mp (hg i)
  have hgmLp' : ∀ i, MemLp (g₀' i) 2 := by
    intro i
    exact (memLp_congr_ae (hgeq' i)).mp (hg' i)
  have hbase := momentClause_of_fdd_eq_measurable hZ hmeas hfdd
    n hn hn4 s hs t ht hst g₀ g₀' hgmLp hgmLp' hgm hgm'
  rcases hbase with ⟨hInt₀, hMoment₀, hMean₀⟩
  let A : Fin n → Set Plane := fun i => toMeasurable volume {x | g i x ≠ g₀ i x}
  let B : Fin n → Set Plane := fun i => toMeasurable volume {x | g' i x ≠ g₀' i x}
  have hAmeas : ∀ i, MeasurableSet (A i) := fun i => measurableSet_toMeasurable _ _
  have hBmeas : ∀ i, MeasurableSet (B i) := fun i => measurableSet_toMeasurable _ _
  have hA0 : ∀ i, volume (A i) = 0 := by
    intro i
    rw [measure_toMeasurable]
    exact (ae_iff.mp (hgeq i))
  have hB0 : ∀ i, volume (B i) = 0 := by
    intro i
    rw [measure_toMeasurable]
    exact (ae_iff.mp (hgeq' i))
  have hAstrip : ∀ i, ∀ᵐ ω ∂P', (Z' s t ω) (A i ×ˢ Set.univ) = 0 := by
    intro i
    exact ae_nullCoordinateMeasure_of_fdd hZ hmeas hfdd hs ht hst
      (hAmeas i) (hA0 i)
  have hBstrip : ∀ i, ∀ᵐ ω ∂P', (Z' s t ω) (Set.univ ×ˢ B i) = 0 := by
    intro i
    exact ae_nullSecondCoordinateMeasure_of_fdd hZ hmeas hfdd hs ht hst
      (hBmeas i) (hB0 i)
  have htest (i : Fin n) : ∀ᵐ ω ∂P',
      (fun p : Plane × Plane => g i p.1 * g' i p.2) =ᵐ[Z' s t ω]
        fun p => g₀ i p.1 * g₀' i p.2 := by
    filter_upwards [hAstrip i, hBstrip i] with ω hA hB
    have hfirst : (fun p : Plane × Plane => g i p.1) =ᵐ[Z' s t ω]
        fun p => g₀ i p.1 := by
      apply ae_iff.mpr
      change (Z' s t ω) {p : Plane × Plane | g i p.1 ≠ g₀ i p.1} = 0
      apply measure_mono_null ?_ hA
      intro p hp
      exact ⟨(subset_toMeasurable volume _ hp), Set.mem_univ _⟩
    have hsecond : (fun p : Plane × Plane => g' i p.2) =ᵐ[Z' s t ω]
        fun p => g₀' i p.2 := by
      apply ae_iff.mpr
      change (Z' s t ω) {p : Plane × Plane | g' i p.2 ≠ g₀' i p.2} = 0
      apply measure_mono_null ?_ hB
      intro p hp
      exact ⟨Set.mem_univ _, subset_toMeasurable volume _ hp⟩
    filter_upwards [hfirst, hsecond] with p hp hp'
    rw [hp, hp']
  have hInt : ∀ᵐ ω ∂P', ∀ i, Integrable
      (fun p : Plane × Plane => g i p.1 * g' i p.2) (Z' s t ω) := by
    apply ae_all_iff.2
    intro i
    filter_upwards [ae_all_iff.mp hInt₀ i, htest i] with ω hω heq
    exact hω.congr heq.symm
  have hProdEq : (fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2 ∂Z' s t ω) =ᵐ[P']
      fun ω => ∏ i, ∫ p, g₀ i p.1 * g₀' i p.2 ∂Z' s t ω := by
    have hIntegrals : ∀ᵐ ω ∂P', ∀ i,
        ∫ p, g i p.1 * g' i p.2 ∂Z' s t ω =
          ∫ p, g₀ i p.1 * g₀' i p.2 ∂Z' s t ω := by
      apply ae_all_iff.2
      intro i
      filter_upwards [htest i] with ω hω
      exact integral_congr_ae hω
    filter_upwards [hIntegrals] with ω hω
    exact Finset.prod_congr rfl fun i _ => hω i
  refine ⟨hInt, hMoment₀.congr hProdEq.symm, ?_⟩
  calc
    ∫ ω, ∏ i, ∫ p, g i p.1 * g' i p.2 ∂Z' s t ω ∂P' =
        ∫ ω, ∏ i, ∫ p, g₀ i p.1 * g₀' i p.2 ∂Z' s t ω ∂P' :=
      integral_congr_ae hProdEq
    _ = ∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
          (∏ i, g₀ i (x i)) * (DeltaBose.momentKernel n θ (t - s) x y).toReal *
            ∏ i, g₀' i (y i) := hMean₀
    _ = ∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
          (∏ i, g i (x i)) * (DeltaBose.momentKernel n θ (t - s) x y).toReal *
            ∏ i, g' i (y i) :=
      (integral_momentKernel_congr_ae g g' g₀ g₀' hgeq hgeq').symm

/-- Tsai's dense-time axioms are determined by the finite-dimensional laws of the random
measures. The composition clause is transferred through the measurable cutoff readouts, with
the compact exhaustion reducing universal test integrability to countably many cutoffs. -/
theorem isDenseSHF_of_fdd_eq {θ : ℝ} {D : Set ℝ} {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)}
    {Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane)} (hZ : IsDenseSHF θ D P Z)
    (hmeas : ∀ s ∈ D, ∀ t ∈ D, s < t → Measurable (Z' s t))
    (hfdd : ∀ (k : ℕ) (s t : Fin k → ℝ), (∀ i, s i ∈ D ∧ t i ∈ D ∧ s i < t i) →
      P.map (fun ω i => Z (s i) (t i) ω) = P'.map (fun ω i => Z' (s i) (t i) ω)) :
    IsDenseSHF θ D P' Z' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs t ht hst
    exact firstClause_of_fdd_eq hZ hmeas hfdd s hs t ht hst
  · intro t₀ ht₀ t₁ ht₁ t₂ ht₂ h01 h12
    rcases hZ.2.1 t₀ ht₀ t₁ ht₁ t₂ ht₂ h01 h12 with
      ⟨w, hw, hwell, hconv⟩
    let E := CompactExhaustion.choice (Plane × Plane)
    let U : Ω → Measure (Plane × Plane) × Measure (Plane × Plane) :=
      fun ω => (Z t₀ t₁ ω, Z t₁ t₂ ω)
    let V : Ω' → Measure (Plane × Plane) × Measure (Plane × Plane) :=
      fun ω => (Z' t₀ t₁ ω, Z' t₁ t₂ ω)
    have hU : Measurable U := by
      exact ((hZ.1 t₀ ht₀ t₁ ht₁ h01).1).prodMk
        ((hZ.1 t₁ ht₁ t₂ ht₂ h12).1)
    have hV : Measurable V := by
      exact (hmeas t₀ ht₀ t₁ ht₁ h01).prodMk (hmeas t₁ ht₁ t₂ ht₂ h12)
    let s : Fin 2 → ℝ := ![t₀, t₁]
    let t : Fin 2 → ℝ := ![t₁, t₂]
    have hst' : ∀ i, s i ∈ D ∧ t i ∈ D ∧ s i < t i := by
      intro i
      fin_cases i
      · exact ⟨ht₀, ht₁, h01⟩
      · exact ⟨ht₁, ht₂, h12⟩
    have htuple : Measurable (fun ω i => Z (s i) (t i) ω) := by
      apply measurable_pi_iff.mpr
      intro i
      fin_cases i
      · simpa [s, t] using (hZ.1 t₀ ht₀ t₁ ht₁ h01).1
      · simpa [s, t] using (hZ.1 t₁ ht₁ t₂ ht₂ h12).1
    have htuple' : Measurable (fun ω i => Z' (s i) (t i) ω) := by
      apply measurable_pi_iff.mpr
      intro i
      fin_cases i
      · simpa [s, t] using hmeas t₀ ht₀ t₁ ht₁ h01
      · simpa [s, t] using hmeas t₁ ht₁ t₂ ht₂ h12
    let pairOf (m : Fin 2 → Measure (Plane × Plane)) := (m 0, m 1)
    have hpairOf : Measurable pairOf :=
      (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
    have hpairLaw : P.map U = P'.map V := by
      have h := congrArg (fun μ : Measure (Fin 2 → Measure (Plane × Plane)) => μ.map pairOf)
        (hfdd 2 s t hst')
      rw [Measure.map_map hpairOf htuple, Measure.map_map hpairOf htuple'] at h
      simpa [Function.comp_def, U, V, pairOf, s, t] using h
    have hLFsrc : ∀ᵐ ω ∂P,
        IsLocallyFiniteMeasure (Z t₀ t₁ ω) ∧ IsLocallyFiniteMeasure (Z t₁ t₂ ω) := by
      filter_upwards [(hZ.1 t₀ ht₀ t₁ ht₁ h01).2,
        (hZ.1 t₁ ht₁ t₂ ht₂ h12).2] with ω h₀ h₁
      exact ⟨h₀, h₁⟩
    have hLFtar (a ha b hb hab) : ∀ᵐ ω ∂P',
        IsLocallyFiniteMeasure (Z' a b ω) :=
      (firstClause_of_fdd_eq hZ hmeas hfdd a ha b hb hab).2
    have hLFtarPair : ∀ᵐ ω ∂P',
        IsLocallyFiniteMeasure (Z' t₀ t₁ ω) ∧ IsLocallyFiniteMeasure (Z' t₁ t₂ ω) := by
      filter_upwards [hLFtar t₀ ht₀ t₁ ht₁ h01,
        hLFtar t₁ ht₁ t₂ ht₂ h12] with ω h₀ h₁
      exact ⟨h₀, h₁⟩
    have hcut (ℓ n : ℕ) : ∀ᵐ ω ∂P', Integrable
        (fun q : (Plane × Plane) × (Plane × Plane) =>
          RandomMeasure.vagueMassTest E n (q.1.1, q.2.2) * w ℓ (q.1.2 - q.2.1))
        ((Z' t₀ t₁ ω).prod (Z' t₁ t₂ ω)) := by
      exact ae_integrable_product_of_pair_law E (w ℓ) (hw.1 ℓ)
        (hw.2.1 ℓ).measurable (RandomMeasure.vagueMassTest E n)
        (Z t₀ t₁) (Z t₁ t₂) (Z' t₀ t₁) (Z' t₁ t₂)
        (hZ.1 t₀ ht₀ t₁ ht₁ h01).1 (hZ.1 t₁ ht₁ t₂ ht₂ h12).1
        (hmeas t₀ ht₀ t₁ ht₁ h01) (hmeas t₁ ht₁ t₂ ht₂ h12)
        hpairLaw hLFsrc hLFtarPair (by
          filter_upwards [hwell ℓ] with ω hω
          exact hω (RandomMeasure.vagueMassTest E n))
    have hcutAll (ℓ : ℕ) : ∀ᵐ ω ∂P', ∀ n : ℕ, Integrable
        (fun q : (Plane × Plane) × (Plane × Plane) =>
          RandomMeasure.vagueMassTest E n (q.1.1, q.2.2) * w ℓ (q.1.2 - q.2.1))
        ((Z' t₀ t₁ ω).prod (Z' t₁ t₂ ω)) := by
      apply ae_all_iff.2
      intro n
      exact hcut ℓ n
    have hwell' (ℓ : ℕ) : ∀ᵐ ω ∂P',
        SmoothedProductWellDefined (Z' t₀ t₁ ω) (w ℓ) (Z' t₁ t₂ ω) := by
      filter_upwards [hcutAll ℓ] with ω hcutω
      intro f
      obtain ⟨n, hsupport⟩ := E.exists_superset_of_isCompact (by
        simpa only [HasCompactSupport, tsupport] using f.hasCompactSupport)
      let c : ℝ := ‖f.toBoundedContinuousFunction‖
      have hpoint (x : Plane × Plane) :
          |f x| ≤ c * RandomMeasure.vagueMassTest E n x := by
        by_cases hx : x ∈ tsupport (f : Plane × Plane → ℝ)
        · rw [(RandomMeasure.vagueMassTest_spec E n).2.2.1 x (hsupport hx)]
          have hnorm : |f x| ≤ ‖f.toBoundedContinuousFunction‖ := by
            calc
              |f x| = ‖f x‖ := (Real.norm_eq_abs _).symm
              _ = ‖f.toBoundedContinuousFunction x‖ := by rfl
              _ ≤ ‖f.toBoundedContinuousFunction‖ :=
                f.toBoundedContinuousFunction.norm_coe_le_norm x
          simpa [c] using hnorm
        · rw [image_eq_zero_of_notMem_tsupport hx]
          simp only [abs_zero]
          exact mul_nonneg (norm_nonneg _) ((RandomMeasure.vagueMassTest_spec E n).1 x)
      have hdom (q : (Plane × Plane) × (Plane × Plane)) :
          ‖f (q.1.1, q.2.2) * w ℓ (q.1.2 - q.2.1)‖ ≤
            c * (RandomMeasure.vagueMassTest E n (q.1.1, q.2.2) *
              w ℓ (q.1.2 - q.2.1)) := by
        have hwq := hw.1 ℓ (q.1.2 - q.2.1)
        calc
          ‖f (q.1.1, q.2.2) * w ℓ (q.1.2 - q.2.1)‖ =
              |f (q.1.1, q.2.2)| * w ℓ (q.1.2 - q.2.1) := by
                rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hwq]
          _ ≤ (c * RandomMeasure.vagueMassTest E n (q.1.1, q.2.2)) *
                w ℓ (q.1.2 - q.2.1) :=
              mul_le_mul_of_nonneg_right (hpoint (q.1.1, q.2.2)) hwq
          _ = c * (RandomMeasure.vagueMassTest E n (q.1.1, q.2.2) *
                w ℓ (q.1.2 - q.2.1)) := by ring
      have hwℓ : Measurable (w ℓ) := (hw.2.1 ℓ).measurable
      have hmeasF : Measurable (fun q : (Plane × Plane) × (Plane × Plane) =>
          f (q.1.1, q.2.2) * w ℓ (q.1.2 - q.2.1)) := by fun_prop
      exact (hcutω n).const_mul c |>.mono' hmeasF.aestronglyMeasurable
        (Filter.Eventually.of_forall hdom)
    refine ⟨w, hw, hwell', ?_⟩
    exact compositionLimit_of_fdd_eq_of_wellDefined hZ hmeas hfdd
      ht₀ ht₁ ht₂ h01 h12 w hw hwell hconv hwell'
      (hLFtar t₀ ht₀ t₁ ht₁ h01) (hLFtar t₁ ht₁ t₂ ht₂ h12)
      (hLFtar t₀ ht₀ t₂ ht₂ (lt_trans h01 h12))
  · exact independenceClause_of_fdd_eq hZ hmeas hfdd
  · exact momentClause_of_fdd_eq hZ hmeas hfdd


/-- A time shift transports the dense SHF axioms to the shifted time set. -/
theorem isDenseSHF_timeShift {θ : ℝ} {D : Set ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)}
    (hZ : IsDenseSHF θ D P Z) (u : ℝ) :
    IsDenseSHF θ {s | s + u ∈ D} P fun s t ω => Z (s + u) (t + u) ω := by
  rcases hZ with ⟨hpair, hcomp, hindep, hmom⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs t ht hst
    change s + u ∈ D at hs
    change t + u ∈ D at ht
    exact hpair (s + u) hs (t + u) ht ((add_lt_add_iff_right u).2 hst)
  · intro t₀ ht₀ t₁ ht₁ t₂ ht₂ h01 h12
    change t₀ + u ∈ D at ht₀
    change t₁ + u ∈ D at ht₁
    change t₂ + u ∈ D at ht₂
    exact hcomp (t₀ + u) ht₀ (t₁ + u) ht₁ (t₂ + u) ht₂
      ((add_lt_add_iff_right u).2 h01) ((add_lt_add_iff_right u).2 h12)
  · intro k t hstrict ht
    apply hindep k (fun i => t i + u)
    · intro i j hij
      exact (add_lt_add_iff_right u).2 (hstrict hij)
    · exact fun i => ht i
  · intro n hn hn4 s hs t ht hst g g' hg hg'
    change s + u ∈ D at hs
    change t + u ∈ D at ht
    have h := hmom n hn hn4 (s + u) hs (t + u) ht
      ((add_lt_add_iff_right u).2 hst) g g' hg hg'
    simpa only [add_sub_add_right_eq_sub] using h

/-- Restricting the time set preserves every dense-time SHF axiom. -/
theorem isDenseSHF_mono {θ : ℝ} {D D' : Set ℝ} (hDD' : D' ⊆ D) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)}
    (hZ : IsDenseSHF θ D P Z) : IsDenseSHF θ D' P Z := by
  rcases hZ with ⟨hpair, hcomp, hindep, hmom⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs t ht hst
    exact hpair s (hDD' hs) t (hDD' ht) hst
  · intro t₀ ht₀ t₁ ht₁ t₂ ht₂ h01 h12
    exact hcomp t₀ (hDD' ht₀) t₁ (hDD' ht₁) t₂ (hDD' ht₂) h01 h12
  · intro k t hmono ht
    exact hindep k t hmono (fun i => hDD' (ht i))
  · intro n hn hn4 s hs t ht hst g g' hg hg'
    exact hmom n hn hn4 s (hDD' hs) t (hDD' ht) hst g g' hg hg'

end Critical2DKPZ.SHF.Symmetries

end
