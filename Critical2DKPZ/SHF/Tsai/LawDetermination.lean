/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.TensorLawDetermination
public import Critical2DKPZ.SHF.Tsai.CompactTensorApproximation
public import Critical2DKPZ.SHF.Tsai.CompactPairingApproximation
public import Critical2DKPZ.SHF.Tsai.LimitLaws
public import Critical2DKPZ.RandomMeasure.PlanePairInterface

/-! # Random-measure laws determined by smooth tensor expectations

Finite tensor-vector laws determine grouped sums with varying row lengths.
Uniform compact tensor approximation passes their laws to arbitrary compact
plane-pair test vectors. The canonical pairing-law criterion identifies the
original random-measure laws, including their exceptional non-locally-finite values.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- Expectations of smooth functions with derivatives bounded through order four of finite compact tensor-pairing sums determine the law of an almost surely locally finite random measure. -/
theorem map_eq_of_forall_integral_contDiff_eq {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] (Z : Ω → Measure (Plane × Plane)) (Z' : Ω' → Measure (Plane × Plane))
    (hZ : Measurable Z) (hZ' : Measurable Z') (hlf : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Z ω))
    (hlf' : ∀ᵐ ω ∂P', IsLocallyFiniteMeasure (Z' ω))
    (h : ∀ (m r : ℕ) (g g' : Fin m → Fin r → C_c(Plane, ℝ)) (H : (Fin m → ℝ) → ℝ), ContDiff ℝ 4 H →
      (∃ C : ℝ, ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k H x‖ ≤ C) →
      ∫ ω, H (fun a => ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂(Z ω)) ∂P =
        ∫ ω, H (fun a => ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂(Z' ω)) ∂P') :
    P.map Z = P'.map Z' := by
  classical
  have hTensor (n : ℕ) (g g' : Fin n → C_c(Plane, ℝ)) :
      P.map (fun ω i => ∫ p, g i p.1 * g' i p.2 ∂Z ω) =
        P'.map (fun ω i => ∫ p, g i p.1 * g' i p.2 ∂Z' ω) := by
    have hLaw := map_tensorSumPairings_eq_of_integral_contDiff_eq P P' Z Z' hZ hZ' n 1
      (fun i _ => g i) (fun i _ => g' i) (h n 1 _ _)
    simpa only [Fin.sum_univ_one] using hLaw
  have hCompact (m : ℕ) (f : Fin m → C_c(Plane × Plane, ℝ)) :
      P.map (fun ω i => ∫ p, f i p ∂Z ω) = P'.map (fun ω i => ∫ p, f i p ∂Z' ω) := by
    choose K hK r g g' hsupport herr using fun a : Fin m => exists_compactTensorSum_sequence (f a)
    let v (n : ℕ) (a : Fin m) : C_c(Plane × Plane, ℝ) :=
      ∑ b, compactTensorTest (g a n b) (g' a n b)
    have hvSupport (n : ℕ) (a : Fin m) : tsupport (v n a : Plane × Plane → ℝ) ⊆ K a := hsupport a n
    have hvApprox (n : ℕ) (a : Fin m) (p : Plane × Plane) :
        |v n a p - f a p| ≤ 1 / ((n : ℝ) + 1) := herr a n p
    have hvIntegral (μ : Measure (Plane × Plane)) [IsLocallyFiniteMeasure μ] (n : ℕ) (a : Fin m) :
        (∫ p, v n a p ∂μ) = ∑ b, ∫ p, g a n b p.1 * g' a n b p.2 ∂μ := by
      simp only [v, CompactlySupportedContinuousMap.sum_apply]
      exact integral_finsetSum _ (fun b _ => (compactTensorTest (g a n b) (g' a n b)).integrable)
    let κ : Kernel Ω (Plane × Plane) := ⟨Z, hZ⟩
    let κ' : Kernel Ω' (Plane × Plane) := ⟨Z', hZ'⟩
    have hVm (n : ℕ) : Measurable (fun ω a => ∫ p, v n a p ∂Z ω) :=
      Measurable.of_eval fun a => ((v n a).continuous.measurable.stronglyMeasurable.integral_kernel (κ := κ)).measurable
    have hVm' (n : ℕ) : Measurable (fun ω a => ∫ p, v n a p ∂Z' ω) :=
      Measurable.of_eval fun a => ((v n a).continuous.measurable.stronglyMeasurable.integral_kernel (κ := κ')).measurable
    have hPoint (μ : Measure (Plane × Plane)) [IsLocallyFiniteMeasure μ] :
        Tendsto (fun n a => ∫ p, v n a p ∂μ) atTop (𝓝 (fun a => ∫ p, f a p ∂μ)) := by
      apply tendsto_pi_nhds.2
      intro a
      exact tendsto_integral_of_uniform_compact_support μ (f a) (fun n => v n a)
        (K a ∪ tsupport (f a : Plane × Plane → ℝ)) ((hK a).union (f a).hasCompactSupport)
        subset_union_right (fun n => (hvSupport n a).trans subset_union_left) (fun n p => hvApprox n a p)
    have hconv : TendstoInMeasure P (fun n ω a => ∫ p, v n a p ∂Z ω) atTop
        (fun ω a => ∫ p, f a p ∂Z ω) := by
      apply tendstoInMeasure_of_tendsto_ae (fun n => (hVm n).aestronglyMeasurable)
      filter_upwards [hlf] with ω hω
      let : IsLocallyFiniteMeasure (Z ω) := hω
      exact hPoint (Z ω)
    have hconv' : TendstoInMeasure P' (fun n ω a => ∫ p, v n a p ∂Z' ω) atTop
        (fun ω a => ∫ p, f a p ∂Z' ω) := by
      apply tendstoInMeasure_of_tendsto_ae (fun n => (hVm' n).aestronglyMeasurable)
      filter_upwards [hlf'] with ω hω
      let : IsLocallyFiniteMeasure (Z' ω) := hω
      exact hPoint (Z' ω)
    apply map_eq_of_tendstoInMeasure_of_map_eq P P' _ _ _ _
      (fun n => (hVm n).aemeasurable) (fun n => (hVm' n).aemeasurable) hconv hconv'
    intro n
    have hRead : (fun ω a => ∫ p, v n a p ∂Z ω) =ᵐ[P]
        fun ω a => ∑ b, ∫ p, g a n b p.1 * g' a n b p.2 ∂Z ω := by
      filter_upwards [hlf] with ω hω
      let : IsLocallyFiniteMeasure (Z ω) := hω
      funext a
      exact hvIntegral (Z ω) n a
    have hRead' : (fun ω a => ∫ p, v n a p ∂Z' ω) =ᵐ[P']
        fun ω a => ∑ b, ∫ p, g a n b p.1 * g' a n b p.2 ∂Z' ω := by
      filter_upwards [hlf'] with ω hω
      let : IsLocallyFiniteMeasure (Z' ω) := hω
      funext a
      exact hvIntegral (Z' ω) n a
    rw [Measure.map_congr hRead, Measure.map_congr hRead']
    exact map_sum_pairings_eq_of_tensor_laws P P' Z Z' hZ hZ' hTensor
      (fun a => r a n) (fun a => g a n) (fun a => g' a n)
  have hMap := RandomMeasure.map_eq_of_pairing_laws P P' 1 (fun _ => Z) (fun _ => Z')
    (fun _ => hZ) (fun _ => hZ') (hlf.mono (fun ω hω _ => hω)) (hlf'.mono (fun ω hω _ => hω))
    (fun m f => hCompact m (fun i => (f i).2))
  have hEval := congrArg (fun ν : Measure (Fin 1 → Measure (Plane × Plane)) => ν.map (fun x => x 0)) hMap
  rw [Measure.map_map (measurable_pi_apply 0) (Measurable.of_eval (fun _ => hZ)),
    Measure.map_map (measurable_pi_apply 0) (Measurable.of_eval (fun _ => hZ'))] at hEval
  simpa only [Function.comp_def] using hEval

end Critical2DKPZ.SHF.Tsai

end
