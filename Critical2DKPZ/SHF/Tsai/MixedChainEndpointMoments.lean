/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.MixedChainLocalFiniteness
public import Critical2DKPZ.SHF.Tsai.ChainEndpointMoments

/-! # The full endpoint moment measure of partially heat-replaced chains

The exact positive mixed tensor moments determine the full endpoint moment
measure using the finite form bound. Locally finite modifications retain
the literal chains almost surely, enabling arbitrary real L2 tests.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Any measurable locally finite modifications of the chains have the literal chain-kernel moment measure. -/
theorem bind_endpointTupleMeasure_mixedChain_eq {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (K j : ℕ) (hj : j ≤ K) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4) (S : Finset (Fin n))
    (w : Fin n → ℕ → ℕ → Plane → ℝ) (hw : ∀ i k, IsL2ApplicableMollifier (w i k)) (ℓ : ℕ)
    (C : Fin n → Ω → Measure (Plane × Plane)) (hCm : ∀ i, Measurable (C i))
    (hClf : ∀ i ω, IsLocallyFiniteMeasure (C i ω))
    (hCeq : ∀ i, C i =ᵐ[P] fun ω => chainProduct (if i ∈ S then (fun k => B k ω) else
      Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w i k ℓ) K) :
    P.bind (fun ω => endpointTupleMeasure (fun i => C i ω)) =
      volume.withDensity (Function.uncurry (chainKernel n (Function.update (fun k => momentKernel n θ (τ k)) j (mixedBlockKernel n θ (τ j) S)) (fun i k => w i k ℓ) K)) := by
  let ν := P.bind (fun ω => endpointTupleMeasure (fun i => C i ω))
  have hνm := measurable_endpointTupleMeasure C hCm hClf
  have hmeanTensor (f g : Fin n → Plane → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i)) :
      (∫⁻ q, (∏ i, f i (q.1 i)) * ∏ i, g i (q.2 i) ∂ν) =
        ∫⁻ x, ∫⁻ y, (∏ i, f i (x i)) *
          chainKernel n (Function.update (fun k => momentKernel n θ (τ k)) j (mixedBlockKernel n θ (τ j) S)) (fun i k => w i k ℓ) K x y * ∏ i, g i (y i) := by
    have hfp : Measurable (fun x : Configuration n => ∏ i, f i (x i)) :=
      Finset.measurable_prod _ (fun i _ => (hf i).comp (measurable_pi_apply i))
    have hgp : Measurable (fun x : Configuration n => ∏ i, g i (x i)) :=
      Finset.measurable_prod _ (fun i _ => (hg i).comp (measurable_pi_apply i))
    have ht := (hfp.comp measurable_fst).mul (hgp.comp measurable_snd)
    calc
      _ = ∫⁻ ω, ∫⁻ q, (∏ i, f i (q.1 i)) * ∏ i, g i (q.2 i)
          ∂endpointTupleMeasure (fun i => C i ω) ∂P := Measure.lintegral_bind hνm.aemeasurable ht.aemeasurable
      _ = ∫⁻ ω, ∏ i, ∫⁻ p, f i p.1 * g i p.2 ∂C i ω ∂P := by
        apply lintegral_congr
        intro ω
        let : ∀ i, IsLocallyFiniteMeasure (C i ω) := fun i => hClf i ω
        exact lintegral_endpointTupleMeasure_tensor (fun i => C i ω) f g hf hg
      _ = ∫⁻ ω, ∏ i, ∫⁻ p, f i p.1 * g i p.2
          ∂chainProduct (if i ∈ S then (fun k => B k ω) else
      Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w i k ℓ) K ∂P := by
        apply lintegral_congr_ae
        filter_upwards [ae_all_iff.2 hCeq] with ω hω
        apply Finset.prod_congr rfl
        intro i _
        rw [hω i]
      _ = _ := lintegral_prod_chainProduct_update_heat_eq K j hj τ hτ B hB hind hn1 hn S (fun i k => w i k ℓ)
        (fun i k => (hw i k).1 ℓ) (fun i k => ((hw i k).2.1 ℓ).measurable) f g hf hg
  have hchain := measurable_chainKernel
    (Function.update (fun k => momentKernel n θ (τ k)) j (mixedBlockKernel n θ (τ j) S))
    (measurable_momentKernel_update_mixed n θ τ j S) (fun i k => w i k ℓ)
    (fun i k => ((hw i k).2.1 ℓ).measurable) K
  obtain ⟨M, hMfin, hMF⟩ := exists_formBound_mixedChainKernel_uniform θ K j hj τ hτ S w hw
  apply (kernelMeasure_eq_of_rectangles hchain hMfin (hMF ℓ) ν ?_).symm
  intro A D hA hD
  let f (i : Fin n) : Plane → ℝ≥0∞ := (A i).indicator (fun _ => 1)
  let g (i : Fin n) : Plane → ℝ≥0∞ := (D i).indicator (fun _ => 1)
  have hf (i) : Measurable (f i) := measurable_const.indicator (hA i)
  have hg (i) : Measurable (g i) := measurable_const.indicator (hD i)
  have hfp : Measurable (fun x : Configuration n => ∏ i, f i (x i)) :=
    Finset.measurable_prod _ (fun i _ => (hf i).comp (measurable_pi_apply i))
  have hgp : Measurable (fun x : Configuration n => ∏ i, g i (x i)) :=
    Finset.measurable_prod _ (fun i _ => (hg i).comp (measurable_pi_apply i))
  calc
    _ = ∫⁻ q, (∏ i, f i (q.1 i)) * ∏ i, g i (q.2 i)
        ∂volume.withDensity (Function.uncurry (chainKernel n (Function.update (fun k => momentKernel n θ (τ k)) j (mixedBlockKernel n θ (τ j) S)) (fun i k => w i k ℓ) K)) :=
      measure_configurationRectangle_eq_lintegral_tensor _ A D hA hD
    _ = ∫⁻ x, ∫⁻ y, (∏ i, f i (x i)) *
        chainKernel n (Function.update (fun k => momentKernel n θ (τ k)) j (mixedBlockKernel n θ (τ j) S)) (fun i k => w i k ℓ) K x y * ∏ i, g i (y i) :=
      lintegral_kernelMeasure_mul hchain hfp hgp
    _ = ∫⁻ q, (∏ i, f i (q.1 i)) * ∏ i, g i (q.2 i) ∂ν := (hmeanTensor f g hf hg).symm
    _ = _ := (measure_configurationRectangle_eq_lintegral_tensor _ A D hA hD).symm


/-- Literal mixed chains admit locally finite measurable modifications with their full endpoint moment measure. -/
theorem exists_mixedChain_endpointTuple_moment_measure {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (K j : ℕ) (hj : j ≤ K) (τ : ℕ → ℝ)
    (hτ : ∀ k ≤ K, 0 < τ k) (B : ℕ → Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4)
    (S : Finset (Fin n)) (w : Fin n → ℕ → ℕ → Plane → ℝ)
    (hw : ∀ i k, IsL2ApplicableMollifier (w i k)) (ℓ : ℕ) :
    ∃ C : Fin n → Ω → Measure (Plane × Plane), (∀ i, Measurable (C i)) ∧
      (∀ i ω, IsLocallyFiniteMeasure (C i ω)) ∧
      (∀ i, C i =ᵐ[P] fun ω => chainProduct
        (if i ∈ S then (fun k => B k ω) else Function.update (fun k => B k ω) j (heatBlock (τ j)))
        (fun k => w i k ℓ) K) ∧
      P.bind (fun ω => endpointTupleMeasure (fun i => C i ω)) =
        volume.withDensity (Function.uncurry (chainKernel n
          (Function.update (fun k => momentKernel n θ (τ k)) j (mixedBlockKernel n θ (τ j) S))
          (fun i k => w i k ℓ) K)) := by
  classical
  let E := CompactExhaustion.choice (Plane × Plane)
  let R (i : Fin n) (ω : Ω) := chainProduct
    (if i ∈ S then (fun k => B k ω) else Function.update (fun k => B k ω) j (heatBlock (τ j)))
    (fun k => w i k ℓ) K
  have hRm (i : Fin n) : AEMeasurable (R i) P := by
    by_cases hi : i ∈ S
    · simp only [R, ite_eq_left hi]
      exact aemeasurable_chainProduct P K B (fun k hk => (hB k hk).1)
        (fun k hk => (hB k hk).2.1) _ (fun k => ((hw i k).2.1 ℓ).measurable)
    · simp only [R, ite_eq_right hi]
      exact aemeasurable_chainProduct_update_heat P K j (τ j) B (fun k hk => (hB k hk).1)
        (fun k hk => (hB k hk).2.1) _ (fun k => ((hw i k).2.1 ℓ).measurable)
  have hRlf (i : Fin n) : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (R i ω) := by
    by_cases hi : i ∈ S
    · simp only [R, ite_eq_left hi]
      exact ae_locallyFinite_chainProduct K τ hτ B hB hind (w i) (hw i) ℓ
    · simp only [R, ite_eq_right hi]
      exact ae_locallyFinite_chainProduct_update_heat K j hj τ hτ B hB hind (w i) (hw i) ℓ
  have hmods (i : Fin n) := RandomMeasure.exists_measurable_locallyFinite_modification E P
    (R i) (hRm i) (hRlf i)
  choose C hCm hClf hCeq using hmods
  exact ⟨C, hCm, hClf, hCeq,
    bind_endpointTupleMeasure_mixedChain_eq K j hj τ hτ B hB hind hn1 hn S w hw ℓ C hCm hClf hCeq⟩

end Critical2DKPZ.SHF.Tsai

end
