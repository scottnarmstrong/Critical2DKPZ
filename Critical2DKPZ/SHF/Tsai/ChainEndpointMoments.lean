/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainLocalFiniteness
public import Critical2DKPZ.SHF.Tsai.BlockTupleMeasures

/-! # The full endpoint moment measure of finite chains

Positive tensor moments determine the expected endpoint tuple measure.
Finite form bounds supply the covering-rectangle finiteness required for
uniqueness. The chains are represented by measurable, everywhere locally
finite modifications equal to the literal chains almost surely.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Any measurable locally finite modifications of the chains have the literal chain-kernel moment measure. -/
theorem bind_endpointTupleMeasure_chain_eq {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (K : ℕ) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4)
    (w : Fin n → ℕ → ℕ → Plane → ℝ) (hw : ∀ i k, IsL2ApplicableMollifier (w i k)) (ℓ : ℕ)
    (C : Fin n → Ω → Measure (Plane × Plane)) (hCm : ∀ i, Measurable (C i))
    (hClf : ∀ i ω, IsLocallyFiniteMeasure (C i ω))
    (hCeq : ∀ i, C i =ᵐ[P] fun ω => chainProduct (fun k => B k ω) (fun k => w i k ℓ) K) :
    P.bind (fun ω => endpointTupleMeasure (fun i => C i ω)) =
      volume.withDensity (Function.uncurry (chainMomentKernel n θ τ (fun i k => w i k ℓ) K)) := by
  let ν := P.bind (fun ω => endpointTupleMeasure (fun i => C i ω))
  have hνm := measurable_endpointTupleMeasure C hCm hClf
  have hmeanTensor (f g : Fin n → Plane → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i)) :
      (∫⁻ q, (∏ i, f i (q.1 i)) * ∏ i, g i (q.2 i) ∂ν) =
        ∫⁻ x, ∫⁻ y, (∏ i, f i (x i)) *
          chainMomentKernel n θ τ (fun i k => w i k ℓ) K x y * ∏ i, g i (y i) := by
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
          ∂chainProduct (fun k => B k ω) (fun k => w i k ℓ) K ∂P := by
        apply lintegral_congr_ae
        filter_upwards [ae_all_iff.2 hCeq] with ω hω
        apply Finset.prod_congr rfl
        intro i _
        rw [hω i]
      _ = _ := lintegral_prod_chainProduct_eq K τ hτ B hB hind hn1 hn (fun i k => w i k ℓ)
        (fun i k => (hw i k).1 ℓ) (fun i k => ((hw i k).2.1 ℓ).measurable) f g hf hg
  have hKm (k) : Measurable (Function.uncurry (momentKernel n θ (τ k))) :=
    Measurable.comp
      (g := fun p : (ℝ × ℝ) × Configuration n × Configuration n =>
        momentKernel n p.1.1 p.1.2 p.2.1 p.2.2)
      (f := fun q : Configuration n × Configuration n => ((θ, τ k), q))
      (measurable_momentKernel n) (measurable_const.prodMk measurable_id)
  have hchain := measurable_chainKernel (fun k => momentKernel n θ (τ k)) hKm
    (fun i k => w i k ℓ) (fun i k => ((hw i k).2.1 ℓ).measurable) K
  obtain ⟨M, hMfin, hMF⟩ := exists_formBound_chainMomentKernel_uniform θ K τ hτ w hw
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
        ∂volume.withDensity (Function.uncurry (chainMomentKernel n θ τ (fun i k => w i k ℓ) K)) :=
      measure_configurationRectangle_eq_lintegral_tensor _ A D hA hD
    _ = ∫⁻ x, ∫⁻ y, (∏ i, f i (x i)) *
        chainMomentKernel n θ τ (fun i k => w i k ℓ) K x y * ∏ i, g i (y i) :=
      lintegral_kernelMeasure_mul hchain hfp hgp
    _ = ∫⁻ q, (∏ i, f i (q.1 i)) * ∏ i, g i (q.2 i) ∂ν := (hmeanTensor f g hf hg).symm
    _ = _ := (measure_configurationRectangle_eq_lintegral_tensor _ A D hA hD).symm

/-- The literal chains admit locally finite measurable modifications with the full endpoint moment measure. -/
theorem exists_chain_endpointTuple_moment_measure {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (K : ℕ) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4)
    (w : Fin n → ℕ → ℕ → Plane → ℝ) (hw : ∀ i k, IsL2ApplicableMollifier (w i k)) (ℓ : ℕ) :
    ∃ C : Fin n → Ω → Measure (Plane × Plane), (∀ i, Measurable (C i)) ∧
      (∀ i ω, IsLocallyFiniteMeasure (C i ω)) ∧
      (∀ i, C i =ᵐ[P] fun ω => chainProduct (fun k => B k ω) (fun k => w i k ℓ) K) ∧
      P.bind (fun ω => endpointTupleMeasure (fun i => C i ω)) =
        volume.withDensity (Function.uncurry (chainMomentKernel n θ τ (fun i k => w i k ℓ) K)) := by
  let E := CompactExhaustion.choice (Plane × Plane)
  have hmods (i : Fin n) := RandomMeasure.exists_measurable_locallyFinite_modification E P
    (fun ω => chainProduct (fun k => B k ω) (fun k => w i k ℓ) K)
    (aemeasurable_chainProduct P K B (fun k hk => (hB k hk).1) (fun k hk => (hB k hk).2.1)
      _ (fun k => ((hw i k).2.1 ℓ).measurable))
    (ae_locallyFinite_chainProduct K τ hτ B hB hind (w i) (hw i) ℓ)
  choose C hCm hClf hCeq using hmods
  exact ⟨C, hCm, hClf, hCeq, bind_endpointTupleMeasure_chain_eq K τ hτ B hB hind hn1 hn w hw ℓ C hCm hClf hCeq⟩

end Critical2DKPZ.SHF.Tsai

end
