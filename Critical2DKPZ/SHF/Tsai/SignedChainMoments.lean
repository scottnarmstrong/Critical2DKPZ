/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainEndpointMoments
public import Critical2DKPZ.SHF.Tsai.EndpointMomentIntegration

/-! # Exact signed product moments for endpoint chains

The full endpoint moment measure evaluates arbitrary real `L²` representatives.
Its one-particle specialization supplies integrability inside each actual
chain; its full tuple supplies integrability and the product-moment identity.
This is the signed product formula of dense-time uniqueness, with both integrability clauses.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The literal signed chain moment identity on arbitrary `L²` endpoint representatives,
including almost-sure inner integrability and integrability of the product moment. -/
theorem integral_prod_chainProduct_eq {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (K : ℕ) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4) (w : Fin n → ℕ → ℕ → Plane → ℝ)
    (hw : ∀ i k, IsL2ApplicableMollifier (w i k)) (ℓ : ℕ)
    (g g' : Fin n → Plane → ℝ) (hg : ∀ i, MemLp (g i) 2) (hg' : ∀ i, MemLp (g' i) 2) :
    (∀ᵐ ω ∂P, ∀ i, Integrable (fun p : Plane × Plane => g i p.1 * g' i p.2)
      (chainProduct (fun k => B k ω) (fun k => w i k ℓ) K)) ∧
    Integrable (fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2
      ∂(chainProduct (fun k => B k ω) (fun k => w i k ℓ) K)) P ∧
    ∫ ω, ∏ i, (∫ p, g i p.1 * g' i p.2 ∂(chainProduct (fun k => B k ω) (fun k => w i k ℓ) K)) ∂P =
      ∫ x, ∫ y, (∏ i, g i (x i)) *
        (chainMomentKernel n θ τ (fun i k => w i k ℓ) K x y).toReal * ∏ i, g' i (y i) := by
  obtain ⟨C, hCm, hClf, hCeq, hmean⟩ :=
    exists_chain_endpointTuple_moment_measure K τ hτ B hB hind hn1 hn w hw ℓ
  have hchain := measurable_chainMomentKernel n θ τ (fun i k => w i k ℓ)
    (fun i k => ((hw i k).2.1 ℓ).measurable) K
  obtain ⟨M, hMfin, hMF⟩ := exists_formBound_chainMomentKernel_uniform θ K τ hτ w hw
  obtain ⟨houter, hmoment⟩ := integral_prod_pairings_of_endpointTuple_mean P C hCm hClf
    hchain hMfin (hMF ℓ) hmean g g' hg hg'
  have hinnerC (i : Fin n) : ∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane => g i p.1 * g' i p.2) (C i ω) := by
    have hmean₁ := bind_endpointTupleMeasure_chain_eq K τ hτ B hB hind
      (n := 1) (by norm_num) (by norm_num) (fun _ => w i) (fun _ => hw i) ℓ
      (fun _ => C i) (fun _ => hCm i) (fun _ => hClf i) (fun _ => hCeq i)
    have hchain₁ := measurable_chainMomentKernel 1 θ τ (fun (_ : Fin 1) k => w i k ℓ)
      (fun _ k => ((hw i k).2.1 ℓ).measurable) K
    obtain ⟨M₁, hM₁fin, hM₁F⟩ := exists_formBound_chainMomentKernel_uniform θ K τ hτ
      (fun _ : Fin 1 => w i) (fun _ => hw i)
    exact ae_integrable_pairing_of_endpointTuple_mean P (C i) (hCm i) (hClf i)
      hchain₁ hM₁fin (hM₁F ℓ) hmean₁ (g i) (g' i) (hg i) (hg' i)
  have hCeqall := ae_all_iff.2 hCeq
  have hinner : ∀ᵐ ω ∂P, ∀ i, Integrable (fun p : Plane × Plane => g i p.1 * g' i p.2)
      (chainProduct (fun k => B k ω) (fun k => w i k ℓ) K) := by
    filter_upwards [hCeqall, ae_all_iff.2 hinnerC] with ω hω hωI
    intro i
    rw [← hω i]
    exact hωI i
  have hprod : (fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2 ∂C i ω) =ᵐ[P]
      fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2
        ∂chainProduct (fun k => B k ω) (fun k => w i k ℓ) K := by
    filter_upwards [hCeqall] with ω hω
    apply Finset.prod_congr rfl
    intro i _
    rw [hω i]
  exact ⟨hinner, houter.congr hprod, (integral_congr_ae hprod).symm.trans hmoment⟩

end Critical2DKPZ.SHF.Tsai

end
