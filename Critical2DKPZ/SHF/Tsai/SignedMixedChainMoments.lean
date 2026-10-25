/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.MixedChainEndpointMoments
public import Critical2DKPZ.SHF.Tsai.EndpointMomentIntegration

/-! # Signed moments of partially heat-replaced chains

For independent blocks with delta-Bose moments through order four, signed `L²` endpoint tests
have the mixed chain moment formula, with almost-sure inner integrability and an integrable
product of pairings.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Products of signed chain pairings equal the mixed chain-kernel integral on `L²` endpoint representatives, with almost-sure inner integrability and an integrable product moment. The kernel density is interpreted using `ENNReal.toReal`. -/
theorem integral_prod_chainProduct_update_heat_eq {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (K j : ℕ) (hj : j ≤ K) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4) (S : Finset (Fin n)) (w : Fin n → ℕ → ℕ → Plane → ℝ)
    (hw : ∀ i k, IsL2ApplicableMollifier (w i k)) (ℓ : ℕ)
    (g g' : Fin n → Plane → ℝ) (hg : ∀ i, MemLp (g i) 2) (hg' : ∀ i, MemLp (g' i) 2) :
    (∀ᵐ ω ∂P, ∀ i, Integrable (fun p : Plane × Plane => g i p.1 * g' i p.2)
      (chainProduct (if i ∈ S then (fun k => B k ω) else
        Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w i k ℓ) K)) ∧
    Integrable (fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2
      ∂(chainProduct (if i ∈ S then (fun k => B k ω) else
        Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w i k ℓ) K)) P ∧
    ∫ ω, ∏ i, (∫ p, g i p.1 * g' i p.2 ∂(chainProduct (if i ∈ S then (fun k => B k ω) else
        Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w i k ℓ) K)) ∂P =
      ∫ x, ∫ y, (∏ i, g i (x i)) *
        (chainKernel n (Function.update (fun k => momentKernel n θ (τ k)) j (mixedBlockKernel n θ (τ j) S)) (fun i k => w i k ℓ) K x y).toReal * ∏ i, g' i (y i) := by
  obtain ⟨C, hCm, hClf, hCeq, hmean⟩ :=
    exists_mixedChain_endpointTuple_moment_measure K j hj τ hτ B hB hind hn1 hn S w hw ℓ
  have hchain := measurable_chainKernel
    (Function.update (fun k => momentKernel n θ (τ k)) j (mixedBlockKernel n θ (τ j) S))
    (measurable_momentKernel_update_mixed n θ τ j S) (fun i k => w i k ℓ)
    (fun i k => ((hw i k).2.1 ℓ).measurable) K
  obtain ⟨M, hMfin, hMF⟩ := exists_formBound_mixedChainKernel_uniform θ K j hj τ hτ S w hw
  obtain ⟨houter, hmoment⟩ := integral_prod_pairings_of_endpointTuple_mean P C hCm hClf
    hchain hMfin (hMF ℓ) hmean g g' hg hg'
  have hinnerC (i : Fin n) : ∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane => g i p.1 * g' i p.2) (C i ω) := by
    classical
    let S₁ : Finset (Fin 1) := if i ∈ S then Finset.univ else ∅
    have hmem (a : Fin 1) : a ∈ S₁ ↔ i ∈ S := by
      by_cases hi : i ∈ S
      · simp only [S₁, ite_eq_left hi, Finset.mem_univ, hi]
      · simp only [S₁, ite_eq_right hi, Finset.notMem_empty, hi]
    have hCeq₁ (a : Fin 1) : C i =ᵐ[P] fun ω => chainProduct
        (if a ∈ S₁ then (fun k => B k ω) else Function.update (fun k => B k ω) j (heatBlock (τ j)))
        (fun k => w i k ℓ) K := by
      simpa only [hmem a] using hCeq i
    have hmean₁ := bind_endpointTupleMeasure_mixedChain_eq K j hj τ hτ B hB hind
      (n := 1) (by norm_num) (by norm_num) S₁ (fun _ => w i) (fun _ => hw i) ℓ
      (fun _ => C i) (fun _ => hCm i) (fun _ => hClf i) hCeq₁
    have hchain₁ := measurable_chainKernel
      (Function.update (fun k => momentKernel 1 θ (τ k)) j (mixedBlockKernel 1 θ (τ j) S₁))
      (measurable_momentKernel_update_mixed 1 θ τ j S₁) (fun (_ : Fin 1) k => w i k ℓ)
      (fun _ k => ((hw i k).2.1 ℓ).measurable) K
    obtain ⟨M₁, hM₁fin, hM₁F⟩ := exists_formBound_mixedChainKernel_uniform θ K j hj τ hτ S₁
      (fun _ : Fin 1 => w i) (fun _ => hw i)
    exact ae_integrable_pairing_of_endpointTuple_mean P (C i) (hCm i) (hClf i)
      hchain₁ hM₁fin (hM₁F ℓ) hmean₁ (g i) (g' i) (hg i) (hg' i)
  have hCeqall := ae_all_iff.2 hCeq
  have hinner : ∀ᵐ ω ∂P, ∀ i, Integrable (fun p : Plane × Plane => g i p.1 * g' i p.2)
      (chainProduct (if i ∈ S then (fun k => B k ω) else
        Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w i k ℓ) K) := by
    filter_upwards [hCeqall, ae_all_iff.2 hinnerC] with ω hω hωI
    intro i
    rw [← hω i]
    exact hωI i
  have hprod : (fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2 ∂C i ω) =ᵐ[P]
      fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2
        ∂chainProduct (if i ∈ S then (fun k => B k ω) else
        Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w i k ℓ) K := by
    filter_upwards [hCeqall] with ω hω
    apply Finset.prod_congr rfl
    intro i _
    rw [hω i]
  exact ⟨hinner, houter.congr hprod, (integral_congr_ae hprod).symm.trans hmoment⟩

end Critical2DKPZ.SHF.Tsai

end
