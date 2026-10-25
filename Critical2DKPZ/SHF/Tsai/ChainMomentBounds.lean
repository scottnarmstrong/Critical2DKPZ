/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.SignedChainMoments
public import Critical2DKPZ.SHF.Tsai.ChainMomentFormBounds
public import Critical2DKPZ.SHF.Tsai.ConfigurationKernelForms

/-! # Uniform moment bounds for endpoint chain tests

For fixed applicable mollifier families, one constant controls every approximation index
and all `L²` endpoint tests through their norms, with integrability of the product moments through order four.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Products of up to four chain pairings are integrable, and their expectations are bounded in absolute value by the endpoint `L²` norms with one constant uniform in the mollifier index and tests. -/
theorem exists_chainPairing_moment_bound {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (K : ℕ) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4) (w : Fin n → ℕ → ℕ → Plane → ℝ)
    (hw : ∀ i k, IsL2ApplicableMollifier (w i k)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ : ℕ) (g g' : Fin n → Plane → ℝ),
      (∀ i, MemLp (g i) 2) → (∀ i, MemLp (g' i) 2) →
      Integrable (fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2
        ∂chainProduct (fun k => B k ω) (fun k => w i k ℓ) K) P ∧
      |∫ ω, ∏ i, (∫ p, g i p.1 * g' i p.2
        ∂chainProduct (fun k => B k ω) (fun k => w i k ℓ) K) ∂P| ≤
        C * (∏ i, (eLpNorm (g i) 2).toReal) * ∏ i, (eLpNorm (g' i) 2).toReal := by
  obtain ⟨C, hCfin, hC⟩ := exists_formBound_chainMomentKernel_uniform θ K τ hτ w hw
  refine ⟨C.toReal, ENNReal.toReal_nonneg, fun ℓ g g' hg hg' => ?_⟩
  have hmom := integral_prod_chainProduct_eq K τ hτ B hB hind hn1 hn w hw ℓ g g' hg hg'
  refine ⟨hmom.2.1, ?_⟩
  let G (x : Configuration n) := ∏ i, g i (x i)
  let F (y : Configuration n) := ∏ i, g' i (y i)
  have hG : MemLp G 2 := memLp_configuration_tensor g hg
  have hF : MemLp F 2 := memLp_configuration_tensor g' hg'
  have hKm := measurable_chainMomentKernel n θ τ (fun i k => w i k ℓ)
    (fun i k => ((hw i k).2.1 ℓ).measurable) K
  have hform := configurationKernel_real_form_bound hKm hCfin (hC ℓ) G F hG hF
  have hnormG : (eLpNorm G 2).toReal = ∏ i, (eLpNorm (g i) 2).toReal := by
    simpa only [tensorLp, Lp.norm_toLp] using norm_tensorLp g hg
  have hnormF : (eLpNorm F 2).toReal = ∏ i, (eLpNorm (g' i) 2).toReal := by
    simpa only [tensorLp, Lp.norm_toLp] using norm_tensorLp g' hg'
  rw [hmom.2.2, ← integral_prod _ hform.1]
  simpa only [hnormG, hnormF] using hform.2

/-- The chain pairing has an integrable second moment bounded by the squared endpoint `L²` norms, uniformly in the mollifier index. -/
theorem exists_chainPairing_sq_bound {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (K : ℕ) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ : ℕ) (g g' : Plane → ℝ), MemLp g 2 → MemLp g' 2 →
      Integrable (fun ω => (∫ p, g p.1 * g' p.2
        ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) ^ 2) P ∧
      (∫ ω, (∫ p, g p.1 * g' p.2
        ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) ^ 2 ∂P) ≤
        C * (eLpNorm g 2).toReal ^ 2 * (eLpNorm g' 2).toReal ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_chainPairing_moment_bound K τ hτ B hB hind
    (n := 2) (by norm_num) (by norm_num) (fun _ => w) (fun _ => hw)
  refine ⟨C, hC, fun ℓ g g' hg hg' => ?_⟩
  have h := hbound ℓ (fun _ => g) (fun _ => g') (fun _ => hg) (fun _ => hg')
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  exact ⟨h.1, (le_abs_self _).trans h.2⟩

end Critical2DKPZ.SHF.Tsai

end
