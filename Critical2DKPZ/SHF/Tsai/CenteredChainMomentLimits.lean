/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CenteredChainMoments
public import Critical2DKPZ.SHF.Tsai.ChainKernelLimits

/-! # Removing connectors in heat-centered chain moments

Each integrable subset term converges by the strong L2 connector theorem.
Finite inclusion-exclusion then gives the exact connector-free signed
limit, before any quantitative bound on the centered kernel is imposed.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Centered chain product moments converge to their connector-free signed kernel form.
Integrability for every index is `integral_prod_centeredChainPairings_eq`. -/
theorem tendsto_integral_prod_centeredChainPairings {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (K j : ℕ) (hj : j ≤ K) (τ : ℕ → ℝ)
    (hτ : ∀ k ≤ K, 0 < τ k) (B : ℕ → Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4)
    (w : Fin n → ℕ → ℕ → Plane → ℝ) (hw : ∀ i k, IsL2ApplicableMollifier (w i k))
    (g g' : Fin n → Plane → ℝ) (hg : ∀ i, MemLp (g i) 2) (hg' : ∀ i, MemLp (g' i) 2) :
    Tendsto (fun ℓ => ∫ ω, ∏ i,
      ((∫ p, g i p.1 * g' i p.2 ∂chainProduct (fun k => B k ω) (fun k => w i k ℓ) K) -
        ∫ p, g i p.1 * g' i p.2 ∂chainProduct
          (Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w i k ℓ) K) ∂P)
      atTop (𝓝 (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, (-1 : ℝ) ^ S.card *
        ∫ x, ∫ y, (∏ i, g i (x i)) *
          (chainKernelLimit n (Function.update (fun k => momentKernel n θ (τ k)) j
            (mixedBlockKernel n θ (τ j) Sᶜ)) K x y).toReal * ∏ i, g' i (y i))) := by
  classical
  let G (x : Configuration n) := ∏ i, g i (x i)
  let F (y : Configuration n) := ∏ i, g' i (y i)
  have hG : MemLp G 2 := memLp_configuration_tensor g hg
  have hF : MemLp F 2 := memLp_configuration_tensor g' hg'
  have hlim (S : Finset (Fin n)) :
      Tendsto (fun ℓ => ∫ x, ∫ y, G x *
        (chainKernel n (Function.update (fun k => momentKernel n θ (τ k)) j
          (mixedBlockKernel n θ (τ j) Sᶜ)) (fun i k => w i k ℓ) K x y).toReal * F y)
        atTop (𝓝 (∫ x, ∫ y, G x *
          (chainKernelLimit n (Function.update (fun k => momentKernel n θ (τ k)) j
            (mixedBlockKernel n θ (τ j) Sᶜ)) K x y).toReal * F y)) := by
    obtain ⟨c, hc, hQ⟩ := exists_formBounds_momentKernel_update_mixed θ K j hj τ hτ Sᶜ
    exact tendsto_integral_chainKernel K _
      (fun k _ => measurable_momentKernel_update_mixed n θ τ j Sᶜ k) c hc hQ w hw G F hG hF
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin n)).powerset
    (fun S _ => (hlim S).const_mul ((-1 : ℝ) ^ S.card))
  apply hsum.congr
  intro ℓ
  exact (integral_prod_centeredChainPairings_eq K j hj τ hτ B hB hind hn1 hn w hw ℓ g g' hg hg').2.symm

end Critical2DKPZ.SHF.Tsai

end
