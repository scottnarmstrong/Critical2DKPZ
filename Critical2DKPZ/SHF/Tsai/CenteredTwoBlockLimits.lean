/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CenteredChainMomentLimits
public import Critical2DKPZ.SHF.Tsai.CenteredMomentEndpointForms
public import Critical2DKPZ.SHF.Tsai.TensorMoments

/-! # Literal centered moment limits for two-block chains

The mixed-kernel connector limits combine into the centered first or last
kernel, with the remaining moment operator acting on the other endpoint.
Random-product integrability is `integral_prod_centeredChainPairings_eq`;
spatial integrability is `integrable_centeredMomentKernel_real_form` applied
to the displayed L² tests.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Centering the first block leaves the suffix semigroup on the right tensor test in the moment limit.
Random-product integrability is `integral_prod_centeredChainPairings_eq`;
spatial integrability is `integrable_centeredMomentKernel_real_form`. -/
theorem tendsto_integral_prod_centeredTwoBlockPairings_first {θ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (τ : ℕ → ℝ) (hτ : ∀ k ≤ 1, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ 1, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin 2 => B k) P) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4)
    (w : Fin n → ℕ → ℕ → Plane → ℝ) (hw : ∀ i k, IsL2ApplicableMollifier (w i k))
    (g g' : Fin n → Plane → ℝ) (hg : ∀ i, MemLp (g i) 2) (hg' : ∀ i, MemLp (g' i) 2) :
    let G : Configuration n → ℝ := fun x => ∏ i, g i (x i)
    let F : Configuration n → ℝ := fun y => ∏ i, g' i (y i)
    let F₀ : Configuration n → ℝ := momentOperator hn θ (hτ 1 le_rfl) ((memLp_configuration_tensor g' hg').toLp F)
    Tendsto (fun ℓ => ∫ ω, ∏ i, ((∫ p, g i p.1 * g' i p.2
      ∂chainProduct (fun k => B k ω) (fun k => w i k ℓ) 1) -
      ∫ p, g i p.1 * g' i p.2 ∂chainProduct
        (Function.update (fun k => B k ω) 0 (heatBlock (τ 0))) (fun k => w i k ℓ) 1) ∂P)
      atTop (𝓝 (∫ x, ∫ y, G x * centeredMomentKernel n θ (τ 0) x y * F₀ y)) := by
  classical
  let G (x : Configuration n) := ∏ i, g i (x i)
  let F (y : Configuration n) := ∏ i, g' i (y i)
  have hG : MemLp G 2 := memLp_configuration_tensor g hg
  have hF : MemLp F 2 := memLp_configuration_tensor g' hg'
  have hCollapse := integral_sum_momentKernel_centered_first_eq hn θ
    (hτ 0 (by omega)) (hτ 1 le_rfl) G F hG hF
  have hLimit := tendsto_integral_prod_centeredChainPairings 1 0 (by omega) τ hτ B hB hind
    hn1 hn w hw g g' hg hg'
  have hKb (S : Finset (Fin n)) :
      chainKernelLimit n (Function.update (fun k => momentKernel n θ (τ k)) 0
        (mixedBlockKernel n θ (τ 0) Sᶜ)) 1 =
      chainKernelLimit n (fun k => if k = 0 then mixedBlockKernel n θ (τ 0) Sᶜ else
        momentKernel n θ (τ 1)) 1 := by
    apply chainKernelLimit_congr_prefix
    intro k hk
    interval_cases k <;> rfl
  simp only [Finset.powerset_univ, hKb] at hLimit
  dsimp only [G, F] at hCollapse
  rwa [hCollapse] at hLimit

/-- Centering the last block leaves the prefix semigroup on the left tensor test in the moment limit.
Random-product integrability is `integral_prod_centeredChainPairings_eq`;
spatial integrability is `integrable_centeredMomentKernel_real_form`. -/
theorem tendsto_integral_prod_centeredTwoBlockPairings_last {θ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (τ : ℕ → ℝ) (hτ : ∀ k ≤ 1, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ 1, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin 2 => B k) P) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4)
    (w : Fin n → ℕ → ℕ → Plane → ℝ) (hw : ∀ i k, IsL2ApplicableMollifier (w i k))
    (g g' : Fin n → Plane → ℝ) (hg : ∀ i, MemLp (g i) 2) (hg' : ∀ i, MemLp (g' i) 2) :
    let G : Configuration n → ℝ := fun x => ∏ i, g i (x i)
    let F : Configuration n → ℝ := fun y => ∏ i, g' i (y i)
    let G₀ : Configuration n → ℝ := momentOperator hn θ (hτ 0 (by omega)) ((memLp_configuration_tensor g hg).toLp G)
    Tendsto (fun ℓ => ∫ ω, ∏ i, ((∫ p, g i p.1 * g' i p.2
      ∂chainProduct (fun k => B k ω) (fun k => w i k ℓ) 1) -
      ∫ p, g i p.1 * g' i p.2 ∂chainProduct
        (Function.update (fun k => B k ω) 1 (heatBlock (τ 1))) (fun k => w i k ℓ) 1) ∂P)
      atTop (𝓝 (∫ x, ∫ y, G₀ x * centeredMomentKernel n θ (τ 1) x y * F y)) := by
  classical
  let G (x : Configuration n) := ∏ i, g i (x i)
  let F (y : Configuration n) := ∏ i, g' i (y i)
  have hG : MemLp G 2 := memLp_configuration_tensor g hg
  have hF : MemLp F 2 := memLp_configuration_tensor g' hg'
  have hCollapse := integral_sum_momentKernel_centered_last_eq hn θ
    (hτ 0 (by omega)) (hτ 1 le_rfl) G F hG hF
  have hLimit := tendsto_integral_prod_centeredChainPairings 1 1 le_rfl τ hτ B hB hind
    hn1 hn w hw g g' hg hg'
  have hKb (S : Finset (Fin n)) :
      chainKernelLimit n (Function.update (fun k => momentKernel n θ (τ k)) 1
        (mixedBlockKernel n θ (τ 1) Sᶜ)) 1 =
      chainKernelLimit n (fun k => if k = 0 then momentKernel n θ (τ 0) else
        mixedBlockKernel n θ (τ 1) Sᶜ) 1 := by
    apply chainKernelLimit_congr_prefix
    intro k hk
    interval_cases k <;> rfl
  simp only [Finset.powerset_univ, hKb] at hLimit
  dsimp only [G, F] at hCollapse
  rwa [hCollapse] at hLimit

end Critical2DKPZ.SHF.Tsai

end
