/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CenteredChainMomentLimits
public import Critical2DKPZ.SHF.Tsai.CenteredMomentKernelForms
public import Critical2DKPZ.SHF.Tsai.TensorMoments

/-! # The literal centered moment limit for three blocks

The connector-free mixed-kernel expansion collapses onto the centered middle
kernel. Its two endpoint tests are transformed by the canonical moment
operators of the prefix and suffix. Both spatial and random-variable forms
remain absolutely integrable.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Three-block centered product moments converge to the centered middle-kernel form on the two moment-transformed tests. Integrability is given by `integral_prod_centeredChainPairings_eq` for the random product and `integrable_centeredMomentKernel_real_form` for the spatial form. -/
theorem tendsto_integral_prod_centeredThreeBlockPairings {θ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (τ : ℕ → ℝ) (hτ : ∀ k ≤ 2, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ 2, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin 3 => B k) P) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4)
    (w : Fin n → ℕ → ℕ → Plane → ℝ) (hw : ∀ i k, IsL2ApplicableMollifier (w i k))
    (g g' : Fin n → Plane → ℝ) (hg : ∀ i, MemLp (g i) 2) (hg' : ∀ i, MemLp (g' i) 2) :
    let G : Configuration n → ℝ := fun x => ∏ i, g i (x i)
    let F : Configuration n → ℝ := fun y => ∏ i, g' i (y i)
    let G₀ : Configuration n → ℝ := momentOperator hn θ (hτ 0 (by omega)) ((memLp_configuration_tensor g hg).toLp G)
    let F₀ : Configuration n → ℝ := momentOperator hn θ (hτ 2 le_rfl) ((memLp_configuration_tensor g' hg').toLp F)
    Tendsto (fun ℓ => ∫ ω, ∏ i, ((∫ p, g i p.1 * g' i p.2
      ∂chainProduct (fun k => B k ω) (fun k => w i k ℓ) 2) -
      ∫ p, g i p.1 * g' i p.2 ∂chainProduct
        (Function.update (fun k => B k ω) 1 (heatBlock (τ 1))) (fun k => w i k ℓ) 2) ∂P)
      atTop (𝓝 (∫ x, ∫ y, G₀ x * centeredMomentKernel n θ (τ 1) x y * F₀ y)) := by
  classical
  let G (x : Configuration n) := ∏ i, g i (x i)
  let F (y : Configuration n) := ∏ i, g' i (y i)
  have hG : MemLp G 2 := memLp_configuration_tensor g hg
  have hF : MemLp F 2 := memLp_configuration_tensor g' hg'
  have hCollapse := integral_sum_momentKernel_centered_middle_eq hn θ
    (hτ 0 (by omega)) (hτ 1 (by omega)) (hτ 2 le_rfl) G F hG hF
  have hLimit := tendsto_integral_prod_centeredChainPairings 2 1 (by omega) τ hτ B hB hind
    hn1 hn w hw g g' hg hg'
  have hKb (S : Finset (Fin n)) :
      chainKernelLimit n (Function.update (fun k => momentKernel n θ (τ k)) 1
        (mixedBlockKernel n θ (τ 1) Sᶜ)) 2 =
      chainKernelLimit n (fun k => if k = 0 then momentKernel n θ (τ 0) else
        if k = 1 then mixedBlockKernel n θ (τ 1) Sᶜ else momentKernel n θ (τ 2)) 2 := by
    apply chainKernelLimit_congr_prefix
    intro k hk
    interval_cases k <;> rfl
  simp only [Finset.powerset_univ, hKb] at hLimit
  have hEq := hCollapse
  dsimp only [G, F] at hEq hCollapse
  rw [hEq] at hLimit
  exact hLimit

end Critical2DKPZ.SHF.Tsai

end
