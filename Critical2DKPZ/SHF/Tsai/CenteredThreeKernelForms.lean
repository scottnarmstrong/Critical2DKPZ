/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ThreeKernelForms
public import Critical2DKPZ.SHF.Tsai.CenteredKernelForms

/-! # The centered middle block of a three-kernel form

Finite inclusion-exclusion stays inside the middle kernel after the outer
operators have been transferred onto the endpoint tests. Every mixed chain
form is integrable by `integral_chainKernelLimit_three_eq`; the signed middle
form is integrable by `integrable_centeredMomentKernel_real_form`.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The signed three-kernel sum is the centered middle form of the two outer transformed tests. -/
theorem integral_sum_chainKernelLimit_centered_middle_eq {n : ℕ} (θ : ℝ) {τ : ℝ} (hτ : 0 < τ)
    (L R : Configuration n → Configuration n → ℝ≥0∞)
    (hL : Measurable (Function.uncurry L)) (hR : Measurable (Function.uncurry R))
    {cL cR : ℝ≥0∞} (hcL : cL ≠ ⊤) (hcR : cR ≠ ⊤)
    (hQL : FormBound volume volume L cL) (hQR : FormBound volume volume R cR)
    (hLSymm : ∀ x y, L x y = L y x)
    (G F : Configuration n → ℝ) (hG : MemLp G 2) (hF : MemLp F 2) :
    let G₀ := configurationKernelOperator hL hcL hQL (hG.toLp G)
    let F₀ := configurationKernelOperator hR hcR hQR (hF.toLp F)
    Integrable (fun q : Configuration n × Configuration n =>
      G₀ q.1 * centeredMomentKernel n θ τ q.1 q.2 * F₀ q.2) (volume.prod volume) ∧
    (∑ S : Finset (Fin n), (-1 : ℝ) ^ S.card *
      ∫ x, ∫ y, G x * (chainKernelLimit n
        (fun k => if k = 0 then L else if k = 1 then mixedBlockKernel n θ τ Sᶜ else R) 2 x y).toReal * F y) =
      ∫ x, ∫ y, G₀ x * centeredMomentKernel n θ τ x y * F₀ y := by
  classical
  let G₀ := configurationKernelOperator hL hcL hQL (hG.toLp G)
  let F₀ := configurationKernelOperator hR hcR hQR (hF.toLp F)
  refine ⟨integrable_centeredMomentKernel_real_form n θ hτ G₀ F₀ (Lp.memLp G₀) (Lp.memLp F₀), ?_⟩
  rw [integral_centeredMomentKernel_real_form_eq_sum_compl n θ hτ G₀ F₀ (Lp.memLp G₀) (Lp.memLp F₀)]
  apply Finset.sum_congr rfl
  intro S _
  congr 1
  obtain ⟨c, hc, hQ⟩ := exists_formBound_mixedBlockKernel n Sᶜ θ hτ
  have hM := measurable_mixedBlockKernel n θ τ Sᶜ
  calc
    _ = ⟪configurationKernelOperator hM hc hQ F₀, G₀⟫_ℝ :=
      (integral_chainKernelLimit_three_eq L (mixedBlockKernel n θ τ Sᶜ) R
        hL hM hR hcL hc hcR hQL hQ hQR hLSymm G F hG hF).2
    _ = ∫ q : Configuration n × Configuration n,
        G₀ q.1 * (mixedBlockKernel n θ τ Sᶜ q.1 q.2).toReal * F₀ q.2 ∂volume.prod volume :=
      inner_configurationKernelOperator hM hc hQ G₀ F₀
    _ = _ := integral_prod _ (configurationKernel_real_form_bound hM hc hQ G₀ F₀
      (Lp.memLp G₀) (Lp.memLp F₀)).1

end Critical2DKPZ.SHF.Tsai

end
