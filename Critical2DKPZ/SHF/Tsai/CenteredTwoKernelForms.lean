/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.TwoKernelForms
public import Critical2DKPZ.SHF.Tsai.CenteredKernelForms

/-! # Centered endpoint blocks in two-kernel forms

Finite inclusion-exclusion combines the mixed endpoint kernels into the
literal signed centered kernel. The other block acts on its endpoint test;
a prefix operator is transferred by symmetry. All signed forms are integrable.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- A centered first block is paired with the suffix-transformed right endpoint test. -/
theorem integral_sum_chainKernelLimit_centered_first_eq {n : ℕ} (θ : ℝ) {τ : ℝ} (hτ : 0 < τ)
    (R : Configuration n → Configuration n → ℝ≥0∞) (hR : Measurable (Function.uncurry R))
    {cR : ℝ≥0∞} (hcR : cR ≠ ⊤) (hQR : FormBound volume volume R cR)
    (G F : Configuration n → ℝ) (hG : MemLp G 2) (hF : MemLp F 2) :
    let F₀ := configurationKernelOperator hR hcR hQR (hF.toLp F)
    Integrable (fun q : Configuration n × Configuration n =>
      G q.1 * centeredMomentKernel n θ τ q.1 q.2 * F₀ q.2) (volume.prod volume) ∧
    (∑ S : Finset (Fin n), (-1 : ℝ) ^ S.card *
      ∫ x, ∫ y, G x * (chainKernelLimit n
        (fun k => if k = 0 then mixedBlockKernel n θ τ Sᶜ else R) 1 x y).toReal * F y) =
      ∫ x, ∫ y, G x * centeredMomentKernel n θ τ x y * F₀ y := by
  classical
  let F₀ := configurationKernelOperator hR hcR hQR (hF.toLp F)
  refine ⟨integrable_centeredMomentKernel_real_form n θ hτ G F₀ hG (Lp.memLp F₀), ?_⟩
  rw [integral_centeredMomentKernel_real_form_eq_sum_compl n θ hτ G F₀ hG (Lp.memLp F₀)]
  apply Finset.sum_congr rfl
  intro S _
  congr 1
  obtain ⟨c, hc, hQ⟩ := exists_formBound_mixedBlockKernel n Sᶜ θ hτ
  have hM := measurable_mixedBlockKernel n θ τ Sᶜ
  have hOp := (integral_chainKernelLimit_two_eq (mixedBlockKernel n θ τ Sᶜ) R
    hM hR hc hcR hQ hQR G F hG hF).2
  rw [hOp]
  have hRep := inner_configurationKernelOperator_toLp hM hc hQ hG (Lp.memLp F₀)
  rw [Lp.toLp_coeFn] at hRep
  exact hRep

/-- A centered last block is paired with the prefix-transformed left endpoint test. -/
theorem integral_sum_chainKernelLimit_centered_last_eq {n : ℕ} (θ : ℝ) {τ : ℝ} (hτ : 0 < τ)
    (L : Configuration n → Configuration n → ℝ≥0∞) (hL : Measurable (Function.uncurry L))
    {cL : ℝ≥0∞} (hcL : cL ≠ ⊤) (hQL : FormBound volume volume L cL)
    (hLSymm : ∀ x y, L x y = L y x)
    (G F : Configuration n → ℝ) (hG : MemLp G 2) (hF : MemLp F 2) :
    let G₀ := configurationKernelOperator hL hcL hQL (hG.toLp G)
    Integrable (fun q : Configuration n × Configuration n =>
      G₀ q.1 * centeredMomentKernel n θ τ q.1 q.2 * F q.2) (volume.prod volume) ∧
    (∑ S : Finset (Fin n), (-1 : ℝ) ^ S.card *
      ∫ x, ∫ y, G x * (chainKernelLimit n
        (fun k => if k = 0 then L else mixedBlockKernel n θ τ Sᶜ) 1 x y).toReal * F y) =
      ∫ x, ∫ y, G₀ x * centeredMomentKernel n θ τ x y * F y := by
  classical
  let G₀ := configurationKernelOperator hL hcL hQL (hG.toLp G)
  refine ⟨integrable_centeredMomentKernel_real_form n θ hτ G₀ F (Lp.memLp G₀) hF, ?_⟩
  rw [integral_centeredMomentKernel_real_form_eq_sum_compl n θ hτ G₀ F (Lp.memLp G₀) hF]
  apply Finset.sum_congr rfl
  intro S _
  congr 1
  obtain ⟨c, hc, hQ⟩ := exists_formBound_mixedBlockKernel n Sᶜ θ hτ
  have hM := measurable_mixedBlockKernel n θ τ Sᶜ
  calc
    _ = ⟪configurationKernelOperator hM hc hQ (hF.toLp F), G₀⟫_ℝ :=
      integral_chainKernelLimit_two_eq_of_symm L (mixedBlockKernel n θ τ Sᶜ)
        hL hM hcL hc hQL hQ hLSymm G F hG hF
    _ = _ := by
      have hRep := inner_configurationKernelOperator_toLp hM hc hQ (Lp.memLp G₀) hF
      rw [Lp.toLp_coeFn] at hRep
      exact hRep

end Critical2DKPZ.SHF.Tsai

end
