/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CenteredThreeKernelForms
public import Critical2DKPZ.SHF.Tsai.MomentOperatorKernelAction
import Critical2DKPZ.SHF.DeltaBose.EndpointSymmetry

/-! # Moment operators in centered three-kernel forms

The signed three-kernel form with a centered middle block equals the centered-kernel
pairing of the two endpoint tests transformed by their moment operators.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

private theorem centered_form_congr {n : ℕ} (θ τ a : ℝ)
    {G F G' F' : Configuration n → ℝ} (hG : G = G') (hF : F = F')
    (h : a = ∫ x, ∫ y, G x * centeredMomentKernel n θ τ x y * F y) :
    a = ∫ x, ∫ y, G' x * centeredMomentKernel n θ τ x y * F' y := by
  cases hG
  cases hF
  exact h


/-- The centered three-kernel form equals the centered-kernel pairing of moment-transformed endpoint tests; spatial integrability follows from `integrable_centeredMomentKernel_real_form`. -/
theorem integral_sum_momentKernel_centered_middle_eq {n : ℕ} (hn : n ≤ 4) (θ : ℝ)
    {s τ t : ℝ} (hs : 0 < s) (hτ : 0 < τ) (ht : 0 < t)
    (G F : Configuration n → ℝ) (hG : MemLp G 2) (hF : MemLp F 2) :
    let G₀ : Configuration n → ℝ := momentOperator hn θ hs (hG.toLp G)
    let F₀ : Configuration n → ℝ := momentOperator hn θ ht (hF.toLp F)
    (∑ S : Finset (Fin n), (-1 : ℝ) ^ S.card *
      ∫ x, ∫ y, G x * (chainKernelLimit n
        (fun k => if k = 0 then momentKernel n θ s else
          if k = 1 then mixedBlockKernel n θ τ Sᶜ else momentKernel n θ t) 2 x y).toReal * F y) =
      ∫ x, ∫ y, G₀ x * centeredMomentKernel n θ τ x y * F₀ y := by
  obtain ⟨C, rate, _hC, hQ⟩ := exists_formBound_momentKernel n θ
  have hQL := hQ θ le_rfl s hs
  have hQR := hQ θ le_rfl t ht
  have hK (u : ℝ) : Measurable (Function.uncurry (momentKernel n θ u)) :=
    Measurable.comp
      (g := fun p : (ℝ × ℝ) × Configuration n × Configuration n =>
        momentKernel n p.1.1 p.1.2 p.2.1 p.2.2)
      (f := fun q : Configuration n × Configuration n => ((θ, u), q))
      (measurable_momentKernel n) (measurable_const.prodMk measurable_id)
  have h := integral_sum_chainKernelLimit_centered_middle_eq θ hτ
    (momentKernel n θ s) (momentKernel n θ t) (hK s) (hK t)
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top hQL hQR (momentKernel_symm n θ s) G F hG hF
  have hEqL := (momentOperator_eq_configurationKernelOperator hn θ hs (hK s)
    ENNReal.ofReal_ne_top hQL).symm
  have hEqR := (momentOperator_eq_configurationKernelOperator hn θ ht (hK t)
    ENNReal.ofReal_ne_top hQR).symm
  have hGL := congrArg (fun Q : Lp ℝ 2 (volume : Measure (Configuration n)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Configuration n)) =>
      (Q (hG.toLp G) : Configuration n → ℝ)) hEqL
  have hFR := congrArg (fun Q : Lp ℝ 2 (volume : Measure (Configuration n)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Configuration n)) =>
      (Q (hF.toLp F) : Configuration n → ℝ)) hEqR
  exact centered_form_congr θ τ _ hGL hFR h.2

end Critical2DKPZ.SHF.Tsai

end
