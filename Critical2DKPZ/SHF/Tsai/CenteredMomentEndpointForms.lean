/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CenteredTwoKernelForms
public import Critical2DKPZ.SHF.Tsai.MomentOperatorKernelAction
import Critical2DKPZ.SHF.DeltaBose.EndpointSymmetry

/-! # Canonical semigroup tests in centered endpoint forms

The positive outer block becomes its canonical moment operator, while the
centered endpoint remains the literal signed kernel. Spatial integrability
is supplied by `integrable_centeredMomentKernel_real_form` on the actual L²
test and the L² representative of the transformed test.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

private theorem measurable_fixed_momentKernel (n : ℕ) (θ u : ℝ) :
    Measurable (Function.uncurry (momentKernel n θ u)) :=
  Measurable.comp
    (g := fun p : (ℝ × ℝ) × Configuration n × Configuration n =>
      momentKernel n p.1.1 p.1.2 p.2.1 p.2.2)
    (f := fun q : Configuration n × Configuration n => ((θ, u), q))
    (measurable_momentKernel n) (measurable_const.prodMk measurable_id)

/-- A centered first moment block leaves the canonical suffix semigroup on the right test. -/
theorem integral_sum_momentKernel_centered_first_eq {n : ℕ} (hn : n ≤ 4) (θ : ℝ)
    {τ t : ℝ} (hτ : 0 < τ) (ht : 0 < t)
    (G F : Configuration n → ℝ) (hG : MemLp G 2) (hF : MemLp F 2) :
    let F₀ : Configuration n → ℝ := momentOperator hn θ ht (hF.toLp F)
    (∑ S : Finset (Fin n), (-1 : ℝ) ^ S.card *
      ∫ x, ∫ y, G x * (chainKernelLimit n
        (fun k => if k = 0 then mixedBlockKernel n θ τ Sᶜ else momentKernel n θ t) 1 x y).toReal * F y) =
      ∫ x, ∫ y, G x * centeredMomentKernel n θ τ x y * F₀ y := by
  obtain ⟨C, rate, _hC, hQ⟩ := exists_formBound_momentKernel n θ
  have hQR := hQ θ le_rfl t ht
  have hK := measurable_fixed_momentKernel n θ t
  have h := integral_sum_chainKernelLimit_centered_first_eq θ hτ (momentKernel n θ t)
    hK ENNReal.ofReal_ne_top hQR G F hG hF
  have hEq := (momentOperator_eq_configurationKernelOperator hn θ ht hK ENNReal.ofReal_ne_top hQR).symm
  have hFR := congrArg (fun Q : Lp ℝ 2 (volume : Measure (Configuration n)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Configuration n)) =>
      (Q (hF.toLp F) : Configuration n → ℝ)) hEq
  exact h.2.trans (congrArg (fun F' : Configuration n → ℝ =>
    ∫ x, ∫ y, G x * centeredMomentKernel n θ τ x y * F' y) hFR)

/-- A centered last moment block leaves the canonical prefix semigroup on the left test. -/
theorem integral_sum_momentKernel_centered_last_eq {n : ℕ} (hn : n ≤ 4) (θ : ℝ)
    {s τ : ℝ} (hs : 0 < s) (hτ : 0 < τ)
    (G F : Configuration n → ℝ) (hG : MemLp G 2) (hF : MemLp F 2) :
    let G₀ : Configuration n → ℝ := momentOperator hn θ hs (hG.toLp G)
    (∑ S : Finset (Fin n), (-1 : ℝ) ^ S.card *
      ∫ x, ∫ y, G x * (chainKernelLimit n
        (fun k => if k = 0 then momentKernel n θ s else mixedBlockKernel n θ τ Sᶜ) 1 x y).toReal * F y) =
      ∫ x, ∫ y, G₀ x * centeredMomentKernel n θ τ x y * F y := by
  obtain ⟨C, rate, _hC, hQ⟩ := exists_formBound_momentKernel n θ
  have hQL := hQ θ le_rfl s hs
  have hK := measurable_fixed_momentKernel n θ s
  have h := integral_sum_chainKernelLimit_centered_last_eq θ hτ (momentKernel n θ s)
    hK ENNReal.ofReal_ne_top hQL (momentKernel_symm n θ s) G F hG hF
  have hEq := (momentOperator_eq_configurationKernelOperator hn θ hs hK ENNReal.ofReal_ne_top hQL).symm
  have hGL := congrArg (fun Q : Lp ℝ 2 (volume : Measure (Configuration n)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Configuration n)) =>
      (Q (hG.toLp G) : Configuration n → ℝ)) hEq
  exact h.2.trans (congrArg (fun G' : Configuration n → ℝ =>
    ∫ x, ∫ y, G' x * centeredMomentKernel n θ τ x y * F y) hGL)

end Critical2DKPZ.SHF.Tsai

end
