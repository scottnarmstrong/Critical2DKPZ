/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainKernels
public import Critical2DKPZ.SHF.Tsai.KernelCompositionOperators
public import Critical2DKPZ.SHF.Tsai.KernelOperatorSymmetry

/-! # Two-kernel forms on transformed endpoint tests

Absolute integrability and the canonical composition operator identify the
literal two-kernel chain with an operator pairing. A symmetric prefix can
then be moved onto the left endpoint test.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- A two-kernel form is the pairing of the two composed operators, with absolute integrability. -/
theorem integral_chainKernelLimit_two_eq {n : ℕ}
    (L R : Configuration n → Configuration n → ℝ≥0∞)
    (hL : Measurable (Function.uncurry L)) (hR : Measurable (Function.uncurry R))
    {cL cR : ℝ≥0∞} (hcL : cL ≠ ⊤) (hcR : cR ≠ ⊤)
    (hQL : FormBound volume volume L cL) (hQR : FormBound volume volume R cR)
    (G F : Configuration n → ℝ) (hG : MemLp G 2) (hF : MemLp F 2) :
    Integrable (fun q : Configuration n × Configuration n =>
      G q.1 * (chainKernelLimit n (fun k => if k = 0 then L else R) 1 q.1 q.2).toReal * F q.2)
      (volume.prod volume) ∧
    (∫ x, ∫ y, G x * (chainKernelLimit n (fun k => if k = 0 then L else R) 1 x y).toReal * F y) =
      ⟪configurationKernelOperator hL hcL hQL (configurationKernelOperator hR hcR hQR (hF.toLp F)),
        hG.toLp G⟫_ℝ := by
  have hKm := measurable_spatialKernelComp volume hL hR
  have hfin := ENNReal.mul_ne_top hcL hcR
  have hBound := hQL.comp volume volume volume hL hR hQR
  have heq : chainKernelLimit n (fun k => if k = 0 then L else R) 1 = spatialKernelComp volume L R := rfl
  rw [heq]
  refine ⟨(configurationKernel_real_form_bound hKm hfin hBound G F hG hF).1, ?_⟩
  have h := inner_configurationKernelOperator_toLp hKm hfin hBound hG hF
  rw [configurationKernelOperator_comp hL hR hcL hcR hQL hQR] at h
  exact h.symm

/-- A symmetric prefix in a two-kernel form transfers to the left endpoint test. -/
theorem integral_chainKernelLimit_two_eq_of_symm {n : ℕ}
    (L R : Configuration n → Configuration n → ℝ≥0∞)
    (hL : Measurable (Function.uncurry L)) (hR : Measurable (Function.uncurry R))
    {cL cR : ℝ≥0∞} (hcL : cL ≠ ⊤) (hcR : cR ≠ ⊤)
    (hQL : FormBound volume volume L cL) (hQR : FormBound volume volume R cR)
    (hSymm : ∀ x y, L x y = L y x)
    (G F : Configuration n → ℝ) (hG : MemLp G 2) (hF : MemLp F 2) :
    (∫ x, ∫ y, G x * (chainKernelLimit n (fun k => if k = 0 then L else R) 1 x y).toReal * F y) =
      ⟪configurationKernelOperator hR hcR hQR (hF.toLp F),
        configurationKernelOperator hL hcL hQL (hG.toLp G)⟫_ℝ :=
  (integral_chainKernelLimit_two_eq L R hL hR hcL hcR hQL hQR G F hG hF).2.trans
    (inner_configurationKernelOperator_symm hL hcL hQL hSymm _ _)

end Critical2DKPZ.SHF.Tsai

end
