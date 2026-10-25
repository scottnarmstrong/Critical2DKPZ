/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainKernelOperators
public import Critical2DKPZ.SHF.Tsai.KernelOperatorSymmetry

/-! # Collapsing a three-kernel form onto its middle block

The connector-free chain is the composition of the three bounded integral
operators. Symmetry of its first kernel moves the prefix operator onto the
left endpoint test. Its positive form bound supplies absolute integrability.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- An integrable three-kernel form is the middle-operator pairing of the two outer transformed tests. -/
theorem integral_chainKernelLimit_three_eq {n : ℕ}
    (L M R : Configuration n → Configuration n → ℝ≥0∞)
    (hL : Measurable (Function.uncurry L)) (hM : Measurable (Function.uncurry M))
    (hR : Measurable (Function.uncurry R)) {cL cM cR : ℝ≥0∞}
    (hcL : cL ≠ ⊤) (hcM : cM ≠ ⊤) (hcR : cR ≠ ⊤)
    (hQL : FormBound volume volume L cL) (hQM : FormBound volume volume M cM)
    (hQR : FormBound volume volume R cR) (hLSymm : ∀ x y, L x y = L y x)
    (G F : Configuration n → ℝ) (hG : MemLp G 2) (hF : MemLp F 2) :
    let Kb (k : ℕ) := if k = 0 then L else if k = 1 then M else R
    Integrable (fun q : Configuration n × Configuration n =>
      G q.1 * (chainKernelLimit n Kb 2 q.1 q.2).toReal * F q.2) (volume.prod volume) ∧
    (∫ x, ∫ y, G x * (chainKernelLimit n Kb 2 x y).toReal * F y) =
      ⟪configurationKernelOperator hM hcM hQM
        (configurationKernelOperator hR hcR hQR (hF.toLp F)),
        configurationKernelOperator hL hcL hQL (hG.toLp G)⟫_ℝ := by
  classical
  let Kb (k : ℕ) := if k = 0 then L else if k = 1 then M else R
  let c (k : ℕ) := if k = 0 then cL else if k = 1 then cM else cR
  have hKb (k : ℕ) : Measurable (Function.uncurry (Kb k)) := by
    dsimp only [Kb]
    split_ifs
    · exact hL
    · exact hM
    · exact hR
  have hc (k : ℕ) : c k ≠ ⊤ := by
    dsimp only [c]
    split_ifs
    · exact hcL
    · exact hcM
    · exact hcR
  have hQ (k : ℕ) : FormBound volume volume (Kb k) (c k) := by
    dsimp only [Kb, c]
    split_ifs
    · exact hQL
    · exact hQM
    · exact hQR
  obtain ⟨C, hC, hBound, hOp⟩ := exists_chainKernelLimitOperator_eq Kb hKb c hc hQ 2
  have hKernelMeas := measurable_chainKernelLimit Kb hKb 2
  refine ⟨(configurationKernel_real_form_bound hKernelMeas hC hBound G F hG hF).1, ?_⟩
  have hActual := inner_configurationKernelOperator_toLp hKernelMeas hC hBound hG hF
  rw [hOp] at hActual
  have hApply : operatorChain (fun k => configurationKernelOperator (hKb k) (hc k) (hQ k))
      (fun _ => ContinuousLinearMap.id ℝ _) 2 (hF.toLp F) =
      configurationKernelOperator hL hcL hQL
        (configurationKernelOperator hM hcM hQM
          (configurationKernelOperator hR hcR hQR (hF.toLp F))) := by rfl
  rw [hApply] at hActual
  exact hActual.symm.trans (inner_configurationKernelOperator_symm hL hcL hQL hLSymm _ _)

end Critical2DKPZ.SHF.Tsai

end
