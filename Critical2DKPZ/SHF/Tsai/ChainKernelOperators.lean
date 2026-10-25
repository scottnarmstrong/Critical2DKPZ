/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConnectorOperators

/-! # Actual operators of finite positive kernel chains

Tonelli's kernel composition is represented by composition of the bounded
integral operators. The finite form constants are constructed along the chain;
the resulting operator is independent of the constants used to construct it.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The operator of a chain kernel is the chain of its actual block and connector operators. -/
theorem exists_chainKernelOperator_eq {n : ℕ}
    (Kb : ℕ → Configuration n → Configuration n → ℝ≥0∞)
    (hKb : ∀ k, Measurable (Function.uncurry (Kb k)))
    (c : ℕ → ℝ≥0∞) (hc : ∀ k, c k ≠ ⊤) (hQ : ∀ k, FormBound volume volume (Kb k) (c k))
    (w : Fin n → ℕ → Plane → ℝ) (hwm : ∀ i k, Measurable (w i k))
    (d : ℕ → ℝ≥0∞) (hd : ∀ k, d k ≠ ⊤)
    (hC : ∀ k, FormBound volume volume (connectorKernel (fun i => w i k)) (d k)) (K : ℕ) :
    ∃ (C : ℝ≥0∞) (hfin : C ≠ ⊤)
      (hF : FormBound volume volume (chainKernel n Kb w K) C),
      configurationKernelOperator (measurable_chainKernel Kb hKb w hwm K) hfin hF =
        operatorChain (fun k => configurationKernelOperator (hKb k) (hc k) (hQ k))
          (fun k => configurationKernelOperator (measurable_connectorKernel _ (fun i => hwm i k))
            (hd k) (hC k)) K := by
  induction K with
  | zero => exact ⟨c 0, hc 0, hQ 0, rfl⟩
  | succ K ih =>
    obtain ⟨C, hfin, hF, hop⟩ := ih
    have hm := measurable_chainKernel Kb hKb w hwm K
    have hcm := measurable_connectorKernel _ (fun i => hwm i K)
    have hlm := measurable_spatialKernelComp volume hcm (hKb (K + 1))
    have hlf := (hC K).comp volume volume volume hcm (hKb (K + 1)) (hQ (K + 1))
    have hlfn := ENNReal.mul_ne_top (hd K) (hc (K + 1))
    have hcomp := hF.comp volume volume volume hm hlm hlf
    have hcompn := ENNReal.mul_ne_top hfin hlfn
    have heq := chainKernel_succ_eq_comp Kb hKb w hwm K
    have hnext : FormBound volume volume (chainKernel n Kb w (K + 1)) (C * (d K * c (K + 1))) := by
      rw [heq]
      exact hcomp
    refine ⟨_, hcompn, hnext, ?_⟩
    calc
      _ = configurationKernelOperator (measurable_spatialKernelComp volume hm hlm) hcompn hcomp :=
        configurationKernelOperator_eq_of_eq heq _ _ _ _ _ _
      _ = (configurationKernelOperator hm hfin hF).comp
          ((configurationKernelOperator hcm (hd K) (hC K)).comp
            (configurationKernelOperator (hKb (K + 1)) (hc (K + 1)) (hQ (K + 1)))) := by
        rw [configurationKernelOperator_comp hm hlm hfin hlfn hF hlf,
          configurationKernelOperator_comp hcm (hKb (K + 1)) (hd K) (hc (K + 1)) (hC K) (hQ (K + 1))]
      _ = _ := by rw [hop]; rfl

/-- Removing the connectors gives the same operator chain with identity connectors. -/
theorem exists_chainKernelLimitOperator_eq {n : ℕ}
    (Kb : ℕ → Configuration n → Configuration n → ℝ≥0∞)
    (hKb : ∀ k, Measurable (Function.uncurry (Kb k)))
    (c : ℕ → ℝ≥0∞) (hc : ∀ k, c k ≠ ⊤) (hQ : ∀ k, FormBound volume volume (Kb k) (c k)) (K : ℕ) :
    ∃ (C : ℝ≥0∞) (hfin : C ≠ ⊤)
      (hF : FormBound volume volume (chainKernelLimit n Kb K) C),
      configurationKernelOperator (measurable_chainKernelLimit Kb hKb K) hfin hF =
        operatorChain (fun k => configurationKernelOperator (hKb k) (hc k) (hQ k))
          (fun _ => ContinuousLinearMap.id ℝ _) K := by
  induction K with
  | zero => exact ⟨c 0, hc 0, hQ 0, rfl⟩
  | succ K ih =>
    obtain ⟨C, hfin, hF, hop⟩ := ih
    have hm := measurable_chainKernelLimit Kb hKb K
    have hcomp := hF.comp volume volume volume hm (hKb (K + 1)) (hQ (K + 1))
    have hcompn := ENNReal.mul_ne_top hfin (hc (K + 1))
    refine ⟨_, hcompn, hcomp, ?_⟩
    calc
      _ = configurationKernelOperator (measurable_spatialKernelComp volume hm (hKb (K + 1)))
          hcompn hcomp := configurationKernelOperator_eq_of_eq rfl _ _ _ _ _ _
      _ = (configurationKernelOperator hm hfin hF).comp
          (configurationKernelOperator (hKb (K + 1)) (hc (K + 1)) (hQ (K + 1))) :=
        configurationKernelOperator_comp _ _ _ _ _ _
      _ = _ := by rw [hop]; simp only [operatorChain, ContinuousLinearMap.id_comp]

end Critical2DKPZ.SHF.Tsai

end
