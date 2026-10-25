/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Independence.Basic

/-! # Pullback of finite independent families

A measure-preserving map preserves the joint law and each marginal law of a
finite measurable family, hence preserves mutual independence.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.SHF.Tsai

/-- Finite measurable independent families remain independent after a measure-preserving pullback. -/
theorem iIndepFun_comp_measurePreserving {Ω Ω' ι X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype ι] [MeasurableSpace X]
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (B : ι → Ω → X) (hB : ∀ i, Measurable (B i)) (hind : iIndepFun B P)
    {φ : Ω' → Ω} (hφ : MeasurePreserving φ Q P) :
    iIndepFun (fun i ω => B i (φ ω)) Q := by
  have hm (f : Ω → ι → X) (hf : Measurable f) :
      Q.map (fun ω => f (φ ω)) = P.map f := by
    rw [← Function.comp_def, ← Measure.map_map hf hφ.measurable, hφ.map_eq]
  have hmarg (i : ι) : Q.map (fun ω => B i (φ ω)) = P.map (B i) := by
    rw [← Function.comp_def, ← Measure.map_map (hB i) hφ.measurable, hφ.map_eq]
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => ((hB i).comp hφ.measurable).aemeasurable)).2
  simp only [Function.comp_def]
  rw [hm _ (Measurable.of_eval hB), hind.map_fun_eq_pi_map (fun i => (hB i).aemeasurable)]
  simp only [hmarg]

end Critical2DKPZ.SHF.Tsai

end
