/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! # Identification of a Cauchy `Lᵖ` limit by convergence in measure

Completeness produces a norm limit. Uniqueness of convergence in measure
identifies its representative with the prescribed probabilistic limit.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Critical2DKPZ.SHF.Tsai

/-- A Cauchy sequence of `Lᵖ` classes converging in measure converges in `Lᵖ` to that limit. -/
theorem tendsto_eLpNorm_sub_of_cauchySeq_of_tendstoInMeasure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : ℕ → Ω → ℝ) (hf : ∀ j, MemLp (f j) p P) (g : Ω → ℝ)
    (hc : CauchySeq (fun j => (hf j).toLp (f j)))
    (hconv : TendstoInMeasure P f atTop g) :
    MemLp g p P ∧ Tendsto (fun j => eLpNorm (f j - g) p P) atTop (𝓝 0) := by
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hc
  have hFm : TendstoInMeasure P f atTop F :=
    (tendstoInMeasure_of_tendsto_Lp hF).congr_left (fun j => (hf j).coeFn_toLp)
  have heq : (F : Ω → ℝ) =ᵐ[P] g := tendstoInMeasure_ae_unique hFm hconv
  refine ⟨(Lp.memLp F).ae_eq heq, ?_⟩
  have hnorm := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ F).1 hF
  apply hnorm.congr
  intro j
  exact eLpNorm_congr_ae ((hf j).coeFn_toLp.sub heq)

end Critical2DKPZ.SHF.Tsai

end
