/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! # Equality of laws passed through convergence in probability

Two approximation sequences with the same law at every index have the same
limiting law whenever they converge in probability on their respective spaces.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Tsai

/-- Equal finite-vector approximation laws give equal laws of their limits in probability. -/
theorem map_eq_of_tendstoInMeasure_of_map_eq {Ω Ω' ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype ι]
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ℕ → Ω → ι → ℝ) (Y : ℕ → Ω' → ι → ℝ) (F : Ω → ι → ℝ) (G : Ω' → ι → ℝ)
    (hX : ∀ n, AEMeasurable (X n) P) (hY : ∀ n, AEMeasurable (Y n) P')
    (hXF : TendstoInMeasure P X atTop F) (hYG : TendstoInMeasure P' Y atTop G)
    (hEq : ∀ n, P.map (X n) = P'.map (Y n)) : P.map F = P'.map G := by
  have h1 := hXF.tendstoInDistribution hX
  have h2 := hYG.tendstoInDistribution hY
  have hfun : (fun n => (⟨P.map (X n), inferInstance⟩ : ProbabilityMeasure (ι → ℝ))) =
      fun n => (⟨P'.map (Y n), inferInstance⟩ : ProbabilityMeasure (ι → ℝ)) := by
    funext n
    exact Subtype.ext (hEq n)
  have hlim := h1.tendsto
  rw [hfun] at hlim
  have heq : (⟨P.map F, inferInstance⟩ : ProbabilityMeasure (ι → ℝ)) =
      (⟨P'.map G, inferInstance⟩ : ProbabilityMeasure (ι → ℝ)) :=
    tendsto_nhds_unique (X := ProbabilityMeasure (ι → ℝ)) hlim h2.tendsto
  exact congrArg (fun ν : ProbabilityMeasure (ι → ℝ) => (ν : Measure (ι → ℝ))) heq

end Critical2DKPZ.SHF.Tsai

end
