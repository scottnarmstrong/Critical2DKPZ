/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.JointConvergence.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Uniqueness of limits in law

If two families with equal laws converge in measure, their limiting vectors have the same law.
-/

@[expose] public section

open MeasureTheory Filter TopologicalSpace

namespace Critical2DKPZ.JointConvergence

/-- Limits in probability of equal-law families have equal laws. -/
theorem map_eq_of_tendstoInMeasure {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X Y : ℕ → Ω → Fin k → ℝ) (X₀ Y₀ : Ω → Fin k → ℝ)
    (hX : TendstoInMeasure P X atTop X₀) (hY : TendstoInMeasure P Y atTop Y₀)
    (hXm : ∀ n, AEMeasurable (X n) P) (hYm : ∀ n, AEMeasurable (Y n) P)
    (hlaw : ∀ n, P.map (X n) = P.map (Y n)) (hX₀ : AEMeasurable X₀ P) (hY₀ : AEMeasurable Y₀ P) :
    P.map X₀ = P.map Y₀ := by
  have hXd' : TendstoInDistribution X atTop X₀ (fun _ => P) P :=
    hX.tendstoInDistribution hXm
  have hYd' : TendstoInDistribution Y atTop Y₀ (fun _ => P) P :=
    hY.tendstoInDistribution hYm
  have hXd : TendstoInDistribution X atTop X₀ (fun _ => P) P := {
    forall_aemeasurable := hXm
    aemeasurable_limit := hX₀
    tendsto := hXd'.tendsto
  }
  have hYd : TendstoInDistribution Y atTop Y₀ (fun _ => P) P := {
    forall_aemeasurable := hYm
    aemeasurable_limit := hY₀
    tendsto := hYd'.tendsto
  }
  have hseq : (fun n : ℕ => (⟨P.map (X n), inferInstance⟩ : ProbabilityMeasure (Fin k → ℝ))) =
      fun n => ⟨P.map (Y n), inferInstance⟩ := by
    funext n
    exact Subtype.ext (hlaw n)
  have hlimX := hXd.tendsto
  have hlimY := hYd.tendsto
  rw [hseq] at hlimX
  have hlimEq := tendsto_nhds_unique hlimX hlimY
  exact congrArg ProbabilityMeasure.toMeasure hlimEq

end Critical2DKPZ.JointConvergence

end
