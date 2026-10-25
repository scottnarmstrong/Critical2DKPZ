/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ProductMeasureKernels
public import Mathlib.Probability.Independence.Integration

/-! # Expected products of independent random measure kernels

Independence factors rectangle masses. Sigma-finiteness of the expected
marginals makes rectangle uniqueness applicable, and gives the full joint
measure identity rather than only a formula for separate tensor tests.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace Critical2DKPZ.SHF.Tsai

/-- Expectation commutes with a finite product of independent kernels with sigma-finite means. -/
theorem bind_piMeasure_eq_pi_bind_of_iIndepFun {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (κ : Fin n → Kernel Ω X) (hκ : ∀ i, IsSFiniteKernel (κ i))
    (hsf : ∀ i ω, SigmaFinite (κ i ω))
    (hind : iIndepFun (fun i ω => κ i ω) P)
    (hmean : ∀ i, SigmaFinite (P.bind (fun ω => κ i ω))) :
    P.bind (fun ω => Measure.pi (fun i => κ i ω)) =
      Measure.pi (fun i => P.bind (fun ω => κ i ω)) := by
  let : ∀ i, SigmaFinite (P.bind (fun ω => κ i ω)) := hmean
  obtain ⟨η, _, hη⟩ := exists_piMeasureKernel n κ hκ hsf
  have hPm : Measurable (fun ω => Measure.pi (fun i => κ i ω)) := by
    have heq : (fun ω => Measure.pi (fun i => κ i ω)) = η := funext fun ω => (hη ω).symm
    rw [heq]
    exact η.measurable
  apply (Measure.pi_eq ?_).symm
  intro A hA
  rw [Measure.bind_apply (MeasurableSet.pi (Set.to_countable univ) (fun i _ => hA i)) hPm.aemeasurable]
  have hrect (ω) : Measure.pi (fun i => κ i ω) (univ.pi A) = ∏ i, κ i ω (A i) := by
    let : ∀ i, SigmaFinite (κ i ω) := fun i => hsf i ω
    exact Measure.pi_pi _ _
  simp_rw [hrect]
  have hind' := hind.comp (fun i μ => μ (A i)) (fun i => Measure.measurable_coe (hA i))
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun i ω => κ i ω (A i)) hind' (fun i => (Measure.measurable_coe (hA i)).comp (κ i).measurable)]
  apply Finset.prod_congr rfl
  intro i _
  exact (Measure.bind_apply (hA i) (κ i).measurable.aemeasurable).symm

end Critical2DKPZ.SHF.Tsai

end
