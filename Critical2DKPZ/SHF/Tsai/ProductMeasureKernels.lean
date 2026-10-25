/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.MeasureKernels
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Kernel.Composition.Prod

/-! # Measurable finite products of measure kernels

Finite tuples of samples from a random block are represented by actual
product measures. A product kernel construction supplies their measurability;
pointwise sigma-finiteness identifies each value with Mathlib's product measure.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.SHF.Tsai

/-- Finite products of s-finite kernels with sigma-finite values are measurable kernels. -/
theorem exists_piMeasureKernel {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] (n : ℕ) :
    ∀ (κ : Fin n → Kernel Ω X) (_ : ∀ i, IsSFiniteKernel (κ i))
      (_ : ∀ i ω, SigmaFinite (κ i ω)),
      ∃ η : Kernel Ω (Fin n → X), IsSFiniteKernel η ∧
        ∀ ω, η ω = Measure.pi (fun i => κ i ω) := by
  induction n with
  | zero =>
    intro κ hκ hsf
    let x : Fin 0 → X := Fin.elim0
    refine ⟨Kernel.const Ω (Measure.dirac x), inferInstance, ?_⟩
    intro ω
    exact (Measure.pi_of_empty (fun i => κ i ω) x).symm
  | succ n ih =>
    intro κ hκ hsf
    obtain ⟨η, hη, hηeq⟩ := ih (fun i => κ i.succ) (fun i => hκ i.succ) (fun i => hsf i.succ)
    let : IsSFiniteKernel (κ 0) := hκ 0
    let : IsSFiniteKernel η := hη
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
    refine ⟨((κ 0).prod η).map e.symm, inferInstance, ?_⟩
    intro ω
    let : ∀ i, SigmaFinite (κ i ω) := fun i => hsf i ω
    have he := measurePreserving_piFinSuccAbove (fun i => κ i ω) 0
    rw [Kernel.map_apply _ e.symm.measurable, Kernel.prod_apply, hηeq ω]
    exact (he.symm e).map_eq

/-- The actual finite product of kernel values is a measurable measure-valued map. -/
theorem measurable_piMeasure_of_kernels {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (n : ℕ) (κ : Fin n → Kernel Ω X) (hκ : ∀ i, IsSFiniteKernel (κ i))
    (hsf : ∀ i ω, SigmaFinite (κ i ω)) :
    Measurable (fun ω => Measure.pi (fun i => κ i ω)) := by
  obtain ⟨η, _, hη⟩ := exists_piMeasureKernel n κ hκ hsf
  have heq : (fun ω => Measure.pi (fun i => κ i ω)) = η := funext fun ω => (hη ω).symm
  rw [heq]
  exact η.measurable

/-- Everywhere locally finite measure-valued maps have measurable finite product measures. -/
theorem measurable_piMeasure_of_locallyFinite {Ω X : Type*}
    [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [T2Space X] [SigmaCompactSpace X] (n : ℕ)
    (B : Fin n → Ω → Measure X) (hB : ∀ i, Measurable (B i))
    (hlf : ∀ i ω, IsLocallyFiniteMeasure (B i ω)) :
    Measurable (fun ω => Measure.pi (fun i => B i ω)) := by
  let κ (i : Fin n) : Kernel Ω X := ⟨B i, hB i⟩
  have hκ (i) : IsSFiniteKernel (κ i) := isSFiniteKernel_of_locallyFinite _ (hlf i)
  have hsf (i) (ω) : SigmaFinite (κ i ω) := by
    let : IsLocallyFiniteMeasure (B i ω) := hlf i ω
    change SigmaFinite (B i ω)
    infer_instance
  obtain ⟨η, _, hη⟩ := exists_piMeasureKernel n κ hκ hsf
  have heq : (fun ω => Measure.pi (fun i => B i ω)) = η := by
    funext ω
    exact (hη ω).symm
  rw [heq]
  exact η.measurable

end Critical2DKPZ.SHF.Tsai

end
