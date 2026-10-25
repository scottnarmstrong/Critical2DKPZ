/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Kernel.WithDensity
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-! # S-finite kernels from locally finite measure families

A measurable family of finite measures is s-finite even when its total masses
have no uniform bound: normalize first, then restore the finite density. A
compact exhaustion extends this to locally finite families. This gives the
kernel calculus needed for measurable chains of endpoint products.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Pointwise finite masses suffice for s-finiteness of a measurable measure kernel. -/
theorem isSFiniteKernel_of_isFiniteMeasure {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (κ : Kernel Ω E) (hκ : ∀ ω, IsFiniteMeasure (κ ω)) : IsSFiniteKernel κ := by
  let η : Kernel Ω E := ⟨fun ω => (κ ω Set.univ)⁻¹ • κ ω, by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ((Kernel.measurable_coe κ MeasurableSet.univ).inv).mul (Kernel.measurable_coe κ hs)⟩
  have hη : IsFiniteKernel η := by
    refine ⟨1, by simp, fun ω => ?_⟩
    change (κ ω Set.univ)⁻¹ * κ ω Set.univ ≤ 1
    exact ENNReal.inv_mul_le_one _
  let : IsFiniteKernel η := hη
  have hm : Measurable (fun q : Ω × E => κ q.1 Set.univ) :=
    (Kernel.measurable_coe κ MeasurableSet.univ).comp measurable_fst
  have heq : η.withDensity (fun ω _ => κ ω Set.univ) = κ := by
    ext ω s hs
    rw [Kernel.withDensity_apply' η (f := fun ω (_ : E) => κ ω Set.univ) hm, lintegral_const, Measure.restrict_apply_univ]
    change κ ω Set.univ * ((κ ω Set.univ)⁻¹ * κ ω s) = κ ω s
    by_cases hzero : κ ω Set.univ = 0
    · have hs0 : κ ω s = 0 := measure_mono_null (Set.subset_univ s) hzero
      simp only [hzero, hs0, mul_zero]
    · let : IsFiniteMeasure (κ ω) := hκ ω
      rw [← mul_assoc, ENNReal.mul_inv_cancel hzero (measure_ne_top _ _), one_mul]
  rw [← heq]
  exact Kernel.IsSFiniteKernel.withDensity η (fun ω _ => by
    let : IsFiniteMeasure (κ ω) := hκ ω
    exact measure_ne_top _ _)

/-- A common measurable exhaustion by pointwise finite sets makes a kernel s-finite. -/
theorem isSFiniteKernel_of_finite_exhaustion {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (κ : Kernel Ω E) (s : ℕ → Set E) (hs : ∀ N, MeasurableSet (s N))
    (hcover : ⋃ N, s N = Set.univ) (hfinite : ∀ ω N, κ ω (s N) < ⊤) : IsSFiniteKernel κ := by
  let η (N : ℕ) : Kernel Ω E := κ.restrict (MeasurableSet.disjointed hs N)
  have hη (N : ℕ) : IsSFiniteKernel (η N) := by
    apply isSFiniteKernel_of_isFiniteMeasure
    intro ω
    refine ⟨?_⟩
    rw [show η N ω = (κ ω).restrict (disjointed s N) from Kernel.restrict_apply _ _ _,
      Measure.restrict_apply_univ]
    exact (measure_mono (disjointed_subset s N)).trans_lt (hfinite ω N)
  have heq : Kernel.sum η = κ := by
    ext ω t ht
    rw [Kernel.sum_apply' _ _ ht]
    simp only [η, Kernel.restrict_apply]
    rw [← Measure.restrict_iUnion_apply (disjoint_disjointed s) (MeasurableSet.disjointed hs) ht,
      iUnion_disjointed, hcover, Measure.restrict_univ]
  rw [← heq]
  exact Kernel.isSFiniteKernel_sum (hκs := hη)

/-- A measurable kernel whose values are locally finite on a sigma-compact space is s-finite. -/
theorem isSFiniteKernel_of_locallyFinite {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] [T2Space E] [SigmaCompactSpace E]
    (κ : Kernel Ω E) (hκ : ∀ ω, IsLocallyFiniteMeasure (κ ω)) : IsSFiniteKernel κ := by
  apply isSFiniteKernel_of_finite_exhaustion κ (compactCovering E)
    (fun N => (isCompact_compactCovering E N).isClosed.measurableSet) (iUnion_compactCovering E)
  intro ω N
  let : IsLocallyFiniteMeasure (κ ω) := hκ ω
  exact (isCompact_compactCovering E N).measure_lt_top

end Critical2DKPZ.SHF.Tsai

end
