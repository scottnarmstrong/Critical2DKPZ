/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.PositiveFiniteDimensional
import Critical2DKPZ.Extensions.ScaleLimit.ZeroReduction

/-! # Finite-dimensional Brownian limit of the critical KPZ scale process

This is Proposition 5.2 of the note, including finite index sets containing
zero, for every associated KPZ version of the given stochastic heat flow.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The scale process has the standard Brownian finite-dimensional laws in the
limit, at every positive horizon and spatial center and for every nonnegative
unit-mass mollifier. Zero scale time is allowed in the finite index set. -/
theorem kpz_scale_finiteDimensional_tendstoInDistribution
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {t : ℝ} (ht : 0 < t) (x : Plane) (φ : TestFn)
    (hφ : ∀ y, 0 ≤ φ y) (hφ1 : (∫ y, φ y) = 1) (I : Finset ℝ≥0) :
    TendstoInDistribution (fun (L : Set.Ioi (0 : ℝ)) ω (i : I) =>
      scaledPairing (H t 0 ω) φ x L (i.val : ℝ)) atTop id
      (fun _ => P) (BrownianReal.projectiveFamily I) := by
  apply tendstoInDistribution_of_drop_zero P
    (fun L ω s => scaledPairing (H t 0 ω) φ x L (s : ℝ))
    (fun L s => (memLp_scaledPairing_two ϑ P Z hZ H hH ht φ x L s).aemeasurable)
    (tendstoInMeasure_scaledPairing_zero ϑ P Z hZ H hH ht φ x) I
  apply kpz_scale_finiteDimensional_tendstoInDistribution_positive ϑ P Z hZ H hH ht x φ hφ hφ1
  intro i hi
  exact lt_of_le_of_ne (show (0 : ℝ≥0) ≤ i from zero_le) (Finset.mem_erase.mp hi).1.symm

end Critical2DKPZ.Extensions.ScaleLimit
