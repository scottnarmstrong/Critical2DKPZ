/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.Definitions.IsCriticalKPZ
public import Critical2DKPZ.Definitions.TestFnDilate
public import Mathlib.Probability.Moments.Basic
import Critical2DKPZ.Extensions.Skewness.CubicBound
import Critical2DKPZ.Extensions.Skewness.LawTransfer
import Critical2DKPZ.Provider.CriticalKPZNonGaussian

/-!
# Theorem A: strict skewness

For every nonzero nonnegative test, the flat KPZ pairing has a finite third
absolute moment and a strictly positive third central moment.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BoundedContinuousFunction

universe u

namespace Critical2DKPZ.Extensions.Provider

/-- Strict skewness of the nonzero nonnegative tested flat critical KPZ field. -/
theorem criticalKPZ_centralMoment_three_pos (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x) (hψ0 : ψ ≠ 0) :
    MemLp (fun ω => H t 0 ω ψ) (3 : ℝ≥0∞) P ∧
      0 < centralMoment (fun ω => H t 0 ω ψ) 3 P := by
  have hL3 := Skewness.memLp_three_flat ϑ P Z hZ H hH t ht ψ
  obtain ⟨hX, h, hm, hc, hmap⟩ :=
    Skewness.exists_convex_representative ϑ P Z hZ H hH t ht ψ hψ
  obtain ⟨hLp, hcm⟩ := Skewness.memLp_centralMoment_of_map_eq hX hm hmap 3
  have hna := Skewness.not_affine_of_map_ne_gaussian hmap
    (Critical2DKPZ.Provider.criticalKPZ_nonGaussian ϑ P Z hZ H hH t ht ψ hψ hψ0)
  refine ⟨hL3, ?_⟩
  rw [hcm]
  exact (Skewness.centralMoment_three_pos_iff_not_affine h hm hc (hLp.mp hL3)).mpr hna

end Critical2DKPZ.Extensions.Provider

end
