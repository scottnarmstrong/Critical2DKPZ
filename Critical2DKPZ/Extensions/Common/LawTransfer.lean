/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.Common.Canonical
import Critical2DKPZ.Assembly.RootInputs

/-! # Joint law transfer for arbitrary critical KPZ fields

At a common time horizon, the toy joint convergence theorem identifies every
critical KPZ field with a limit of the same reversed lattice vectors. Uniqueness
of limits in distribution gives equality of laws across probability spaces.
-/

@[expose] public section

open MeasureTheory Filter
open scoped BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.Common

/-- At fixed parameters, any two critical KPZ fields have the same finite tested laws,
including different bounded continuous initial conditions in different coordinates. -/
theorem map_eq_of_isCriticalKPZ (ϑ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane)) (hZ' : IsCriticalSHF ϑ P' Z')
    (H' : ℝ → (Plane →ᵇ ℝ) → Ω' → Distr) (hH' : IsCriticalKPZ P' Z' H')
    (k : ℕ) (t : Fin k → ℝ) (ht : ∀ i, 0 < t i)
    (h₀ : Fin k → (Plane →ᵇ ℝ)) (φ : Fin k → TestFn) :
    P.map (fun ω i => H (t i) (h₀ i) ω (φ i)) =
      P'.map (fun ω i => H' (t i) (h₀ i) ω (φ i)) := by
  let T : ℝ := 1 + ∑ i, |t i|
  have hsum : 0 ≤ ∑ i, |t i| := Finset.sum_nonneg fun i _ => abs_nonneg (t i)
  have hT : 0 < T := by dsimp [T]; linarith
  have htT (i : Fin k) : t i < T := by
    have hi : |t i| ≤ ∑ j, |t j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (t j)) (Finset.mem_univ i)
    have hi' := le_abs_self (t i)
    dsimp [T]
    linarith
  let s : Fin k → ℝ := fun i => T - t i
  have hs : ∀ i, 0 ≤ s i ∧ s i < T := by
    intro i
    dsimp [s]
    constructor <;> linarith [htT i, ht i]
  obtain ⟨X, _, _, _, hdist, hlaw⟩ :=
    Assembly.toyJointAt_of_isCriticalSHF ϑ P Z hZ T hT
  obtain ⟨X', _, _, _, hdist', hlaw'⟩ :=
    Assembly.toyJointAt_of_isCriticalSHF ϑ P' Z' hZ' T hT
  have heq := tendstoInDistribution_unique _ (hdist k s h₀ φ hs) (hdist' k s h₀ φ hs)
  have hleft := hlaw H hH k s h₀ φ hs
  have hright := hlaw' H' hH' k s h₀ φ hs
  have hst (i : Fin k) : T - s i = t i := by dsimp [s]; ring
  simpa only [hst] using hleft.symm.trans (heq.trans hright)

/-- The finite tested random vector has the measurability required for its law. -/
theorem aemeasurable_pairing_family_of_isCriticalKPZ (ϑ : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (k : ℕ) (t : Fin k → ℝ) (ht : ∀ i, 0 < t i)
    (h₀ : Fin k → (Plane →ᵇ ℝ)) (φ : Fin k → TestFn) :
    AEMeasurable (fun ω i => H (t i) (h₀ i) ω (φ i)) P := by
  exact aemeasurable_pi_iff.mpr fun i =>
    aemeasurable_pairing_of_isCriticalKPZ ϑ P Z hZ H hH (t i) (ht i) (h₀ i) (φ i)

end Critical2DKPZ.Extensions.Common
