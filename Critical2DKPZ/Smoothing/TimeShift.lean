/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.TimeShiftEnvironment
public import Critical2DKPZ.Smoothing.Measurability
public import Critical2DKPZ.PolymerCalculus.Clocks
public import Critical2DKPZ.Definitions.TestFn
import Mathlib.Tactic.Linarith

/-! # Exact time-shift law for the tested lattice difference -/

@[expose] public noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

namespace Critical2DKPZ.Smoothing

/-- The centered profile logarithm is invariant under subtracting its initial clock. -/
theorem centered_profile_timeShift_sub (β : ℝ) {d a b : ℕ} (hda : d ≤ a) (hdb : d ≤ b)
    (ν f : Site → ℝ) (ω : Disorder) :
    (Real.log (profileP2Fun β a b ν f ω) -
      ∫ ω', Real.log (profileP2Fun β a b ν (fun _ => 1) ω') ∂disorderLaw) =
    (Real.log (profileP2Fun β (a - d) (b - d) ν f (shiftEnvironment d ω)) -
      ∫ ω', Real.log (profileP2Fun β (a - d) (b - d) ν (fun _ => 1) ω') ∂disorderLaw) := by
  simp_rw [profileP2Fun_timeShift_sub β hda hdb]
  rw [integral_shiftEnvironment d (Polymer.measurable_profileP2Fun β (a - d) (b - d) ν (fun _ => 1)).log]

/-- The two fields use the same shifted environment, including their deterministic centerings. -/
theorem kpzLattice_difference_timeShift (ϑ : ℝ) (N : ℕ) {t T δ : ℝ} (_ht : 0 ≤ t) (hδ : 0 < δ)
    (htT : t + δ < T) (h₀ : Plane →ᵇ ℝ) (φ : Plane → ℝ) (ω : Disorder) :
    (∫ x, φ x * (kpzLatticeReversed ϑ N t T h₀ x ω -
      kpzLatticeReversedReg ϑ N t T δ h₀ x ω)) =
      latticeSmoothingError (criticalBeta ϑ N) N (evenCeil (N * T) - evenCeil (N * t))
        (evenCeil (N * (t + δ)) - evenCeil (N * t)) (evenCeil (δ * N)) h₀ φ
        (shiftEnvironment (evenCeil (N * t)) ω) := by
  have hab : evenCeil (N * t) ≤ evenCeil (N * T) := evenCeil_mono
    (mul_le_mul_of_nonneg_left (by linarith only [hδ, htT]) (Nat.cast_nonneg N))
  have hac : evenCeil (N * t) ≤ evenCeil (N * (t + δ)) := evenCeil_mono
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hδ.le) (Nat.cast_nonneg N))
  unfold kpzLatticeReversed kpzLatticeReversedReg latticeSmoothingError
  apply integral_congr_ae
  filter_upwards [] with x
  rw [centered_profile_timeShift_sub (criticalBeta ϑ N) le_rfl hab,
    centered_profile_timeShift_sub (criticalBeta ϑ N) hac hab, Nat.sub_self]

/-- The tested lattice difference has the unit-start smoothing-error law. -/
theorem kpzLattice_difference_timeShift_law (ϑ : ℝ) (N : ℕ) {t T δ : ℝ} (ht : 0 ≤ t) (hδ : 0 < δ)
    (htT : t + δ < T) (h₀ : Plane →ᵇ ℝ) (φ : TestFn) :
    disorderLaw.map (fun ω => ∫ x, φ x * (kpzLatticeReversed ϑ N t T h₀ x ω -
        kpzLatticeReversedReg ϑ N t T δ h₀ x ω)) =
      disorderLaw.map (latticeSmoothingError (criticalBeta ϑ N) N (evenCeil (N * T) - evenCeil (N * t))
        (evenCeil (N * (t + δ)) - evenCeil (N * t)) (evenCeil (δ * N)) h₀ φ) := by
  have he : (fun ω => ∫ x, φ x * (kpzLatticeReversed ϑ N t T h₀ x ω -
      kpzLatticeReversedReg ϑ N t T δ h₀ x ω)) =
      latticeSmoothingError (criticalBeta ϑ N) N (evenCeil (N * T) - evenCeil (N * t))
        (evenCeil (N * (t + δ)) - evenCeil (N * t)) (evenCeil (δ * N)) h₀ φ ∘
          shiftEnvironment (evenCeil (N * t)) :=
    funext fun ω => kpzLattice_difference_timeShift ϑ N ht hδ htT h₀ φ ω
  rw [he, ← Measure.map_map
    (measurable_latticeSmoothingError _ _ _ _ _ _ φ.continuous.measurable)
    (measurable_shiftEnvironment _), (measurePreserving_shiftEnvironment _).map_eq]

end Critical2DKPZ.Smoothing

end
