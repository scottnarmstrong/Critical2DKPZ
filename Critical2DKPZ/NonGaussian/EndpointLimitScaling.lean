/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.Basic
public import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Tactic

/-! # Scaling compact endpoint tests -/

@[expose] public noncomputable section

open MeasureTheory
open scoped CompactlySupported

namespace Critical2DKPZ.NonGaussian

/-- Endpoint pairings commute with multiplication of a terminal test by a
real constant, including at zero normalizations. -/
theorem endpointPairing_const_mul {Ω : Type*}
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (r t : ℝ) (x : Plane)
    (c : ℝ) (f : Plane → ℝ) (ω : Ω) :
    endpointPairing Z r t x (fun y => c * f y) ω = c * endpointPairing Z r t x f ω := by
  unfold endpointPairing shfPairing
  have heq : (fun p : Plane × Plane => heatKernel r (p.1 - x) * (c * f p.2)) =
      fun p => c * (heatKernel r (p.1 - x) * f p.2) := by funext p; ring
  rw [heq, integral_const_mul]
  ring

/-- The mean absolute centered averaged pairing scales by the absolute value
of the scalar multiplying its compact test. -/
theorem endpointPairing_average_abs_centered_smul {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (r t : ℝ)
    (ψ : Plane → ℝ) (c : ℝ) (φ : C_c(Plane, ℝ)) :
    (∫ ω, |(∫ x, ψ x * endpointPairing Z r t x (c • φ) ω) -
      ∫ ω', (∫ x, ψ x * endpointPairing Z r t x (c • φ) ω') ∂P| ∂P) =
      |c| * ∫ ω, |(∫ x, ψ x * endpointPairing Z r t x φ ω) -
        ∫ ω', (∫ x, ψ x * endpointPairing Z r t x φ ω') ∂P| ∂P := by
  let A (f : Plane → ℝ) (ω : Ω) := ∫ x, ψ x * endpointPairing Z r t x f ω
  have hA (ω : Ω) : A (c • φ) ω = c * A φ ω := by
    calc
      _ = ∫ x, c * (ψ x * endpointPairing Z r t x φ ω) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          change ψ x * endpointPairing Z r t x (fun y => c * φ y) ω = _
          rw [endpointPairing_const_mul]
          ring
      _ = _ := integral_const_mul _ _
  have hmean : (∫ ω, A (c • φ) ω ∂P) = c * ∫ ω, A φ ω ∂P := by
    simp_rw [hA]
    exact integral_const_mul _ _
  change (∫ ω, |A (c • φ) ω - ∫ ω', A (c • φ) ω' ∂P| ∂P) = _
  calc
    _ = ∫ ω, |c * (A φ ω - ∫ ω', A φ ω' ∂P)| ∂P := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        change |A (c • φ) ω - ∫ ω', A (c • φ) ω' ∂P| =
          |c * (A φ ω - ∫ ω', A φ ω' ∂P)|
        rw [hA, hmean]
        congr 1
        ring
    _ = _ := by simp_rw [abs_mul]; exact integral_const_mul _ _

end Critical2DKPZ.NonGaussian
