/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. Bou-Rabee, Scott Armstrong
Modified for Critical2DKPZ, 2026.
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Rellich.Convolution
public import Critical2DKPZ.Analysis.Sobolev.Rellich.Additivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Sobolev weights and the weighted Fourier-integral representation of Sobolev energy.

Adapted from work of A. Bou-Rabee, licensed under Apache 2.0. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal FourierTransform Topology

namespace Critical2DKPZ.Analysis.Sobolev.Rellich

/-- The Sobolev weight of exponent `s` at the frequency `ξ`, namely
`(1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s`.  This is the weight used by `sobolevNormSq`. -/
noncomputable def sobolevWeight {d : ℕ} (s : ℝ) (ξ : Space d) : ℝ :=
  (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s

/-- The Sobolev weight is nonnegative. -/
theorem sobolevWeight_nonneg {d : ℕ} (s : ℝ) (ξ : Space d) : 0 ≤ sobolevWeight s ξ := by
  unfold sobolevWeight
  exact Real.rpow_nonneg (by positivity) s

/-- The definition `sobolevNormSq` written through the named weight `sobolevWeight`. -/
theorem sobolevNormSq_eq_lintegral_weight {d : ℕ} (s : ℝ) (φ : Space d → ℝ) :
    sobolevNormSq d s φ
      = ∫⁻ ξ : Space d, ENNReal.ofReal
          (sobolevWeight s ξ * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) := by
  unfold sobolevNormSq sobolevWeight
  rfl



end Critical2DKPZ.Analysis.Sobolev.Rellich

end
