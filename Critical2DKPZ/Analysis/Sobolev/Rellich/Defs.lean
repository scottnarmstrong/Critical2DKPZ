/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. Bou-Rabee, Scott Armstrong
Modified for Critical2DKPZ, 2026.
-/
module

public import Critical2DKPZ.Analysis.Sobolev.FunctionBound

/-! The Sobolev square is a weighted Fourier energy, and its dual bound is the supremum of a functional over unit-energy tests supported in a bounded open domain.

Adapted from A. Bou-Rabee's Lattice-Probability development (Apache-2.0). -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

namespace Critical2DKPZ.Analysis.Sobolev.Rellich

/-- `ℝ^d` as a Euclidean space. -/
abbrev Space (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- `φ ∈ C_c^∞(D)`. -/
def IsTestFn {d : ℕ} (D : Set (Space d)) (φ : Space d → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ D

/-- `‖φ‖_{H^s}²`, through the Fourier transform. -/
noncomputable def sobolevNormSq (d : ℕ) (s : ℝ) (φ : Space d → ℝ) : ℝ≥0∞ :=
  ∫⁻ ξ : Space d, ENNReal.ofReal
    ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2)


/-- `‖F‖_{H^{-s}(D)}` for a functional `F` on test functions. -/
noncomputable def negSobolevNorm (d : ℕ) (s : ℝ) (D : Set (Space d))
    (F : (Space d → ℝ) → ℝ) : ℝ≥0∞ :=
  sSup {v : ℝ≥0∞ | ∃ φ : Space d → ℝ,
    IsTestFn D φ ∧ sobolevNormSq d s φ ≤ 1 ∧ v = ENNReal.ofReal |F φ|}

/-- A bounded nonempty open subset of Euclidean space. -/
def IsDomain {d : ℕ} (D : Set (Space d)) : Prop :=
  IsOpen D ∧ Bornology.IsBounded D ∧ D.Nonempty

end Critical2DKPZ.Analysis.Sobolev.Rellich

end
