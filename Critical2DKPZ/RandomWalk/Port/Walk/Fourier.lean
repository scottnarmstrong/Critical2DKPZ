/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module

import Critical2DKPZ.RandomWalk.Port.Walk.Character
public import Critical2DKPZ.RandomWalk.Port.Walk.SRW

/-! # The walk characteristic function and Fourier torus

The characteristic function of one simple random walk step is the average of the
coordinate cosines, and the Fourier torus carries restricted Lebesgue measure. -/

@[expose] public section

noncomputable section

namespace LatticeProb

open MeasureTheory

/-! ### The torus, the character and the Fourier representation -/


/-- The characteristic function `φ(θ) = d^{-1} ∑_j cos θ_j` of one step of the
simple random walk on `ℤ^d`. -/
def charFn (d : ℕ) (θ : Fin d → ℝ) : ℝ := (∑ i, Real.cos (θ i)) / d

/-- Lebesgue measure on the torus `[-π, π]^d`, as a measure on `Fin d → ℝ`. -/
def torusMeasure (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ => volume.restrict (Set.Icc (-Real.pi) Real.pi)




end LatticeProb

end
