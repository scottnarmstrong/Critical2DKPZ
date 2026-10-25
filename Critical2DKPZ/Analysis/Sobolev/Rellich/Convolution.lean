/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. Bou-Rabee, Scott Armstrong
Modified for Critical2DKPZ, 2026.
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Rellich.Defs
import Mathlib.Analysis.Fourier.Convolution

/-! Convolution of real functions on Euclidean space.

Adapted from A. Bou-Rabee's Lattice-Probability development (Apache-2.0). -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal FourierTransform Topology

namespace Critical2DKPZ.Analysis.Sobolev.Rellich

/-- Convolution of two real functions. -/
noncomputable def convReal {d : ℕ} (f ρ : Space d → ℝ) : Space d → ℝ :=
  convolution f ρ (ContinuousLinearMap.mul ℝ ℝ) volume




end Critical2DKPZ.Analysis.Sobolev.Rellich

end
