/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. Bou-Rabee, Scott Armstrong
Modified for Critical2DKPZ, 2026.
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Rellich.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! Convolution of a locally integrable function with a smooth compactly supported kernel is smooth.

Adapted from A. Bou-Rabee's Lattice-Probability development (Apache-2.0). -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Topology

namespace Critical2DKPZ.Analysis.Sobolev.Rellich


/-- Convolution with a smooth compactly supported kernel is smooth for locally integrable input. -/
theorem contDiff_convReal {d : ℕ} {f ρ : Space d → ℝ} (hf : LocallyIntegrable f volume)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρcs : HasCompactSupport ρ) :
    ContDiff ℝ (⊤ : ℕ∞) (convReal f ρ) := by
  unfold convReal
  exact hρcs.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf hρ

end Critical2DKPZ.Analysis.Sobolev.Rellich

end
