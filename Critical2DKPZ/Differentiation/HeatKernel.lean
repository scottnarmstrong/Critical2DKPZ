/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Heat.Moments
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Small-time concentration of the planar heat kernel

The Gaussian mass outside every fixed positive-radius ball tends to zero as the heat time
decreases to zero. This is the tail input in approximate-identity arguments for heat smoothing.
-/

@[expose] public section

open MeasureTheory Filter
open Bornology
open scoped Topology ENNReal

namespace Critical2DKPZ.Differentiation

/-- The heat-smoothed density of a positive measure, using the paper's covariance-time kernel. -/
noncomputable def heatSmoothedDensity (μ : Measure Plane) (u : ℝ) (x : Plane) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (heatKernel u (x - y)) ∂μ






end Critical2DKPZ.Differentiation

end
