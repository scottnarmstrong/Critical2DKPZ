/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SchwartzSpectralLp
import Critical2DKPZ.Extensions.ScaleLimit.SchwartzLpLimit

/-! # L² convergence of Fourier cutoffs -/

public section

noncomputable section

open MeasureTheory Filter Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Compact spatial cutoffs approximate every Schwartz test in spectral L². -/
theorem schwartzFourier_cutoff_toLp_tendsto (ν : Measure Plane) [ν.HasTemperateGrowth]
    (f : SchwartzMap Plane ℝ) :
    Tendsto (fun n => (schwartzFourier (Spectral.scaledCutoffSchwartz n f)).toLp 2 ν)
      atTop (𝓝 ((schwartzFourier f).toLp 2 ν)) :=
  tendsto_schwartz_toLp_of_bounded_pointwise ν _ _ (schwartzFourier_cutoff_bounded f)
    (schwartzFourier_cutoff_tendsto f)

end Critical2DKPZ.Extensions.ScaleLimit
