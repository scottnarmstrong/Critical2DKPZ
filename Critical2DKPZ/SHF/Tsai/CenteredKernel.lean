/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.DiagramSeries
public import Critical2DKPZ.SHF.DeltaBose.ConfigurationWeight
import Critical2DKPZ.SHF.DeltaBose.Measurability

/-! # Centered moment kernels

The centered moment kernel is the finite signed sum of moment kernels on active
particle subsets multiplied by heat kernels on their complements.
-/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Tsai's sum of absolute coordinate values, using the canonical configuration weight. -/
abbrev configL1Norm {n : ℕ} (x : Configuration n) : ℝ := configurationOneNorm x

/-- Tsai's centered kernel, the finite signed sum over active particle subsets. -/
def centeredMomentKernel (n : ℕ) (θ t : ℝ) (x y : Configuration n) : ℝ :=
  ∑ ω : Finset (Fin n), (-1 : ℝ) ^ (n - ω.card) *
    (momentKernel ω.card θ t (fun i => x (ω.orderEmbOfFin rfl i))
      (fun i => y (ω.orderEmbOfFin rfl i))).toReal *
    ∏ i ∈ ωᶜ, heatKernel t (y i - x i)


end Critical2DKPZ.SHF.Tsai

end
