/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Critical2DKPZ.Definitions.HeatKernel
public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.Definitions.Plane
public import Critical2DKPZ.Definitions.ShfPairing
public import Critical2DKPZ.Provider.ShfLogNormality

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise

namespace Critical2DKPZ

/-- **log-normality of small-scale SHF averages** (KPZ Theorem `thm:log-normality`,
§8.1, from GT26 Theorem 1.3): with `F_δ(x) = log 𝒵_{δ,1}(g_δ^{(x)}, 1)` (§3.4),
`(F_{ε²}(x) − E F_{ε²}(x)) / √(log log(1/ε)) ⇒ N(0, 1)` as `ε ↓ 0`.
The index ranges over `ε ∈ (0, 1)`, where every `F_{ε²}(x)` is measurable. -/
theorem shf_logNormality (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (x : Plane) :
    TendstoInDistribution
      (fun (ε : Set.Ioo (0 : ℝ) 1) ω =>
        (Real.log (shfPairing Z ((ε : ℝ) ^ 2) 1 (fun y => heatKernel ((ε : ℝ) ^ 2) (y - x)) (fun _ => 1) ω) -
          ∫ ω', Real.log (shfPairing Z ((ε : ℝ) ^ 2) 1 (fun y => heatKernel ((ε : ℝ) ^ 2) (y - x))
            (fun _ => 1) ω') ∂P) /
        Real.sqrt (Real.log (Real.log (ε : ℝ)⁻¹)))
      (Filter.comap Subtype.val (nhdsWithin 0 (Set.Ioi 0))) id (fun _ => P) (gaussianReal 0 1) :=
  by exact Critical2DKPZ.Provider.shf_logNormality ϑ P Z hZ x
end Critical2DKPZ

end

end
