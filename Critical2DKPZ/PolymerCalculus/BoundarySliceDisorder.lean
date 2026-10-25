/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Probability.Moments.Basic
public import Critical2DKPZ.PolymerCalculus.LogSumExp
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Analysis.Complex.Exponential
public import Critical2DKPZ.Gaussian.DisorderLaws
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-! Every injective finite collection of Gaussian disorder coordinates forms a standard Gaussian vector. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace Critical2DKPZ.PolymerCalculus

variable {ι : Type*} [Fintype ι]

/-- The finite vector of disorder variables on a fixed slice. -/
def disorderSliceCoordinates (e : ι → ℕ × Site) (ω : Disorder) :
    EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => ω (e i))

/-- An injective finite collection of disorder coordinates has the standard Gaussian vector law. -/
theorem hasLaw_disorderSliceCoordinates (e : ι → ℕ × Site)
    (he : Function.Injective e) :
    HasLaw (disorderSliceCoordinates e) (stdGaussian (EuclideanSpace ℝ ι)) disorderLaw := by
  classical
  refine ⟨?_, ?_⟩
  · change AEMeasurable (fun ω : Disorder =>
      WithLp.toLp 2 (fun i => ω (e i))) disorderLaw
    have hraw : Measurable (fun ω : Disorder => fun i => ω (e i)) :=
      measurable_pi_iff.mpr (fun i => Gaussian.measurable_disorder_eval (e i))
    have hto : Measurable (fun x : ι → ℝ => WithLp.toLp 2 x) := by fun_prop
    exact (hto.comp hraw).aemeasurable
  · change disorderLaw.map
        (WithLp.toLp 2 ∘ fun ω : Disorder => fun i => ω (e i)) =
      stdGaussian (EuclideanSpace ℝ ι)
    have hcoord : HasLaw (fun ω : Disorder => fun i => ω (e i))
        (Measure.pi fun _ : ι => gaussianReal 0 1) disorderLaw := by
      refine ⟨(measurable_pi_iff.mpr
        (fun i => Gaussian.measurable_disorder_eval (e i))).aemeasurable, ?_⟩
      rw [(Gaussian.iIndepFun_disorder_eval.precomp he).map_fun_eq_pi_map
        (fun i => (Gaussian.measurable_disorder_eval (e i)).aemeasurable)]
      simp only [(Gaussian.hasLaw_disorder_eval _).map_eq]
    rw [← map_pi_eq_stdGaussian, ← Measure.map_map (by fun_prop) (by fun_prop),
      hcoord.map_eq]










end Critical2DKPZ.PolymerCalculus
