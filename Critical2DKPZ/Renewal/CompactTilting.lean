/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.CompactMoments
public import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Continuous changes of density on compact probability spaces

Exponential tilting by a continuous function preserves weak convergence. This permits
removing the renewal Laplace damping on any fixed finite time horizon.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.Renewal

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

/-- Exponential tilting of a probability measure by a continuous compact-domain function. -/
def compactTilt (μ : ProbabilityMeasure X) (f : C(X, ℝ)) : ProbabilityMeasure X :=
  ⟨(μ : Measure X).tilted f, isProbabilityMeasure_tilted
    (integrable_continuousMap_compact (μ : Measure X) ⟨fun x => Real.exp (f x), by fun_prop⟩)⟩


/-- Integrating against the compact tilted law equals integration against its density. -/
theorem integral_compactTilt (μ : ProbabilityMeasure X) (f : C(X, ℝ)) (g : X → ℝ) :
    (∫ x, g x ∂(compactTilt μ f : Measure X)) =
      (∫ x, Real.exp (f x) * g x ∂(μ : Measure X)) /
        ∫ x, Real.exp (f x) ∂(μ : Measure X) := by
  rw [compactTilt, ProbabilityMeasure.coe_mk, integral_tilted]
  simp only [smul_eq_mul, div_mul_eq_mul_div, integral_div]

/-- Removing the tilt normalization recovers the weighted mass of a measurable set. -/
theorem compactTilt_real_mul_integral (μ : ProbabilityMeasure X) (f : C(X, ℝ))
    {E : Set X} (hE : MeasurableSet E) :
    (compactTilt μ f : Measure X).real E * (∫ x, Real.exp (f x) ∂(μ : Measure X)) =
      ∫ x in E, Real.exp (f x) ∂(μ : Measure X) := by
  have hi := integrable_continuousMap_compact (μ : Measure X)
    (⟨fun x => Real.exp (f x), by fun_prop⟩ : C(X, ℝ))
  have hpos : 0 < ∫ x, Real.exp (f x) ∂(μ : Measure X) := integral_exp_pos hi
  change ((μ : Measure X).tilted f E).toReal * _ = _
  rw [tilted_apply_eq_ofReal_integral' _ hE, integral_div,
    ENNReal.toReal_ofReal (div_nonneg (integral_nonneg (fun _ => (Real.exp_pos _).le)) hpos.le)]
  exact div_mul_cancel₀ _ hpos.ne'

/-- Continuous compact-domain tilting preserves weak convergence. -/
theorem tendsto_compactTilt {μ : ℕ → ProbabilityMeasure X} {ν : ProbabilityMeasure X}
    (hμ : Tendsto μ atTop (nhds ν)) (f : C(X, ℝ)) :
    Tendsto (fun N => compactTilt (μ N) f) atTop (nhds (compactTilt ν f)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro g
  let e : BoundedContinuousFunction X ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun x => Real.exp (f x), by fun_prop⟩
  have hnum := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ (e * g)
  have hden := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ e
  have hpos : 0 < ∫ x, Real.exp (f x) ∂(ν : Measure X) :=
    integral_exp_pos (integrable_continuousMap_compact (ν : Measure X)
      ⟨fun x => Real.exp (f x), by fun_prop⟩)
  simpa only [integral_compactTilt, BoundedContinuousFunction.mul_apply,
    BoundedContinuousFunction.mkOfCompact_apply, e] using! hnum.div hden hpos.ne'


end Critical2DKPZ.Renewal

end
