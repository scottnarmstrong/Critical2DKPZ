/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.StationaryLaw
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # The absolute value field in `L¹`

Taking absolute values is a Lipschitz operation on `L¹`, hence preserves the
continuity in mean obtained from stationary integrable one-point laws.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

/-- The real norm is one-Lipschitz. -/
theorem real_norm_lipschitzWith : LipschitzWith 1 (norm : ℝ → ℝ) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using dist_norm_norm_le x y

/-- The `L¹` class of the absolute value of an integrable stationary field. -/
@[expose] def normL1Field {g : Plane → Ω → ℝ}
    (hstat : ∀ y, IdentDistrib (g y) (g 0) P P) (hint : Integrable (g 0) P)
    (y : Plane) : Lp ℝ 1 P :=
  real_norm_lipschitzWith.compLp (norm_zero : ‖(0 : ℝ)‖ = 0) (stationaryL1 hstat hint y)

/-- The class represents the pointwise absolute value at each fixed point. -/
theorem normL1Field_ae_eq {g : Plane → Ω → ℝ}
    (hstat : ∀ y, IdentDistrib (g y) (g 0) P P) (hint : Integrable (g 0) P)
    (y : Plane) : (normL1Field hstat hint y : Ω → ℝ) =ᵐ[P] fun ω => ‖g y ω‖ := by
  filter_upwards [real_norm_lipschitzWith.coeFn_compLp (norm_zero : ‖(0 : ℝ)‖ = 0)
    (stationaryL1 hstat hint y), stationaryL1_ae_eq hstat hint y] with ω hω hrep
  exact hω.trans (congrArg norm hrep)

/-- Continuity of the absolute value field in `L¹`. -/
theorem continuous_normL1Field [IsProbabilityMeasure P] {g : Plane → Ω → ℝ}
    (hstat : ∀ y, IdentDistrib (g y) (g 0) P P) (hint : Integrable (g 0) P)
    (hcont : ∀ y₀, TendstoInMeasure P g (𝓝 y₀) (g y₀)) :
    Continuous (normL1Field hstat hint) :=
  (real_norm_lipschitzWith.continuous_compLp (norm_zero : ‖(0 : ℝ)‖ = 0)).comp
    (continuous_stationaryL1 hstat hint hcont)


end Critical2DKPZ.Extensions.ScaleLimit

end
