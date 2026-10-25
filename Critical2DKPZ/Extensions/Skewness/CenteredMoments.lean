/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Basic
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Matched Gaussian moments and the residual's two cancellations -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Critical2DKPZ.Extensions.Skewness

/-- Mean under the standard Gaussian law. -/
noncomputable def mean (h : ℝ → ℝ) : ℝ := ∫ x, h x ∂gaussianReal 0 1

/-- Standard deviation under the standard Gaussian law. -/
noncomputable def stddev (h : ℝ → ℝ) : ℝ := Real.sqrt (variance h (gaussianReal 0 1))

/-- Difference from the affine function with matching first two moments. -/
noncomputable def residual (h : ℝ → ℝ) (x : ℝ) : ℝ := h x - mean h - stddev h * x

/-- The standard deviation is nonnegative, including the degenerate case. -/
theorem stddev_nonneg (h : ℝ → ℝ) : 0 ≤ stddev h := Real.sqrt_nonneg _

/-- Its square is the actual variance. Moment finiteness is supplied by consumers. -/
theorem stddev_sq (h : ℝ → ℝ) : stddev h ^ 2 = variance h (gaussianReal 0 1) :=
  Real.sq_sqrt (variance_nonneg h _)

/-- Powers of degree at most three are integrable for an L³ function. -/
theorem integrable_pow_of_memLp_three {h : ℝ → ℝ}
    (hL3 : MemLp h 3 (gaussianReal 0 1)) {n : ℕ} (hn : n ≤ 3) :
    Integrable (fun x => h x ^ n) (gaussianReal 0 1) := by
  have hLn : MemLp h (n : ℝ≥0∞) (gaussianReal 0 1) :=
    hL3.mono_exponent (by exact_mod_cast hn)
  apply hLn.integrable_norm_pow'.mono' (hL3.aestronglyMeasurable.pow n)
  exact Filter.Eventually.of_forall fun x => le_of_eq (norm_pow (h x) n)


/-- The first and third standard Gaussian moments vanish; the second is one. -/
theorem integral_gaussian_odd :
    (∫ x : ℝ, x ∂gaussianReal 0 1) = 0 ∧
    (∫ x : ℝ, x ^ 3 ∂gaussianReal 0 1) = 0 ∧
    (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
  refine ⟨integral_id_gaussianReal, ?_, ?_⟩
  · have hsym : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
      simpa only [neg_zero] using (gaussianReal_map_neg (μ := 0) (v := 1))
    have heq : (∫ x : ℝ, x ^ 3 ∂gaussianReal 0 1) =
        -(∫ x : ℝ, x ^ 3 ∂gaussianReal 0 1) := by
      calc
        (∫ x : ℝ, x ^ 3 ∂gaussianReal 0 1) =
            ∫ x : ℝ, x ^ 3 ∂(gaussianReal 0 1).map (fun x : ℝ => -x) := by rw [hsym]
        _ = ∫ x : ℝ, (-x) ^ 3 ∂gaussianReal 0 1 :=
          integral_map (by fun_prop) (by fun_prop)
        _ = -(∫ x : ℝ, x ^ 3 ∂gaussianReal 0 1) := by
          simp only [neg_pow, Odd.neg_one_pow (by decide : Odd 3), neg_one_mul, integral_neg]
    linarith only [heq]
  · have hv := variance_fun_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_eq_integral (X := fun x : ℝ => x) measurable_id.aemeasurable] at hv
    simpa only [integral_id_gaussianReal, sub_zero, NNReal.coe_one] using hv

/-- The centered function remains in L³. -/
theorem memLp_centered {h : ℝ → ℝ} (hL3 : MemLp h 3 (gaussianReal 0 1)) :
    MemLp (fun x => h x - mean h) 3 (gaussianReal 0 1) :=
  hL3.sub (memLp_const _)

/-- The residual remains in L³. -/
theorem memLp_residual {h : ℝ → ℝ} (hL3 : MemLp h 3 (gaussianReal 0 1)) :
    MemLp (residual h) 3 (gaussianReal 0 1) :=
  (memLp_centered hL3).sub ((memLp_id_gaussianReal' 3 (by norm_num)).const_mul _)

/-- The residual and its product with the increasing companion have mean zero. -/
theorem orthogonality (h : ℝ → ℝ) (hL3 : MemLp h 3 (gaussianReal 0 1)) :
    Integrable (residual h) (gaussianReal 0 1) ∧
    Integrable (fun x => residual h x * (h x - mean h + stddev h * x))
      (gaussianReal 0 1) ∧
    (∫ x, residual h x ∂gaussianReal 0 1) = 0 ∧
    (∫ x, residual h x * (h x - mean h + stddev h * x) ∂gaussianReal 0 1) = 0 := by
  have hId : Integrable (fun x : ℝ => x) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' 3 (by norm_num)).integrable (by norm_num)
  have hc := memLp_centered hL3
  have hi := hc.integrable (by norm_num)
  have hs := (hId.const_mul (stddev h))
  have hsq := integrable_pow_of_memLp_three hc (n := 2) (by norm_num)
  have hxsq : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
    integrable_pow_of_memLp_three (memLp_id_gaussianReal' 3 (by norm_num)) (by norm_num)
  have hfun : (fun x => residual h x * (h x - mean h + stddev h * x)) =
      (fun x => (h x - mean h) ^ 2 - stddev h ^ 2 * x ^ 2) := by
    funext x
    dsimp [residual]
    ring
  have hp : Integrable (fun x => residual h x * (h x - mean h + stddev h * x))
      (gaussianReal 0 1) := by
    rw [hfun]
    exact hsq.sub (hxsq.const_mul _)
  refine ⟨hi.sub hs, hp, ?_, ?_⟩
  · change (∫ x, (h x - mean h) - stddev h * x ∂gaussianReal 0 1) = 0
    rw [integral_sub hi hs, integral_sub (hL3.integrable (by norm_num)) (integrable_const _),
      integral_const_mul, integral_id_gaussianReal]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_zero, mean, sub_self]
  · rw [hfun, integral_sub hsq (hxsq.const_mul _), integral_const_mul,
      integral_gaussian_odd.2.2, mul_one, stddev_sq,
      variance_eq_integral hL3.aestronglyMeasurable.aemeasurable]
    exact sub_self _

end Critical2DKPZ.Extensions.Skewness
