/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.RadialIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-! # Integral comparison for the weighted scalar shell series -/

public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

/-- One unit interval controls its left-endpoint radial summand uniformly in the exponent. -/
theorem radialIntegrand_le_unit_integral {L γ k : ℝ} (hL : 0 < L) (hγlo : -1 < γ)
    (hγhi : γ < 1) (hk : 1 ≤ k) :
    radialIntegrand L γ k ≤ 8 * ∫ x in k..k + 1, radialIntegrand L γ x := by
  have hint := integrableOn_radialIntegrand hL hγlo hγhi
  have hle : k ≤ k + 1 := le_add_of_nonneg_right zero_le_one
  have hi : IntervalIntegrable (radialIntegrand L γ) volume k (k + 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mpr
      (hint.mono_set fun x hx => (zero_lt_one.trans_le hk).trans hx.1)
  calc
    _ = ∫ _x in k..k + 1, radialIntegrand L γ k := by
      rw [intervalIntegral.integral_const, add_sub_cancel_left, one_smul]
    _ ≤ ∫ x in k..k + 1, 8 * radialIntegrand L γ x :=
      intervalIntegral.integral_mono_on hle intervalIntegrable_const (hi.const_mul 8)
        (fun x hx => radial_summand_le_eight hL hk hx.1 hx.2 hγlo.le)
    _ = _ := intervalIntegral.integral_const_mul _ _

/-- The radial sum is bounded by eight times the corresponding integral. -/
theorem sum_radialIntegrand_le_integral {L γ : ℝ} (hL : 0 < L) (hγlo : -1 < γ)
    (hγhi : γ < 1) (K : ℕ) :
    (∑ j ∈ Finset.range K, radialIntegrand L γ ((j : ℝ) + 1)) ≤
      8 * ∫ x in Ioi 0, radialIntegrand L γ x := by
  have hint := integrableOn_radialIntegrand hL hγlo hγhi
  have hi (j : ℕ) : IntervalIntegrable (radialIntegrand L γ) volume
      ((j : ℝ) + 1) (((j + 1 : ℕ) : ℝ) + 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by push_cast; linarith)).mpr
      (hint.mono_set fun x hx => (by positivity : (0 : ℝ) < (j : ℝ) + 1).trans hx.1)
  calc
    _ ≤ ∑ j ∈ Finset.range K, 8 *
        ∫ x in ((j : ℝ) + 1)..(((j + 1 : ℕ) : ℝ) + 1), radialIntegrand L γ x := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [Nat.cast_add_one, add_assoc] using
        radialIntegrand_le_unit_integral hL hγlo hγhi (by linarith only [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)] : 1 ≤ (j : ℝ) + 1)
    _ = 8 * ∫ x in (1 : ℝ)..((K : ℝ) + 1), radialIntegrand L γ x := by
      rw [← Finset.mul_sum, intervalIntegral.sum_integral_adjacent_intervals
        (a := fun j : ℕ => (j : ℝ) + 1) (fun j _ => hi j)]
      simp only [Nat.cast_zero, zero_add]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [intervalIntegral.integral_of_le (by linarith only [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)] : (1 : ℝ) ≤ (K : ℝ) + 1)]
      apply setIntegral_mono_set hint _ (Filter.Eventually.of_forall ?_)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact radialIntegrand_nonneg hL.le hx.le γ
      · intro x hx
        exact zero_lt_one.trans hx.1


end Critical2DKPZ.MomentBounds
