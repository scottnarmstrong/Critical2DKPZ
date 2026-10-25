/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.ReturnSeries
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Euler shift in the damped return normalization

The exact critical coupling uses `R_N`, so the summable local-CLT error cancels from the
difference between the damped return series and `R_N`. The surviving constant is
`-(log a + γ)/π`, with the period-2 normalization fixed throughout.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.Renewal

/-- First-order expansion of exponential damping at the lattice scale. -/
theorem tendsto_scale_one_sub_exp_neg (a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ => ((N : ℝ) + 1) * (1 - Real.exp (-a / (N + 1)))) atTop (nhds a) := by
  have htop : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using!
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp htop
  have hx0 : Tendsto (fun N : ℕ => -a / ((N : ℝ) + 1)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using (tendsto_const_nhds (x := -a)).mul hinv
  have hx : Tendsto (fun N : ℕ => -a / ((N : ℝ) + 1)) atTop (nhdsWithin 0 {0}ᶜ) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hx0, Filter.Eventually.of_forall fun N => ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact div_ne_zero (neg_ne_zero.mpr ha.ne') (by positivity)
  have hs := (Real.hasDerivAt_exp 0).tendsto_slope_zero
  simp only [zero_add, Real.exp_zero, smul_eq_mul] at hs
  have h := (tendsto_const_nhds (x := a)).mul (hs.comp hx)
  rw [mul_one] at h
  apply h.congr
  intro N
  dsimp only [Function.comp_def]
  field_simp
  ring

/-- The damped harmonic series minus the logarithm of the lattice scale converges to the negative logarithm of the damping parameter. -/
theorem tendsto_damped_harmonic_sub_log (a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ => -Real.log (1 - Real.exp (-a / (N + 1))) - Real.log N)
      atTop (nhds (-Real.log a)) := by
  have hscale := tendsto_scale_one_sub_exp_neg a ha
  have hlog := (Real.continuousAt_log ha.ne').tendsto.comp hscale
  have h := hlog.neg.add Real.tendsto_log_nat_add_one_sub_log
  rw [add_zero] at h
  apply h.congr
  intro N
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hq : 0 < 1 - Real.exp (-a / (N + 1)) := sub_pos.mpr
    (Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos ha) hN))
  dsimp only [Function.comp_def]
  rw [Real.log_mul hN.ne' hq.ne']
  ring

/-- The damped return sum differs from the overlap by `-(log a + γ)/π`. -/
theorem tendsto_dampedReturnSum_sub_overlap (a : {a : ℝ // 0 < a}) :
    Tendsto (fun N : ℕ => dampedReturnSum a N - replicaOverlap N) atTop
      (nhds (-(Real.log a + Real.eulerMascheroniConstant) / Real.pi)) := by
  have hpartial : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, returnError n) atTop
      (nhds (∑' n, returnError n)) := summable_returnError.hasSum.tendsto_sum_nat
  have hmain := ((tendsto_damped_harmonic_sub_log a a.2).sub
    Real.tendsto_harmonic_sub_log).const_mul (1 / Real.pi)
  have herr := (tendsto_tsum_damped_returnError a.2.le).sub hpartial
  have h := hmain.add herr
  have heq : (fun N : ℕ => dampedReturnSum a N - replicaOverlap N) = fun N : ℕ =>
      (1 / Real.pi) * ((-Real.log (1 - Real.exp (-a / (N + 1))) - Real.log N) -
        ((harmonic N : ℝ) - Real.log N)) +
      ((∑' n, returnError n * dampingFactor a N n) - ∑ n ∈ Finset.range N, returnError n) := by
    funext N
    rw [dampedReturnSum_eq, replicaOverlap_eq_harmonic_add_error]
    ring
  rw [heq]
  convert h using 1
  ring

end Critical2DKPZ.Renewal

end
