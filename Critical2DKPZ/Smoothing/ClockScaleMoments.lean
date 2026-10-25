/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.SecondMoment
public import Critical2DKPZ.MomentBounds.BlockVarianceReduction
public import Critical2DKPZ.OnePoint.RenewalGap
import Mathlib.Tactic

/-! # Uniform second moments at macroscopic smoothing clocks -/

@[expose] public section

open MeasureTheory Filter

namespace Critical2DKPZ.Smoothing

/-- When the smoothing clock is a fixed positive fraction of the horizon, the flat smoothed mass
has a uniformly bounded second moment. The integral's integrability companion is included. -/
theorem integrable_smoothedP2Plane_sq_and_le_of_scale (A δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ Q : ℝ, 0 < Q ∧ ∀ᶠ M : ℕ in atTop,
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ s : ℕ,
        1 ≤ s → δ * (M : ℝ) / 2 ≤ s → s ≤ M →
        Integrable (fun ω => smoothedP2Plane (criticalBeta ϑ M) s M 0 ω ^ 2)
            disorderLaw ∧
          (∫ ω, smoothedP2Plane (criticalBeta ϑ M) s M 0 ω ^ 2 ∂disorderLaw) ≤ Q := by
  obtain ⟨C₂, hC₂⟩ := OnePoint.smoothedP2Plane_secondMoment_le_uniform A 1
  obtain ⟨Cperiod, hCperiod⟩ :=
    Critical2DKPZ.OnePoint.replicaOverlap_sub_log_bounded
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratio : 1 < 2 / δ := by
    rw [lt_div_iff₀ hδ]
    linarith
  let Q : ℝ := 1 + |C₂| * ((Real.log (2 / δ) + Cperiod) / Real.pi) / Real.log 2
  have hQ : 0 < Q := by
    dsimp [Q]
    have hlogRatio : 0 < Real.log (2 / δ) := Real.log_pos hratio
    have hperiodNonneg : 0 ≤ Cperiod := by
      have h := hCperiod 1 1 (by omega)
      exact le_trans (abs_nonneg _) h
    positivity
  refine ⟨Q, hQ, ?_⟩
  filter_upwards [hC₂, Filter.eventually_ge_atTop (2 : ℕ)] with M hC₂M hM
  intro ϑ hϑ s hs1 hsScale hsM
  have hM1 : 1 ≤ M := by omega
  have hsMcast : (s : ℝ) ≤ (M : ℝ) := by exact_mod_cast hsM
  have hsScale' : δ * (M : ℝ) / 2 ≤ (s : ℝ) := by exact_mod_cast hsScale
  have hspos : 0 < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have hratioBound : (M : ℝ) / (s : ℝ) ≤ 2 / δ := by
    rw [div_le_div_iff₀ hspos hδ]
    nlinarith [hsScale']
  have hratioNat :
      (((max M 1 : ℕ) : ℝ) / ((max s 1 : ℕ) : ℝ)) ≤ 2 / δ := by
    simpa only [max_eq_left hM1, max_eq_left hs1, Nat.cast_one] using hratioBound
  have hgap : Critical2DKPZ.replicaOverlap M - Critical2DKPZ.replicaOverlap s ≤
      (Real.log (2 / δ) + Cperiod) / Real.pi :=
    Critical2DKPZ.MomentBounds.replicaOverlap_sub_le_of_ratio_bound
      Cperiod hCperiod hsM hratioNat
  have hgapNonneg : 0 ≤
      Critical2DKPZ.replicaOverlap M - Critical2DKPZ.replicaOverlap s := by
    rw [OnePoint.replicaOverlap_sub_eq_sum s M hsM]
    exact Finset.sum_nonneg fun r _ =>
      Critical2DKPZ.srwKernel_nonneg (2 * r) 0
  have hcoef : C₂ *
      (Critical2DKPZ.replicaOverlap M - Critical2DKPZ.replicaOverlap s) ≤
      |C₂| * ((Real.log (2 / δ) + Cperiod) / Real.pi) := by
    calc
      _ ≤ |C₂| * (Critical2DKPZ.replicaOverlap M -
          Critical2DKPZ.replicaOverlap s) :=
        mul_le_mul_of_nonneg_right (le_abs_self C₂) hgapNonneg
      _ ≤ _ := mul_le_mul_of_nonneg_left hgap (abs_nonneg C₂)
  have hsecond := hC₂M ϑ hϑ s M hsM (by omega) (by
    nlinarith)
  have hsecondQ :
      (∫ ω, smoothedP2Plane (criticalBeta ϑ M) s M 0 ω ^ 2 ∂disorderLaw) ≤ Q := by
    dsimp [Q]
    have hden : Real.log (1 + (M : ℝ) / M) = Real.log 2 := by
      have hMpos : (M : ℝ) ≠ 0 := by positivity
      rw [div_self hMpos]
      norm_num
    rw [hden] at hsecond
    have hlogNonneg : 0 ≤ Real.log (2 / δ) + Cperiod := by
      have hperiodNonneg : 0 ≤ Cperiod := by
        have h := hCperiod 1 1 (by omega)
        exact le_trans (abs_nonneg _) h
      exact add_nonneg (Real.log_nonneg (le_of_lt hratio)) hperiodNonneg
    have hcoefDiv : C₂ *
        (Critical2DKPZ.replicaOverlap M - Critical2DKPZ.replicaOverlap s) /
          Real.log 2 ≤
        |C₂| * ((Real.log (2 / δ) + Cperiod) / Real.pi) / Real.log 2 := by
      exact (div_le_div_of_nonneg_right hcoef hlog2.le)
    linarith
  exact ⟨OnePoint.integrable_smoothedP2Plane_sq (criticalBeta ϑ M) s M,
    hsecondQ⟩

end Critical2DKPZ.Smoothing

end
