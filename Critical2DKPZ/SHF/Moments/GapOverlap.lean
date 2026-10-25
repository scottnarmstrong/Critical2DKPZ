/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.ReturnAsymptotics
public import Critical2DKPZ.SHF.Moments.BoundaryConvention
import Critical2DKPZ.Renewal.CriticalWindow
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-! # Logarithmic normalization at accessible gaps

Accessible gaps have the same leading logarithmic overlap constant, and the centered return sum converges. -/

@[expose] public section

noncomputable section

open Filter
open scoped Topology BigOperators

namespace Critical2DKPZ.SHF.Moments

/-- The collision return sum at a fixed displacement, without the zero-time atom. -/
def gapOverlap (z : Site) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, srwKernel (2 * n) z

/-- Summable difference from the reciprocal-time kernel at every accessible gap. -/
theorem summable_gap_return_error (z : Site) (hz : Even (z 0 + z 1)) :
    Summable (fun n : ℕ => srwKernel (2 * n) z - (1 / Real.pi) * (n : ℝ)⁻¹) := by
  obtain ⟨C, _, hC⟩ := srwKernel_even_gap_localCLT z hz
  have hs : Summable (fun n : ℕ => C / (n : ℝ) ^ 2) := by
    simpa only [div_eq_mul_inv, one_mul] using
      (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).mul_left C
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop 1] with n hn
  simpa only [Real.norm_eq_abs] using hC n hn

/-- Convergence of the centered return sum, stronger than bounded logarithmic error. -/
theorem gapOverlap_centered_converges (z : Site) (hz : Even (z 0 + z 1)) :
    ∃ b : ℝ, Tendsto (fun N : ℕ => gapOverlap z N - (1 / Real.pi) * Real.log N)
      atTop (𝓝 b) := by
  let e : ℕ → ℝ := fun n => srwKernel (2 * n) z - (1 / Real.pi) * (n : ℝ)⁻¹
  have he : Summable e := summable_gap_return_error z hz
  have hid (N : ℕ) : gapOverlap z N - (1 / Real.pi) * (harmonic N : ℝ) =
      (∑ n ∈ Finset.range (N + 1), e n) - e 0 := by
    calc
      _ = ∑ n ∈ Finset.Icc 1 N, e n := by
        simp only [gapOverlap, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
          Rat.cast_natCast, Finset.mul_sum, Finset.sum_sub_distrib, e]
      _ = _ := by
        rw [sum_Icc_eq_sum_range_boundary, Finset.sum_range_succ]
  have hpart := (he.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).sub_const (e 0)
  have hlog := Real.tendsto_harmonic_sub_log.const_mul (1 / Real.pi)
  refine ⟨((∑' n, e n) - e 0) + (1 / Real.pi) * Real.eulerMascheroniConstant, ?_⟩
  convert hpart.add hlog using 1
  funext N
  dsimp only [Function.comp_apply]
  rw [← hid N]
  ring



/-- A single logarithmic error constant for each accessible gap, at every cutoff. -/
theorem gapOverlap_log_bound (z : Site) (hz : Even (z 0 + z 1)) :
    ∃ C : ℝ, ∀ N : ℕ, |gapOverlap z N - (1 / Real.pi) * Real.log N| ≤ C := by
  obtain ⟨b, hb⟩ := gapOverlap_centered_converges z hz
  obtain ⟨C, hC⟩ := hb.norm.bddAbove_range
  exact ⟨C, fun N => by simpa only [Real.norm_eq_abs] using hC (Set.mem_range_self N)⟩


end Critical2DKPZ.SHF.Moments
