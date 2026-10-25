/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.RandomWalk.ReplicaOverlap
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-! The replica overlap satisfies `R_N - π⁻¹ log N → c` for a finite constant `c`, and its logarithmic increments are uniformly accurate at large horizons. -/

@[expose] public noncomputable section

open Filter
open scoped Topology BigOperators

namespace Critical2DKPZ.PolymerCalculus

private theorem sum_Icc_one_eq_shifted_range (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, f n) = ∑ n ∈ Finset.range N, f (n + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), Finset.sum_range_succ, ih]

/-- The local-CLT error along positive even return times is absolutely summable. -/
theorem summable_return_error : Summable (fun n : ℕ =>
    srwKernel (2 * (n + 1)) 0 - (1 / Real.pi) * ((n + 1 : ℕ) : ℝ)⁻¹) := by
  obtain ⟨C, hC, h⟩ := srwKernel_two_mul_zero_localCLT
  have hs : Summable (fun n : ℕ => C / (n : ℝ) ^ 2) := by
    simpa only [div_eq_mul_inv, one_mul] using
      (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).mul_left C
  have ht : Summable (fun n : ℕ => C / ((n + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).mpr hs
  exact ht.of_norm_bounded (fun n => by simpa only [Real.norm_eq_abs] using h (n + 1) (by omega))

/-- For the planar simple-walk return probabilities, `R_N - π⁻¹ log N` converges to a finite constant. -/
theorem exists_tendsto_replicaOverlap_sub_log : ∃ c : ℝ,
    Tendsto (fun N : ℕ => replicaOverlap N - (1 / Real.pi) * Real.log N) atTop (𝓝 c) := by
  let e : ℕ → ℝ := fun n =>
    srwKernel (2 * (n + 1)) 0 - (1 / Real.pi) * ((n + 1 : ℕ) : ℝ)⁻¹
  have he : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, e n) atTop (𝓝 (∑' n, e n)) :=
    summable_return_error.hasSum.tendsto_sum_nat
  have hh := Real.tendsto_harmonic_sub_log.const_mul (1 / Real.pi)
  refine ⟨(∑' n, e n) + (1 / Real.pi) * Real.eulerMascheroniConstant, ?_⟩
  convert he.add hh using 1
  funext N
  have hsum : replicaOverlap N - (1 / Real.pi) * (harmonic N : ℝ) =
      ∑ n ∈ Finset.range N, e n := by
    rw [← sum_Icc_one_eq_shifted_range (fun n => srwKernel (2 * n) 0 -
      (1 / Real.pi) * (n : ℝ)⁻¹)]
    simp only [replicaOverlap, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast, Finset.mul_sum, Finset.sum_sub_distrib]
  rw [← hsum]
  ring

/-- Once both indices are large, the logarithmic overlap increment is uniformly accurate. -/
theorem replicaOverlap_increment_uniform {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ M N : ℕ, K ≤ M → K ≤ N →
      |replicaOverlap M - replicaOverlap N -
        (1 / Real.pi) * (Real.log M - Real.log N)| < ε := by
  obtain ⟨c, hc⟩ := exists_tendsto_replicaOverlap_sub_log
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hc (ε / 2) (by positivity)
  refine ⟨K, fun M N hM hN => ?_⟩
  have hm := hK M hM
  have hn := hK N hN
  rw [Real.dist_eq] at hm hn
  calc
    _ = |(replicaOverlap M - (1 / Real.pi) * Real.log M - c) -
        (replicaOverlap N - (1 / Real.pi) * Real.log N - c)| := by congr 1; ring
    _ ≤ |replicaOverlap M - (1 / Real.pi) * Real.log M - c| +
        |replicaOverlap N - (1 / Real.pi) * Real.log N - c| := abs_sub _ _
    _ < ε := by linarith only [hm, hn]

end Critical2DKPZ.PolymerCalculus
