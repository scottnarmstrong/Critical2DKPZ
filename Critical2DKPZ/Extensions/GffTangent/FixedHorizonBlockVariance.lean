/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonBlockFourth
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonApproximation
import Mathlib.Tactic

/-! # Variance of the actual cell-weighted time-block array -/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- Every fixed partition of the actual polymer array has the same limiting
total variance, equal to the fixed-horizon flow covariance. -/
theorem tendsto_sum_variance_cellBlockFluctuation
    (l β : ℕ → ℝ) (hl : Tendsto l atTop atTop)
    (hratio : Tendsto (fun N => l N / Real.log (N : ℝ)) atTop (𝓝 0))
    (hβ : ∀ᶠ N : ℕ in atTop, 0 < β N)
    (hσ : ∀ᶠ N : ℕ in atTop, Polymer.sigmaSq (β N) = criticalSigmaSq (-l N) N)
    (n : ℕ → ℕ) {T : ℝ} (hT : 0 < T)
    (hn : Tendsto (fun N : ℕ => (n N : ℝ) / N) atTop (𝓝 T))
    {M : ℕ} (hM : 0 < M) (f : TestFn) :
    Tendsto (fun N : ℕ => ∑ i : Fin M,
      ∫ ω, cellBlockFluctuation (β N) (l N) N (n N) M i f ω ^ 2 ∂disorderLaw)
      atTop (𝓝 (4 * Real.pi * ∫ t in Ioo 0 T, ∫ p : Plane × Plane,
        f p.1 * f p.2 * heatKernel (2 * t) (p.2 - p.1) ∂(volume.prod volume))) := by
  let S := fun N => fixedHorizonCellSites N f
  have hS : ∀ N x, f x ≠ 0 → latticePoint N x ∈ S N :=
    fun N x hx => latticePoint_mem_fixedHorizonCellSites N f hx
  let H : ℝ → ℝ := fun t => ∫ p : Plane × Plane,
    f p.1 * f p.2 * heatKernel (2 * t) (p.2 - p.1) ∂(volume.prod volume)
  let W : ℕ → Fin M → Disorder → ℝ := fun N i =>
    latticeWindowFluctuation (β N) (Real.sqrt (l N))
      (quasiCriticalBlockClock (n N) M i)
      (quasiCriticalBlockClock (n N) M ((i : ℕ) + 1)) (S N)
      (fun w => ∫ x in cell N w, f x)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hclock (i : ℕ) : Tendsto
      (fun N : ℕ => (quasiCriticalBlockClock (n N) M i : ℝ) / N) atTop
      (𝓝 (T * (i : ℝ) / M)) := by
    simpa only [mul_div_assoc] using tendsto_quasiCriticalBlockClock_div n hn hM i
  have hinterval (i : Fin M) : T * ((i : ℕ) : ℝ) / M <
      T * (((i : ℕ) : ℝ) + 1) / M := by
    apply (div_lt_div_iff_of_pos_right hMr).mpr
    nlinarith
  have hvar (i : Fin M) : Tendsto (fun N => ∫ ω, W N i ω ^ 2 ∂disorderLaw) atTop
      (𝓝 (4 * Real.pi * ∫ t in Ioo (T * ((i : ℕ) : ℝ) / M)
        (T * (((i : ℕ) : ℝ) + 1) / M), H t)) := by
    apply tendsto_integral_sq_quasiCritical_cell_window l β hl hratio hβ hσ
      (by positivity) (hinterval i) _ _ (hclock i) _ (f : Plane → ℝ)
      f.continuous f.hasCompactSupport S hS
    simpa only [Nat.cast_add, Nat.cast_one] using hclock ((i : ℕ) + 1)
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hvar i)
  rw [← Finset.mul_sum, sum_integral_fixedHorizon_partition hT hM H
    (integrableOn_fixedHorizon_heat_energy f hT)] at hsum
  exact hsum

end Critical2DKPZ.Extensions.GffTangent
