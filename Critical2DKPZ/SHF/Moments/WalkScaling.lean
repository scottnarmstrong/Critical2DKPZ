/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.RandomWalk.Estimates
public import Critical2DKPZ.Analysis.Lattice.Sampling
import Critical2DKPZ.SHF.DeltaBose.BlockTransport
import Mathlib.Tactic

/-! The walk local central limit theorem uses spatial scale √(2/N), cell mass 4/N and spatial parity matching the microscopic time. -/

public section

noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

/-- Exact heat-kernel change of scale, using the lattice representative. -/
theorem heatKernel_latticeRepresentative {N : ℕ} (hN : 0 < N) (n : ℕ) (z : Site) :
    heatKernel ((n : ℝ) / N) (latticeRepresentative N z) =
      (N : ℝ) / 2 * heatKernel ((n : ℝ) / 2) (siteToPlane z) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : 0 < (2 : ℝ) / N := div_pos (by norm_num) hNr
  have hs : (Real.sqrt ((N : ℝ) / 2))⁻¹ = Real.sqrt ((2 : ℝ) / N) := by
    rw [← Real.sqrt_inv, inv_div]
  have ht : (2 / (N : ℝ)) * (n / 2) = (n : ℝ) / N := by ring
  rw [latticeRepresentative, hs, ← ht, DeltaBose.heatKernel_scale ha, inv_div]

/-- A uniform quantitative local CLT after the period-two density normalization. -/
theorem srwKernel_scaled_localCLT :
    ∃ C : ℝ, 0 < C ∧ ∀ N n : ℕ, 0 < N → 1 ≤ n → ∀ z : Site,
      Even (z 0 + z 1 + n) →
      |((N : ℝ) / 4) * srwKernel n z -
        heatKernel ((n : ℝ) / N) (latticeRepresentative N z)| ≤
          C * (N : ℝ) / (n : ℝ) ^ 2 := by
  obtain ⟨C, hC, h⟩ := srwKernel_localCLT
  refine ⟨C / 4, by positivity, fun N n hN hn z hz => ?_⟩
  rw [heatKernel_latticeRepresentative hN]
  have he : (N : ℝ) / 4 * srwKernel n z -
      (N : ℝ) / 2 * heatKernel ((n : ℝ) / 2) (siteToPlane z) =
        (N : ℝ) / 4 * (srwKernel n z -
          2 * heatKernel ((n : ℝ) / 2) (siteToPlane z)) := by ring
  rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (N : ℝ) / 4)]
  calc
    _ ≤ (N : ℝ) / 4 * (C / (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (h n hn z hz) (by positivity)
    _ = _ := by ring

/-- Away from macroscopic time zero, the rescaled walk kernel has a uniform `O(1/N)` local central limit error. -/
theorem srwKernel_scaled_localCLT_away_zero {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N n : ℕ, 0 < N → 1 ≤ n → ε * N ≤ n → ∀ z : Site,
      Even (z 0 + z 1 + n) →
      |((N : ℝ) / 4) * srwKernel n z -
        heatKernel ((n : ℝ) / N) (latticeRepresentative N z)| ≤ C / N := by
  obtain ⟨C, hC, h⟩ := srwKernel_scaled_localCLT
  refine ⟨C / ε ^ 2, by positivity, fun N n hN hn hgap z hz => ?_⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    _ ≤ C * (N : ℝ) / (n : ℝ) ^ 2 := h N n hN hn z hz
    _ ≤ C * (N : ℝ) / (ε * N) ^ 2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact pow_le_pow_left₀ (by positivity) hgap 2
    _ = (C / ε ^ 2) / N := by field_simp

end Critical2DKPZ.SHF.Moments
