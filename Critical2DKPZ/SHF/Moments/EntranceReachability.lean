/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WalkScaling
public import Critical2DKPZ.SHF.Moments.TimeRounding
public import Critical2DKPZ.Polymer.Endpoints
public import Critical2DKPZ.Analysis.Heat.Basic
import Mathlib.Tactic

/-! # Reachability on compact diffusive windows

The period-correct local central limit theorem makes every phase-compatible site in a bounded diffusive window reachable at sufficiently large scales, away from macroscopic time zero. -/

public section

noncomputable section

open Filter

namespace Critical2DKPZ.SHF.Moments

/-- A positive heat kernel has a uniform positive lower bound when time stays
in a compact positive interval and space stays in a compact ball. -/
theorem heatKernel_lower_on_compact {ε T R : ℝ} (hε : 0 < ε) (hεT : ε ≤ T)
    {u : ℝ} (hu : ε ≤ u) (huT : u ≤ T)
    {x : Plane} (hx : ‖x‖ ≤ R) :
    (2 * Real.pi * T)⁻¹ * Real.exp (-R ^ 2 / (2 * ε)) ≤ heatKernel u x := by
  have hu0 : 0 < u := lt_of_lt_of_le hε hu
  have hT0 : 0 < T := lt_of_lt_of_le hε hεT
  have hden : 0 < 2 * Real.pi * u := by positivity
  have hdenT : 0 < 2 * Real.pi * T :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) hT0
  have hpref : (2 * Real.pi * T)⁻¹ ≤ (2 * Real.pi * u)⁻¹ := by
    apply (inv_le_inv₀ hdenT hden).2
    exact mul_le_mul_of_nonneg_left huT (by positivity)
  have hinv : (2 * u)⁻¹ ≤ (2 * ε)⁻¹ := by
    apply (inv_le_inv₀ (by positivity : 0 < 2 * u) (by positivity : 0 < 2 * ε)).2
    nlinarith only [hu]
  have hnorm : ‖x‖ ^ 2 ≤ R ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hexpArg : (2 * u)⁻¹ * ‖x‖ ^ 2 ≤ (2 * ε)⁻¹ * R ^ 2 :=
    mul_le_mul hinv hnorm (sq_nonneg ‖x‖) (by positivity)
  have hexp : Real.exp (-R ^ 2 / (2 * ε)) ≤
      Real.exp (-((2 * u)⁻¹ * ‖x‖ ^ 2)) := by
    apply Real.exp_le_exp.mpr
    calc
      -R ^ 2 / (2 * ε) = -((2 * ε)⁻¹ * R ^ 2) := by
        field_simp [ne_of_gt hε]
      _ ≤ -((2 * u)⁻¹ * ‖x‖ ^ 2) := neg_le_neg hexpArg
  calc
    (2 * Real.pi * T)⁻¹ * Real.exp (-R ^ 2 / (2 * ε)) ≤
        (2 * Real.pi * u)⁻¹ * Real.exp (-R ^ 2 / (2 * ε)) :=
      mul_le_mul_of_nonneg_right hpref (Real.exp_nonneg _)
    _ ≤ (2 * Real.pi * u)⁻¹ * Real.exp (-((2 * u)⁻¹ * ‖x‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = heatKernel u x := by
      rw [heatKernel_eq_exp]
      congr 1
      ring_nf

/-- A compact diffusive window contains only reachable sites of the matching
time-space parity once N is large. -/
theorem eventually_srwKernel_pos_on_scaled_compact {ε T R : ℝ}
    (hε : 0 < ε) (hεT : ε ≤ T) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, ε * (N : ℝ) ≤ n →
      (n : ℝ) ≤ T * N → ∀ z : Site,
        Even (z 0 + z 1 + n) → ‖latticeRepresentative N z‖ ≤ R →
        0 < srwKernel n z := by
  obtain ⟨C, hC, hlocal⟩ := srwKernel_scaled_localCLT_away_zero hε
  let c := (2 * Real.pi * T)⁻¹ * Real.exp (-R ^ 2 / (2 * ε))
  have hc : 0 < c := by
    dsimp [c]
    exact mul_pos (inv_pos.mpr
      (mul_pos (mul_pos (by norm_num) Real.pi_pos) (lt_of_lt_of_le hε hεT)))
      (Real.exp_pos _)
  have hsmall : ∀ᶠ N : ℕ in atTop, C / (N : ℝ) < c / 2 :=
    (tendsto_const_div_nat C).eventually (Iio_mem_nhds (by linarith))
  filter_upwards [eventually_gt_atTop 0, hsmall] with N hN hCN
  intro n hlow hhigh z hphase hspace
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hnpos : 0 < (n : ℝ) := by
    exact lt_of_lt_of_le (mul_pos hε hNr) hlow
  have hn : 1 ≤ n := by exact_mod_cast hnpos
  have hu : ε ≤ (n : ℝ) / N := (le_div_iff₀ hNr).2 (by simpa using hlow)
  have huT : (n : ℝ) / N ≤ T := (div_le_iff₀ hNr).2 (by simpa using hhigh)
  have hheat := heatKernel_lower_on_compact hε hεT hu huT hspace
  let A := ((N : ℝ) / 4) * srwKernel n z
  have happrox := hlocal N n hN hn hlow z hphase
  have hA : heatKernel ((n : ℝ) / N) (latticeRepresentative N z) - C / N ≤ A := by
    dsimp [A]
    have hlower := (abs_le.mp happrox).1
    linarith only [hlower]
  have hApos : 0 < A := by
    dsimp [A, c] at *
    linarith only [hA, hheat, hCN, hc]
  have hq : 0 < srwKernel n z := by
    by_contra hnot
    have hqle : srwKernel n z ≤ 0 := le_of_not_gt hnot
    have hAle : A ≤ 0 := by
      dsimp [A]
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hqle
    exact (not_le_of_gt hApos) hAle
  exact hq

/-- Positivity of the walk kernel implies endpoint reachability. -/
theorem mem_endpoints_of_srwKernel_pos (n : ℕ) (a z : Site)
    (hpos : 0 < srwKernel n (z - a)) : z ∈ Polymer.endpoints a n := by
  have hmem : z - a ∈ Polymer.endpoints 0 n := by
    by_contra hnot
    have hzero := Polymer.srwKernel_eq_zero_of_not_mem n 0 (z - a) hnot
    rw [sub_zero] at hzero
    rw [hzero] at hpos
    exact (lt_irrefl 0) hpos
  obtain ⟨s, hs⟩ := (Polymer.mem_endpoints_iff 0 (z - a) n).mp hmem
  apply (Polymer.mem_endpoints_iff a z n).mpr
  refine ⟨s, ?_⟩
  rw [Polymer.walkPosition_eq_start_add a s n, hs]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- Every matching-phase endpoint in a fixed scaled spatial ball is present in
the finite walk endpoint sum, uniformly over all macroscopic time indices. -/
theorem eventually_endpoints_cover_scaled_compact {ε T R : ℝ}
    (hε : 0 < ε) (hεT : ε ≤ T) (aN : ℕ → Site) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, ε * (N : ℝ) ≤ n →
      (n : ℝ) ≤ T * N → ∀ z : Site,
        Even ((z - aN N) 0 + (z - aN N) 1 + n) →
        ‖latticeRepresentative N (z - aN N)‖ ≤ R →
        z ∈ Polymer.endpoints (aN N) n := by
  filter_upwards [eventually_srwKernel_pos_on_scaled_compact hε hεT] with N hN
  intro n hlow hhigh z hphase hspace
  apply mem_endpoints_of_srwKernel_pos n (aN N) z
  exact hN n hlow hhigh (z - aN N) hphase hspace

end Critical2DKPZ.SHF.Moments

end
