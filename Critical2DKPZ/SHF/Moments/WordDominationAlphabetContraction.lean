/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationCriticalDampingHorizon
public import Critical2DKPZ.Polymer.Chaos
import Mathlib.Tactic

/-! # Critical contraction for a fixed finite partition alphabet -/

@[expose] public section

namespace Critical2DKPZ.SHF.Moments

open Filter Critical2DKPZ.Renewal Critical2DKPZ.MomentBounds Polymer

/-- For fixed operator constants and finite alphabet size, one damping parameter gives the stated critical contraction at all sufficiently large lattice scales. -/
theorem eventually_critical_alphabet_contraction
    (ϑ : ℝ) (B : ℕ) (hB : 1 ≤ B) (cI cQ P : ℝ)
    (hcI : 1 ≤ cI) (hcQ : 1 ≤ cQ) (hP : 1 ≤ P) :
    ∃ lam : ℝ, 1 ≤ lam ∧ ∀ᶠ N : ℕ in atTop,
      sigmaSq (criticalBeta ϑ N) *
        dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N) < 1 ∧
      (1 + cI * (sigmaSq (criticalBeta ϑ N) *
          dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N) /
        (1 - sigmaSq (criticalBeta ϑ N) *
          dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N)))) *
        sigmaSq (criticalBeta ϑ N) * P * cQ < 1 / 4 := by
  let K : ℝ := P * cQ
  let ε : ℝ := 1 / (8 * cI * K)
  have hK : 0 < K := by dsimp [K]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨lam, hlam, N₀, hres⟩ :=
    eventually_critical_damped_resolvent_small_mul_horizon ϑ ε hε B hB
  have hσsmall := (tendsto_order.mp (tendsto_sigma_zero ϑ)).2
    (1 / (8 * K)) (by positivity)
  refine ⟨lam, hlam, ?_⟩
  filter_upwards [hσsmall, criticalBeta_spec ϑ, eventually_ge_atTop N₀]
    with N hσsmall hβ hN
  let σ : ℝ := sigmaSq (criticalBeta ϑ N)
  let D : ℝ := dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N)
  have hσeq : σ = criticalSigmaSq ϑ N := by simpa [σ, sigmaSq] using hβ
  obtain ⟨_, hD, hratio⟩ := hres N hN
  have hD' : σ * D < 1 := by simpa [D, ← hσeq] using hD
  have hratio' : σ * (σ * D / (1 - σ * D)) ≤ ε := by
    simpa [D, ← hσeq] using hratio
  have hσK : σ * K < 1 / 8 := by
    have hs : σ < 1 / (8 * K) := by simpa [← hσeq] using hσsmall
    calc
      _ < (1 / (8 * K)) * K := mul_lt_mul_of_pos_right hs hK
      _ = 1 / 8 := by field_simp
  have hscaled : cI * (σ * (σ * D / (1 - σ * D))) * K ≤ 1 / 8 := by
    calc
      _ ≤ cI * ε * K := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio' (by linarith)) hK.le
      _ = 1 / 8 := by dsimp [ε]; field_simp
  refine ⟨hD', ?_⟩
  change (1 + cI * (σ * D / (1 - σ * D))) * σ * P * cQ < 1 / 4
  calc
    _ = σ * K + cI * (σ * (σ * D / (1 - σ * D))) * K := by dsimp [K]; ring
    _ < 1 / 8 + 1 / 8 := add_lt_add_of_lt_of_le hσK hscaled
    _ = 1 / 4 := by norm_num

end Critical2DKPZ.SHF.Moments

end
