/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.PolymerLogMomentBounds
public import Critical2DKPZ.OnePoint.OnePointInverseMomentComparison
import Mathlib.Tactic

/-! # Logarithmic lattice inverse-moment lower bound -/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.NonGaussian

/-- For even smoothing times up to a fixed small macroscopic cutoff, the inverse smoothed mass
has expectation at least `c (1 + log (n / max(s,1)))`, uniformly over the stated time
and critical-parameter windows for sufficiently large lattice scales. -/
theorem exists_lattice_inverse_log_lower_bound_of (hVD : Smoothing.PropVDBound)
    (A T₀ T₁ : ℝ) (hT₀ : 0 < T₀) (hT : T₀ < T₁) :
    ∃ q c : ℝ, 0 < q ∧ q < T₀ ∧ 0 < c ∧
      ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ s n : ℕ,
        Even s → s ≤ evenCeil (q * N) → T₀ * N ≤ n → (n : ℝ) ≤ T₁ * N →
          c * (1 + Real.log ((n : ℝ) / (max s 1 : ℕ))) ≤
            ∫ ω, (smoothedP2Plane (criticalBeta ϑ N) s n 0 ω)⁻¹ ∂disorderLaw := by
  obtain ⟨δ, hδ, hδT, hLow⟩ := OnePoint.smoothedP2Plane_secondMoment_ge_log A T₀ T₁ hT₀ hT
  obtain ⟨c₀, hc₀, hLowδ⟩ := hLow δ hδ le_rfl
  let q : ℝ := Real.sqrt δ
  have hq : 0 < q := Real.sqrt_pos.mpr hδ
  have hqT : q < T₀ := hδT
  obtain ⟨C, hVDq⟩ := (hVD A).1 (q / 2) (q + 1) (by positivity) (by linarith)
  let c : ℝ := c₀ * Real.exp (-C)
  have hc : 0 < c := mul_pos hc₀ (Real.exp_pos _)
  have hRound : ∀ᶠ N : ℕ in atTop, 2 / (T₀ - q) ≤ (N : ℝ) :=
    (tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  refine ⟨q, c, hq, hqT, hc, ?_⟩
  filter_upwards [hLowδ, hVDq, hRound, eventually_ge_atTop 2] with N hLowN hVDN hRoundN hN
  intro ϑ hϑ s n hs hsq hnlo hnhi
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  let n₀ : ℕ := evenCeil (q * N)
  have hqN : 0 ≤ q * N := mul_nonneg hq.le hN0
  have hn₀lo : q / 2 * N ≤ (n₀ : ℝ) := by
    have h := le_evenCeil (q * N)
    change q / 2 * N ≤ (evenCeil (q * N) : ℝ)
    nlinarith only [h, hqN]
  have hn₀hi : (n₀ : ℝ) ≤ (q + 1) * N := by
    have h := (evenCeil_lt_add_two hqN).le
    change (evenCeil (q * N) : ℝ) ≤ (q + 1) * N
    nlinarith only [h, hN2]
  have hn₀n : n₀ ≤ n := by
    have hgap : 2 ≤ (T₀ - q) * N := by
      simpa only [mul_comm] using (div_le_iff₀ (sub_pos.mpr hqT)).mp hRoundN
    have hround := (evenCeil_lt_add_two hqN).le
    have hreal : (n₀ : ℝ) ≤ (n : ℝ) := by
      dsimp [n₀]
      nlinarith only [hgap, hround, hnlo]
    exact_mod_cast hreal
  have hRatio := (hVDN ϑ hϑ 0 s n₀ hs (evenCeil_even _) hsq hn₀lo hn₀hi).2.2
  let S : ℝ := ∫ ω, smoothedP2Plane (criticalBeta ϑ N) s n₀ 0 ω ^ 2 ∂disorderLaw
  let I : ℝ := ∫ ω, (smoothedP2Plane (criticalBeta ϑ N) s n₀ 0 ω)⁻¹ ∂disorderLaw
  have hI : 0 < I := lt_of_lt_of_le zero_lt_one
    (OnePoint.one_le_integral_inv_smoothedP2Plane _ _ _ _)
  have hS : 0 < S := by
    have hMem := Polymer.memLp_smoothedP2Plane (criticalBeta ϑ N) s n₀ 0 2 (by norm_num)
    have hv := ProbabilityTheory.variance_nonneg (smoothedP2Plane (criticalBeta ϑ N) s n₀ 0) disorderLaw
    rw [ProbabilityTheory.variance_eq_sub hMem, Polymer.integral_smoothedP2Plane] at hv
    change 0 < S
    dsimp [S]
    norm_num at hv
    linarith only [hv]
  have hSI : S / I ≤ Real.exp C := (Real.log_le_iff_le_exp (div_pos hS hI)).mp hRatio
  have hInvLower : Real.exp (-C) * S ≤ I := by
    have hmul := (div_le_iff₀ hI).mp hSI
    calc
      Real.exp (-C) * S ≤ Real.exp (-C) * (Real.exp C * I) :=
        mul_le_mul_of_nonneg_left hmul (Real.exp_pos _).le
      _ = I := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have hSecond := hLowN ϑ hϑ s n hsq hnlo hnhi
  calc
    c * (1 + Real.log ((n : ℝ) / (max s 1 : ℕ))) =
        Real.exp (-C) * (c₀ * (1 + Real.log ((n : ℝ) / (max s 1 : ℕ)))) := by dsimp [c]; ring
    _ ≤ Real.exp (-C) * S := mul_le_mul_of_nonneg_left hSecond (Real.exp_pos _).le
    _ ≤ I := hInvLower
    _ ≤ ∫ ω, (smoothedP2Plane (criticalBeta ϑ N) s n 0 ω)⁻¹ ∂disorderLaw :=
      OnePoint.integral_inv_smoothedP2Plane_mono_end _ _ hsq hn₀n

end Critical2DKPZ.NonGaussian

end
