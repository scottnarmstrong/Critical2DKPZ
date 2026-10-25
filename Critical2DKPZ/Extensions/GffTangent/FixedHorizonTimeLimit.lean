/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonTimeCells
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! # Dominated limits of first-collision time sums -/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- A bounded first-collision sum converges by its cellwise limit, with moving
lower and upper endpoints. The lower macroscopic endpoint may be zero. -/
theorem tendsto_fixedHorizon_time_sum {a b : ℝ} (ha : 0 ≤ a)
    (A B : ℕ → ℕ)
    (hA : Tendsto (fun N : ℕ => (A N : ℝ) / N) atTop (𝓝 a))
    (hB : Tendsto (fun N : ℕ => (B N : ℝ) / N) atTop (𝓝 b))
    (F : ℕ → ℕ → ℝ) (H : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᶠ N : ℕ in atTop, ∀ r ∈ Finset.Icc (A N + 1) (B N), |F N r| ≤ C)
    (hpoint : ∀ t ∈ Ioo a b,
      Tendsto (fun N => F N (fixedHorizonClock N t)) atTop (𝓝 (H t))) :
    Tendsto (fun N : ℕ => (∑ r ∈ Finset.Icc (A N + 1) (B N), F N r) / N)
      atTop (𝓝 (∫ t in Ioo a b, H t)) := by
  let S : ℕ → ℝ → ℝ := fun N t =>
    if 0 ≤ t ∧ A N < fixedHorizonClock N t ∧ fixedHorizonClock N t ≤ B N
    then F N (fixedHorizonClock N t) else 0
  have hSm : ∀ᶠ N : ℕ in atTop, AEStronglyMeasurable (S N) volume := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact (integrable_integral_fixedHorizonTimeStep hN (A N) (B N) (F N)).1.aestronglyMeasurable
  have hdom : ∀ᶠ N : ℕ in atTop, ∀ᵐ t : ℝ,
      ‖S N t‖ ≤ (Icc 0 (b + 1)).indicator (fun _ => C) t := by
    filter_upwards [eventually_gt_atTop 0, hbound,
      hB.eventually (gt_mem_nhds (lt_add_one b))] with N hN hFN hBN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    exact Eventually.of_forall fun t => by
      dsimp only [S]
      split_ifs with ht
      · have hfloor := Nat.lt_floor_add_one ((N : ℝ) * t)
        have hclock : (N : ℝ) * t < (fixedHorizonClock N t : ℝ) := by
          simpa only [fixedHorizonClock, Nat.cast_add, Nat.cast_one] using hfloor
        have hupper : t < b + 1 := by
          have hle : (fixedHorizonClock N t : ℝ) ≤ B N := by exact_mod_cast ht.2.2
          have hquot := (div_lt_iff₀ hNr).mp hBN
          nlinarith
        rw [indicator_of_mem (show t ∈ Icc 0 (b + 1) from ⟨ht.1, hupper.le⟩),
          Real.norm_eq_abs]
        exact hFN _ (Finset.mem_Icc.mpr ⟨by omega, ht.2.2⟩)
      · rw [norm_zero]
        exact indicator_nonneg (fun _ _ => hC) _
  have hp : ∀ᵐ t : ℝ, Tendsto (fun N => S N t) atTop
      (𝓝 ((Ioo a b).indicator H t)) := by
    have hne (x : ℝ) : ∀ᵐ t : ℝ, t ≠ x := by simp [ae_iff]
    filter_upwards [hne 0, hne a, hne b] with t ht0 hta htb
    by_cases ht : t < 0
    · have hs : ∀ N, S N t = 0 := fun N => ite_eq_right (by simp only [not_and]; intro h; linarith)
      simp_rw [hs]
      rw [indicator_of_notMem (show t ∉ Ioo a b by intro h; linarith [h.1])]
      exact tendsto_const_nhds
    have htpos : 0 < t := lt_of_le_of_ne (le_of_not_gt ht) ht0.symm
    have hclock := tendsto_fixedHorizonClock_div htpos
    by_cases hi : t ∈ Ioo a b
    · rw [indicator_of_mem hi]
      apply (hpoint t hi).congr'
      filter_upwards [hA.eventually_lt hclock hi.1, hclock.eventually_lt hB hi.2,
        eventually_gt_atTop 0] with N hlow hupp hN
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      have hlow' : A N < fixedHorizonClock N t := by
        exact_mod_cast (div_lt_div_iff_of_pos_right hNr).mp hlow
      have hupp' : fixedHorizonClock N t < B N := by
        exact_mod_cast (div_lt_div_iff_of_pos_right hNr).mp hupp
      exact (ite_eq_left ⟨htpos.le, hlow', hupp'.le⟩).symm
    · rw [indicator_of_notMem hi]
      apply tendsto_const_nhds.congr'
      have hout : t < a ∨ b < t := by
        simp only [mem_Ioo, not_and_or, not_lt] at hi
        rcases hi with h | h
        · exact Or.inl (lt_of_le_of_ne h hta)
        · exact Or.inr (lt_of_le_of_ne h htb.symm)
      rcases hout with hlow | hupp
      · filter_upwards [hclock.eventually_lt hA hlow, eventually_gt_atTop 0] with N hlt hN
        have hNr : (0 : ℝ) < N := by exact_mod_cast hN
        have hlt' : fixedHorizonClock N t < A N := by
          exact_mod_cast (div_lt_div_iff_of_pos_right hNr).mp hlt
        exact (ite_eq_right (by rintro ⟨_, h, _⟩; omega)).symm
      · filter_upwards [hB.eventually_lt hclock hupp, eventually_gt_atTop 0] with N hlt hN
        have hNr : (0 : ℝ) < N := by exact_mod_cast hN
        have hlt' : B N < fixedHorizonClock N t := by
          exact_mod_cast (div_lt_div_iff_of_pos_right hNr).mp hlt
        exact (ite_eq_right (by rintro ⟨_, _, h⟩; omega)).symm
  have hd : Tendsto (fun N => ∫ t, S N t) atTop
      (𝓝 (∫ t, (Ioo a b).indicator H t)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (bound := (Icc 0 (b + 1)).indicator (fun _ => C)) hSm hdom
    · exact (integrable_indicator_iff measurableSet_Icc).mpr
        (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    · exact hp
  rw [integral_indicator measurableSet_Ioo] at hd
  apply hd.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact (integrable_integral_fixedHorizonTimeStep hN (A N) (B N) (F N)).2

end Critical2DKPZ.Extensions.GffTangent
