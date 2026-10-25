/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordPotentialInduction
public import Critical2DKPZ.SHF.Moments.WordLimitGapPotentialSingle

/-! # Common multi-letter mass induction at three and four replicas -/

@[expose] public noncomputable section

open Filter
open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

/-- For at most four replicas, an inverse-square-root time-envelope bound implies potential domination of every word with distinct consecutive letters. -/
theorem word_mass_domination_of_time_envelope (ϑ : ℝ) {h : ℕ} (hh : h ≤ 4)
    (A : ℝ) (hA : 0 < A)
    (htime : ∀ m : ℕ, wordGapTimeEnvelope m ≤ A / Real.sqrt ((m : ℝ) + 1))
    {T : ℝ} (hT : 0 < T) (α : CollisionPair h) (w : List (CollisionPair h))
    (hchain : (α :: w).IsChain (· ≠ ·)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, (n : ℝ) ≤ T * N →
      ∀ x : Fin h → Site,
      wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) (α :: w) n x (fun _ => 1) ≤
        C * Real.sqrt (N : ℝ) * wordGapPotential n (x α.1.2 - x α.1.1) := by
  obtain ⟨K, hK, hblock⟩ := exists_wordFirstBlock_gapPotential_bound_of_time_envelope A hA htime
  induction w generalizing α with
  | nil =>
      obtain ⟨C, hC, hbound⟩ := eventually_single_mass_le_scaled_gapPotential ϑ T hT
      exact ⟨C, hC, hbound.mono fun N hN n hn x => hN n hn α x⟩
  | cons β w ih =>
      have hparts := List.isChain_cons_cons.mp hchain
      obtain ⟨C, hC, htail⟩ := ih β hparts.2
      obtain ⟨B, hB, hrun⟩ := eventually_critical_run_mass_le ϑ T hT
      refine ⟨C * K * B, mul_pos (mul_pos hC hK) hB, ?_⟩
      filter_upwards [htail, hrun] with N htailN hrunN
      intro n hn x
      apply wordTerminalTest_cons_mass_le_of_potential_step N (criticalBeta ϑ N)
        α β w n x C K B hC.le hK.le
      · intro L hL v
        exact htailN L ((Nat.cast_le.mpr hL).trans hn) v
      · intro s r
        exact hblock hh (criticalBeta ϑ N) α β hparts.1 s r n x
      · intro L hL
        exact hrunN L ((Nat.cast_le.mpr hL).trans hn)

end Critical2DKPZ.SHF.Moments
