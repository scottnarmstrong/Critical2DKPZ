/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationMarkedProfileSmall
public import Critical2DKPZ.SHF.Moments.WordDominationTestedNonpairPathBound
public import Critical2DKPZ.SHF.Moments.WordDominationPairWordProfiles
public import Critical2DKPZ.SHF.Moments.WordDominationHorizon
public import Critical2DKPZ.SHF.Moments.WordDominationLowOrder
import Mathlib.Tactic

/-! # Uniform disappearance of the non-pair tested remainder -/

@[expose] public section

noncomputable section

open scoped BigOperators CompactlySupported

namespace Critical2DKPZ.SHF.Moments

open Filter

/-- Marked partition moments and weighted CCR bounds remove the tested
non-pair remainder at every fixed replica order at least three. -/
theorem testedNonpairRemainder_small_of_three_le (ϑ : ℝ) {h : ℕ} (hh : 3 ≤ h)
    {τ T : ℝ} (hτ : 0 < τ) (φ : Fin h → C_c(Plane × Plane, ℝ)) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ s t : ℝ,
      0 ≤ s → τ ≤ t - s → t ≤ T → |testedNonpairRemainder ϑ N s t φ| ≤ ε := by
  classical
  obtain ⟨M, R, hM, hR, hφ, hφR⟩ := exists_collisionWord_compactTest_bounds φ
  obtain ⟨B, hB, htime⟩ := exists_evenClock_horizon_bound (τ := τ) (T := T) hτ
  obtain ⟨C, hC, hsmall⟩ := eventually_collisionWord_markedProfile_le_small_scale h hh ϑ B hB R hR
  intro ε hε
  let K := (4 * M) ^ h * C
  let δ := ε / (K + 1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδK : δ * K ≤ ε := by
    calc
      _ ≤ δ * (K + 1) := mul_le_mul_of_nonneg_left (by linarith) hδ.le
      _ = ε := by dsimp [δ]; field_simp
  filter_upwards [hsmall δ hδ, htime, eventually_ge_atTop 1] with N hsmall htime hN
  intro s t hs hst ht
  have hL : evenCeil (N * t) - evenCeil (N * s) ≤ B * N := by
    have htime' := htime s t hs hst ht
    omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ (4 * M / N) ^ h *
        ∑ x ∈ Fintype.piFinset (fun _ : Fin h => collisionWordScaledBallSites N R),
          ∑ I ∈ collisionWordMarkedPartitionSequences h (evenCeil (N * t) - evenCeil (N * s)),
            (∏ j : Fin (evenCeil (N * t) - evenCeil (N * s)),
              |Critical2DKPZ.MomentBounds.replicaPartitionDisorderMoment (criticalBeta ϑ N) (I j)|) *
              Critical2DKPZ.MomentBounds.replicaPathWeight (List.ofFn I) x :=
      abs_testedNonpairRemainder_le_markedPartitionSum ϑ (by omega) s t M R hM hR φ hφ hφR
    _ ≤ (4 * M / N) ^ h * (δ * C * (N : ℝ) ^ h) :=
      mul_le_mul_of_nonneg_left (hsmall _ hL) (by positivity)
    _ = δ * K := by
      dsimp [K]
      rw [div_pow]
      field_simp [hNpos.ne']
    _ ≤ ε := hδK

/-- For the period-two Gaussian polymer through order four, tested non-pair remainders vanish uniformly on compact positive-time windows, paralleling DHP26 Corollary 3.29. -/
theorem testedNonpairRemainder_small (ϑ : ℝ) {h : ℕ} (_hh : h ≤ 4)
    {τ T : ℝ} (hτ : 0 < τ) (φ : Fin h → C_c(Plane × Plane, ℝ)) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ s t : ℝ,
      0 ≤ s → τ ≤ t - s → t ≤ T → |testedNonpairRemainder ϑ N s t φ| ≤ ε := by
  by_cases hlow : h ≤ 2
  · exact testedNonpairRemainder_small_of_h_le_two ϑ hlow hτ φ
  · exact testedNonpairRemainder_small_of_three_le ϑ (by omega) hτ φ

end Critical2DKPZ.SHF.Moments

end
