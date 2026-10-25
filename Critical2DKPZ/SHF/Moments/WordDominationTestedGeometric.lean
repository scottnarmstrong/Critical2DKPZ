/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationTestedWordPathBound
public import Critical2DKPZ.SHF.Moments.WordDominationPathGeometric
public import Critical2DKPZ.SHF.Moments.WordDominationBoundaryProfiles
public import Critical2DKPZ.SHF.Moments.WordDominationBoundaryScale
public import Critical2DKPZ.SHF.Moments.WordDominationOperatorContraction
public import Critical2DKPZ.SHF.Moments.WordDominationHorizon
public import Critical2DKPZ.SHF.Moments.WordDominationCoefficientBound
public import Critical2DKPZ.SHF.Moments.WordDominationTwoReplicas
import Mathlib.Tactic

/-! # Uniform geometric domination of tested collision words -/

@[expose] public section

noncomputable section

open Filter
open scoped BigOperators CompactlySupported

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds Critical2DKPZ.Renewal Polymer

/-- The CCR contraction and terminal averaging give uniform geometric
domination for orders three and four. -/
theorem testedBlockWord_geometric_le_of_three_le (ϑ : ℝ) {h : ℕ}
    (hh : h ≤ 4) (hh3 : 3 ≤ h) {τ T : ℝ} (hτ : 0 < τ)
    (φ : Fin h → C_c(Plane × Plane, ℝ)) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ᶠ N : ℕ in atTop, ∀ s t : ℝ, 0 ≤ s → τ ≤ t - s → t ≤ T →
        ∀ m : ℕ, ∑ w : CollisionWord h m,
          |testedBlockWord ϑ N s t φ (List.ofFn w.1)| ≤ C * ρ ^ m := by
  classical
  obtain ⟨M, R, hM, hR, hφ, hφR⟩ := exists_collisionWord_compactTest_bounds φ
  obtain ⟨Cb, hCb, hboundary⟩ := finiteLpNorm_hattedBoundary_indicator_le h (by omega)
  obtain ⟨Cball, hCball, hcard⟩ := card_collisionWordScaledBallSites_le
  obtain ⟨B, hB, htime⟩ := exists_evenClock_horizon_bound (τ := τ) (T := T) hτ
  obtain ⟨cI, cQ, lam, hcI, hcQ, hlam, N₀, hcontract⟩ :=
    eventually_critical_pairOperator_word_contraction_with_bounds h hh3 ϑ B hB
  obtain ⟨B₀, hB₀, hflat⟩ := eventually_sum_abs_testedBlockWord_le_flatMoment ϑ hh φ hτ
  let R' : ℝ := 2 * (R + 2)
  let K : ℝ := 4 * Cb ^ 2 * (8 * M) ^ h * (Cball * (R' + 2) ^ 2) ^ (h + 1)
  have hR' : 0 ≤ R' := by dsimp [R']; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨B₀ + 2 * Real.exp lam * K, (1 / 2 : ℝ), by positivity,
    by norm_num, by norm_num, ?_⟩
  filter_upwards [htime, hflat, eventually_ge_atTop N₀, eventually_ge_atTop 1]
    with N htimeN hflatN hN₀ hN
  intro s t hs hst ht m
  cases m with
  | zero =>
      simpa only [pow_zero, mul_one] using
        (hflatN s t hs hst ht 0).trans (le_add_of_nonneg_right (by positivity))
  | succ n =>
      let L : ℕ := B * N
      let κ : ℝ := lam / (L : ℝ)
      let β : ℝ := criticalBeta ϑ N
      let A : Finset Site := collisionWordScaledBallSites N R'
      let X : Finset (LatticeConfiguration h) := Fintype.piFinset fun _ => A
      let dur : ℕ := evenCeil (N * t) - evenCeil (N * s)
      let d : ℝ := 2 * Cb * (A.card : ℝ) * (Real.sqrt (A.card : ℝ)) ^ (h - 1)
      let D : ℝ := dampedOverlap κ L
      let cU : ℝ := 1 + cI * (sigmaSq β * D / (1 - sigmaSq β * D))
      obtain ⟨hMom, hD, hsmall, hIop, hQop⟩ := hcontract N hN₀
      have hL : 0 < L := by dsimp [L]; exact Nat.mul_pos (by omega) (by omega)
      have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
      have hκ : 0 ≤ κ := by dsimp [κ]; positivity
      have hwindow : dur + N ≤ L := by
        have hw := htimeN s t hs hst ht
        dsimp [dur, L]
        omega
      have hD' : sigmaSq β * D < 1 := hD
      have hD0 : 0 ≤ D := by
        dsimp [D, dampedOverlap]
        apply Finset.sum_nonneg
        intro k hk
        exact mul_nonneg (Real.exp_nonneg _) (srwKernel_nonneg _ _)
      have hcU : 0 ≤ cU := by
        dsimp [cU]
        have hden : 0 < 1 - sigmaSq β * D := sub_pos.mpr hD'
        have hcI0 : 0 ≤ cI := by linarith
        have hσ : 0 ≤ sigmaSq β := sigmaSq_nonneg β
        positivity
      have hd : 0 ≤ d := by dsimp [d]; positivity
      have hQone : 1 ≤ 4 * cQ := by linarith
      have hpath :
          (∑ w : CollisionWord h (n + 1), ∑ x ∈ X, ∑ z ∈ X,
            varianceWeightedHattedPairWordPath L κ β ⊥ (List.ofFn w.1) x z) ≤
            d ^ 2 * (1 / 2 : ℝ) ^ n := by
        apply sum_varianceWeightedHattedPairWordPath_le_half_pow L κ β A cU (4 * cQ) d
          hcU hQone hd
        · intro S I hI
          change finiteLpNorm S 2 (fun x => hattedReplicaBoundaryVector L I A
            (fun y => if y ∈ A then (1 : ℝ) else 0) x) ≤
              2 * Cb * (A.card : ℝ) * (Real.sqrt (A.card : ℝ)) ^ (h - 1)
          exact hboundary L A S I hI
        · intro S I hI f
          exact hIop I hI L κ β hκ hMom hD' S f
        · intro S I J hI hJ hIJ f
          exact hQop L S I J hI hJ hIJ f
        · exact hsmall
      let p : ℝ := (4 * M / N) ^ h * ((2 : ℝ) ^ h / N)
      let e : ℝ := Real.exp (κ * ((dur + N : ℕ) : ℝ))
      have hp : 0 ≤ p := by dsimp [p]; positivity
      have he : 0 ≤ e := Real.exp_nonneg _
      have htest :
          (∑ w : CollisionWord h (n + 1),
            |testedBlockWord ϑ N s t φ (List.ofFn w.1)|) ≤
            p * e * (d ^ 2 * (1 / 2 : ℝ) ^ n) := by
        calc
          _ ≤ ∑ w : CollisionWord h (n + 1), p * e *
                (∑ x ∈ X, ∑ z ∈ X,
                  varianceWeightedHattedPairWordPath L κ β ⊥ (List.ofFn w.1) x z) := by
              apply Finset.sum_le_sum
              intro w hw
              exact testedBlockWord_nonnegative_le_variancePathPairing
                ϑ hN L lam (by linarith) hwindow M R hM hR φ hφ hφR w
          _ = p * e *
                (∑ w : CollisionWord h (n + 1), ∑ x ∈ X, ∑ z ∈ X,
                  varianceWeightedHattedPairWordPath L κ β ⊥ (List.ofFn w.1) x z) :=
              (Finset.mul_sum Finset.univ _ (p * e)).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hpath (mul_nonneg hp he)
      have he_le : e ≤ Real.exp lam := by
        apply Real.exp_le_exp.mpr
        have hw : ((dur + N : ℕ) : ℝ) ≤ L := by exact_mod_cast hwindow
        calc
          κ * ((dur + N : ℕ) : ℝ) ≤ κ * L := mul_le_mul_of_nonneg_left hw hκ
          _ = lam := by dsimp [κ]; field_simp
      have hscale : p * d ^ 2 ≤ K := by
        have hc := hcard hN hR'
        have hb := compactTestBoundaryScale_le (h := h) (by omega) (by omega)
          R' M Cb Cball (A.card : ℝ) 1 hR' hM hCball (Nat.cast_nonneg _) hc (by norm_num)
        simpa [p, d, K] using hb
      have hmain :
          (∑ w : CollisionWord h (n + 1),
            |testedBlockWord ϑ N s t φ (List.ofFn w.1)|) ≤
            Real.exp lam * K * (1 / 2 : ℝ) ^ n := by
        calc
          _ ≤ p * e * (d ^ 2 * (1 / 2 : ℝ) ^ n) := htest
          _ = e * (p * d ^ 2) * (1 / 2 : ℝ) ^ n := by ring
          _ ≤ Real.exp lam * K * (1 / 2 : ℝ) ^ n := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul he_le hscale (mul_nonneg hp (sq_nonneg d))
              (Real.exp_nonneg lam)
      calc
        _ ≤ Real.exp lam * K * (1 / 2 : ℝ) ^ n := hmain
        _ = (2 * Real.exp lam * K) * (1 / 2 : ℝ) ^ (n + 1) := by
          rw [pow_succ]
          ring
        _ ≤ (B₀ + 2 * Real.exp lam * K) * (1 / 2 : ℝ) ^ (n + 1) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB₀) (by positivity)

/-- For the period-two Gaussian polymer through order four, the absolute tested word sums have a uniform geometric majorant on compact positive-time windows, paralleling DHP26 Corollary 3.28. -/
theorem testedBlockWord_geometric_le (ϑ : ℝ) {h : ℕ} (hh : h ≤ 4)
    {τ T : ℝ} (hτ : 0 < τ) (φ : Fin h → C_c(Plane × Plane, ℝ)) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ᶠ N : ℕ in atTop, ∀ s t : ℝ, 0 ≤ s → τ ≤ t - s → t ≤ T →
        ∀ m : ℕ, ∑ w : CollisionWord h m,
          |testedBlockWord ϑ N s t φ (List.ofFn w.1)| ≤ C * ρ ^ m := by
  by_cases hh2 : h ≤ 2
  · exact testedBlockWord_geometric_le_of_h_le_two ϑ hh2 hτ φ
  · exact testedBlockWord_geometric_le_of_three_le ϑ hh (by omega) hτ φ

end Critical2DKPZ.SHF.Moments

end
