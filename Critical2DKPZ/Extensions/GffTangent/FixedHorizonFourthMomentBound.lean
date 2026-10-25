/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonFourthTwoRuns
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonWindowFourth
import Critical2DKPZ.MomentBounds.CCR25PartitionSumWordRuns
import Critical2DKPZ.Polymer.ProfileCovariance
import Mathlib.Tactic

/-! # A complete finite-volume fourth-moment bound with the sharp leading term -/

@[expose] public noncomputable section

open MeasureTheory Critical2DKPZ.MomentBounds
open scoped BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- Centering the profile partition function is exactly the finite entrance
fluctuation, including signed coefficients. -/
theorem finiteEntranceFluctuation_eq_centered_profile (β c : ℝ) (L : ℕ)
    (S : Finset Site) (φ : Site → ℝ) (hS : ∀ w ∉ S, φ w = 0) (ω : Disorder) :
    finiteEntranceFluctuation β c 0 L S φ ω =
      c * (profileP2Fun β 0 L φ (fun _ => 1) ω -
        ∫ η, profileP2Fun β 0 L φ (fun _ => 1) η ∂disorderLaw) := by
  have hmean : (∫ η, profileP2Fun β 0 L φ (fun _ => 1) η ∂disorderLaw) = ∑ w ∈ S, φ w := by
    simpa only [mul_one, Nat.sub_zero, Polymer.tsum_srwKernel] using
      Polymer.integral_profileP2Fun_finset β 0 L φ (fun _ => 1) S hS
  have hpoint := Polymer.profileP2Fun_flat_eq_sum β 0 L φ S hS ω
  simp only [Nat.zero_add] at hpoint
  rw [hpoint, hmean]
  unfold finiteEntranceFluctuation
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib]
  ring

private theorem finite_run_sum_le_first_two_tail (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n)
    (hs : Summable (fun n => F (n + 2))) (L : ℕ) :
    (∑ n ∈ Finset.range L, F n) ≤ F 0 + F 1 + ∑' n, F (n + 2) := by
  rcases L with _ | _ | L
  · simp only [Finset.range_zero, Finset.sum_empty]
    exact add_nonneg (add_nonneg (hF 0) (hF 1)) (tsum_nonneg (fun n => hF (n + 2)))
  · have h1 : F 0 ≤ F 0 + F 1 + ∑' n, F (n + 2) :=
      (le_add_of_nonneg_right (hF 1)).trans
        (le_add_of_nonneg_right (tsum_nonneg (fun n => hF (n + 2))))
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] using h1
  · have he : (∑ n ∈ Finset.range (L + 2), F n) =
        F 0 + F 1 + ∑ n ∈ Finset.range L, F (n + 2) := by
      rw [show L + 2 = 2 + L by omega, Finset.sum_range_add]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.add_comm 2]
    rw [he]
    exact add_le_add (le_refl (F 0 + F 1))
      (hs.sum_le_tsum (Finset.range L) (fun n _ => hF (n + 2)))

/-- The actual positive-profile fourth moment is controlled by a sharp
quadratic-width leading term and three explicitly small operator remainders.
No fourth-moment or limit assertion is assumed. -/
theorem integral_fourth_finiteEntranceFluctuation_le
    (β : ℝ) (L : ℕ) (S : Finset Site) (φ : Site → ℝ)
    (hφ : ∀ y, 0 ≤ φ y) (hS : ∀ w ∉ S, φ w = 0)
    {B : ℝ} (hB : 0 ≤ B) (hφB : ∀ y ∈ S, φ y ≤ B)
    (b : FourthWordOperatorBounds (configBox 4 S L) L β
      (fun I => hattedReplicaBoundaryVector L I S φ) collisionIndicator)
    (hσ : Polymer.sigmaSq β ≤ 1)
    (hsmall : (ccr25GaussianFiniteWordOperatorScale 4 b.interactionCost * Polymer.sigmaSq β) * b.freeCost < 1) :
    (∫ ω, finiteEntranceFluctuation β 1 0 L S φ ω ^ 4 ∂disorderLaw) ≤
      b.leftCost * b.rightCost * ccr25GaussianFiniteWordOperatorScale 4 b.interactionCost *
        Polymer.sigmaSq β ^ 2 +
      (2 : ℝ) ^ 32 *
        (Polymer.sigmaSq β ^ 2 * (L : ℝ) ^ 2 * Renewal.freeSecondMoment β L ^ 2 *
          (B * ∑ y ∈ S, φ y) ^ 2 +
        (max 1 (ccr25GaussianMomentUniformConstant 4)) ^ 8 *
          Polymer.sigmaSq β ^ 2 * Real.sqrt (Polymer.sigmaSq β) *
            (b.leftCost * b.rightCost * b.interactionCost ^ 2 * b.freeCost)) +
      b.leftCost * b.rightCost * (ccr25GaussianFiniteWordOperatorScale 4 b.interactionCost) ^ 3 *
          b.freeCost ^ 2 * Polymer.sigmaSq β ^ 3 /
            (1 - (ccr25GaussianFiniteWordOperatorScale 4 b.interactionCost * Polymer.sigmaSq β) * b.freeCost) := by
  let F : ℕ → ℝ := ccr25GaussianFiniteWordRun (configBox 4 S L) L 0 β
    (fun I => hattedReplicaBoundaryVector L I S φ) collisionIndicator
  have hnonneg (n : ℕ) : 0 ≤ F n := ccr25GaussianFiniteWordRun_nonneg _ _ _ _ _ _
    b.left_nonneg b.right_nonneg n
  have htail := b.tail_summable_le hσ hsmall
  have hsource := abs_centeredMoment_profileP2Fun_le_wordRuns (h := 4) (by norm_num)
    β 0 (le_refl 0) L φ S hφ hS
  have hcenter (ω : Disorder) :
      profileP2Fun β 0 L φ (fun _ => 1) ω -
        (∫ η, profileP2Fun β 0 L φ (fun _ => 1) η ∂disorderLaw) =
      finiteEntranceFluctuation β 1 0 L S φ ω := by
    simpa only [one_mul] using (finiteEntranceFluctuation_eq_centered_profile β 1 L S φ hS ω).symm
  simp_rw [hcenter] at hsource
  rw [abs_of_nonneg (integral_nonneg (fun _ => by positivity)), zero_mul, Real.exp_zero, one_mul] at hsource
  calc
    _ ≤ ∑ n ∈ Finset.range L, F n := hsource
    _ ≤ F 0 + F 1 + ∑' n, F (n + 2) := finite_run_sum_le_first_two_tail F hnonneg htail.1 L
    _ ≤ _ := add_le_add (add_le_add (b.first_run_le hσ)
      (ccr25_fourth_two_runs_le β L S φ hB (fun y _ => hφ y) hφB _ b hσ)) htail.2

end Critical2DKPZ.Extensions.GffTangent
