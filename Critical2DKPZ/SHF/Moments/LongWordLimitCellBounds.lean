/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.LongWordLimitCellIntegral
public import Critical2DKPZ.SHF.Moments.LongWordLimitSampling
public import Critical2DKPZ.SHF.Moments.LongWordLimitMajorant
public import Critical2DKPZ.SHF.Moments.WordDominationPairWordProfiles
public import Critical2DKPZ.SHF.Moments.WordLimitTerminal
import Critical2DKPZ.MomentBounds.CCR25GaussianMoments
import Mathlib.Tactic

/-! # An integrable uniform envelope for the compactly tested initial step -/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped BigOperators CompactlySupported Topology
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- Normalize a single cell weight by its initial cell volume. -/
theorem abs_normalized_cellTestWeight_le {N : ℕ} (hN : 0 < N)
    (φ : C_c(Plane × Plane, ℝ)) (M : ℝ) (hM : 0 ≤ M)
    (hφ : ∀ p, |φ p| ≤ M) (a b : Site) :
    |(N / 4 : ℝ) * cellTestWeight N φ a b| ≤ M := by
  have hh := mul_le_mul_of_nonneg_left
    (abs_cellTestWeight_le_four_mul_bound_div hN φ M hM hφ a b)
    (show 0 ≤ (N / 4 : ℝ) by positivity)
  have he : |(N / 4 : ℝ) * cellTestWeight N φ a b| =
      (N / 4 : ℝ) * |cellTestWeight N φ a b| := by
    rw [abs_mul, abs_of_nonneg (show 0 ≤ (N / 4 : ℝ) by positivity)]
  rw [← he] at hh
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  convert hh using 1
  field_simp

/-- A finite endpoint formula for the normalized initial step. -/
theorem wordCellInitialAction_eq_sum (ϑ : ℝ) (N n : ℕ) {h : ℕ}
    (φ : Fin h → C_c(Plane × Plane, ℝ)) (w : List (CollisionPair h))
    (x : Configuration h) :
    wordCellInitialAction ϑ N n φ w x =
      ∑ y ∈ collisionWordConfigurationEndpointSet n (fun i => latticePoint N (x i)),
        blockWordKernel (sigmaSq (criticalBeta ϑ N)) w n
          (fun i => latticePoint N (x i)) y *
        ∏ i, (N / 4 : ℝ) * cellTestWeight N (φ i) (latticePoint N (x i)) (y i) := by
  classical
  unfold wordCellInitialAction
  rw [tsum_eq_sum (s := collisionWordConfigurationEndpointSet n (fun i => latticePoint N (x i)))]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  · intro y hy
    rw [blockWordKernel_zero_of_endpoint_not_mem _ _ _ _ _ hy, mul_zero]

/-- A bounded family of compact tests controls the normalized initial-cell action by the product of their bounds times the terminal row mass. -/
theorem abs_wordCellInitialAction_le_mass (ϑ : ℝ) {N : ℕ} (hN : 0 < N)
    (n : ℕ) {h : ℕ} (φ : Fin h → C_c(Plane × Plane, ℝ))
    (w : List (CollisionPair h)) (x : Configuration h)
    (M : ℝ) (hM : 0 ≤ M) (hφ : ∀ i p, |φ i p| ≤ M) :
    |wordCellInitialAction ϑ N n φ w x| ≤ M ^ h *
      wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) w n
        (fun i => latticePoint N (x i)) (fun _ => 1) := by
  classical
  rw [wordCellInitialAction_eq_sum, wordTerminalTest_eq_sum]
  simp only [mul_one]
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y hy => ?_)
  have hK := blockWordKernel_nonneg _ (sigmaSq_nonneg (criticalBeta ϑ N)) w n
    (fun i => latticePoint N (x i)) y
  rw [abs_mul, abs_of_nonneg hK, Finset.abs_prod]
  have hh : (∏ i, |(N / 4 : ℝ) * cellTestWeight N (φ i) (latticePoint N (x i)) (y i)|) ≤ M ^ h := by
    calc
      _ ≤ ∏ _i : Fin h, M := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
        (fun i _ => abs_normalized_cellTestWeight_le hN (φ i) M hM (hφ i) _ _)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (mul_le_mul_of_nonneg_left hh hK).trans_eq (mul_comm _ _)

/-- The initial step vanishes outside a fixed compact box, including the
rounding slack, uniformly in every positive lattice scale. -/
theorem wordCellInitialAction_eq_zero_of_outside (ϑ : ℝ) {N : ℕ} (hN : 0 < N)
    (n : ℕ) {h : ℕ} (φ : Fin h → C_c(Plane × Plane, ℝ))
    (w : List (CollisionPair h)) (R : ℝ)
    (hφ : ∀ i p, φ i p ≠ 0 → ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R)
    (x : Configuration h) (hx : ¬ ∀ i, ‖x i‖ ≤ R + 4) :
    wordCellInitialAction ϑ N n φ w x = 0 := by
  classical
  obtain ⟨i, hi⟩ := not_forall.mp hx
  have hz (y : Fin h → Site) : cellTestWeight N (φ i) (latticePoint N (x i)) (y i) = 0 := by
    by_contra hn
    have hb := (cellTestWeight_ne_zero_imp_scaled_sites_bounded hN (φ i)
      (hφ i) (latticePoint N (x i)) (y i) hn).1
    have hd := dist_cellSample_le_two hN (x i)
    have ht : ‖x i‖ ≤ ‖cellSample N (x i)‖ + 2 :=
      norm_le_norm_add_const_of_dist_le (by simpa only [dist_comm] using hd)
    apply hi
    change ‖cellSample N (x i)‖ ≤ R + 2 at hb
    linarith only [hb, hd, ht]
  rw [wordCellInitialAction_eq_sum]
  apply Finset.sum_eq_zero
  intro y hy
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hz y, mul_zero]), mul_zero]

/-- Potential domination and compact support give one integrable envelope,
independent of all sufficiently large scales and all shorter horizons. -/
theorem eventually_wordCellInitialAction_integrable_bound (ϑ : ℝ) {h : ℕ}
    (hD : WordPotentialDomination ϑ h) {T : ℝ} (hT : 0 < T)
    (α : CollisionPair h) (w : List (CollisionPair h)) (hw : (α :: w).IsChain (· ≠ ·))
    (φ : Fin h → C_c(Plane × Plane, ℝ)) :
    ∃ B : Configuration h → ℝ, Integrable B ∧
      ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, (n : ℝ) ≤ T * N →
        ∀ᵐ x : Configuration h, |wordCellInitialAction ϑ N n φ (α :: w) x| ≤ B x := by
  obtain ⟨M, R, hM, hR, hφ, hφR⟩ := exists_collisionWord_compactTest_bounds φ
  obtain ⟨B, hB, hB0, hBb⟩ := exists_integrable_configuration_inverse_gap_majorant α (R + 4) (by positivity)
  obtain ⟨C, hC, hmass⟩ := hD hT α w hw
  obtain ⟨A, hA, hpotential⟩ := exists_cell_wordGapPotential_inverse_distance_bound
  refine ⟨fun x => (M ^ h * C * A) * B x, hB.const_mul _, ?_⟩
  filter_upwards [hmass, eventually_gt_atTop 0] with N hmassN hN
  intro n hn
  filter_upwards [ae_configuration_pair_ne α] with x hx
  by_cases hbox : ∀ i, ‖x i‖ ≤ R + 4
  · calc
      _ ≤ M ^ h * wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) (α :: w) n
          (fun i => latticePoint N (x i)) (fun _ => 1) :=
        abs_wordCellInitialAction_le_mass ϑ hN n φ (α :: w) x M hM hφ
      _ ≤ M ^ h * (C * Real.sqrt (N : ℝ) *
          wordGapPotential n (latticePoint N (x α.1.2) - latticePoint N (x α.1.1))) :=
        mul_le_mul_of_nonneg_left (hmassN n hn _) (pow_nonneg hM _)
      _ ≤ (M ^ h * C) * (A / ‖x α.1.2 - x α.1.1‖) := by
        calc
          _ = (M ^ h * C) * (Real.sqrt (N : ℝ) *
              wordGapPotential n (latticePoint N (x α.1.2) - latticePoint N (x α.1.1))) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hpotential N n hN _ _ hx) (by positivity)
      _ = (M ^ h * C * A) * ‖x α.1.2 - x α.1.1‖⁻¹ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hBb x hbox) (by positivity)
  · rw [wordCellInitialAction_eq_zero_of_outside ϑ hN n φ (α :: w) R hφR x hbox, abs_zero]
    exact mul_nonneg (by positivity) (hB0 x)

end Critical2DKPZ.SHF.Moments
