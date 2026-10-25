/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SlabProductsCore
public import Critical2DKPZ.SHF.Moments.WordDominationCellSupport
public import Critical2DKPZ.SHF.Moments.WordDominationPairWordProfiles
import Mathlib.Tactic

/-! # Initial support sizes for compact two-particle tests -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory
open scoped CompactlySupported

/-- A nonzero cell-pair integral uses an even initial site. -/
theorem cellPairTest_initialSupport_even (N : ℕ) (φ : C_c(Plane × Plane, ℝ))
    {a : Site} (ha : a ∈ ((SHF.Flow.finite_support_cellPairTest N φ).toFinset.image Prod.fst)) :
    a ∈ evenLattice := by
  classical
  obtain ⟨⟨w, z⟩, hwz, rfl⟩ := Finset.mem_image.mp ha
  have hint := (SHF.Flow.finite_support_cellPairTest N φ).mem_toFinset.mp hwz
  by_contra hw
  have he := cell_eq_empty_of_not_even (N := N) hw
  apply hint
  rw [he, Set.empty_prod, MeasureTheory.setIntegral_empty]

/-- The initial cell-pair support lies in the compact test's scaled spatial ball enlarged by the cell mesh. -/
theorem cellPairTest_initialSupport_scaledNorm_le {N : ℕ} (hN : 0 < N)
    (φ : C_c(Plane × Plane, ℝ)) {R : ℝ}
    (hR : ∀ p, φ p ≠ 0 → ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R)
    {a : Site} (ha : a ∈ ((SHF.Flow.finite_support_cellPairTest N φ).toFinset.image Prod.fst)) :
    ‖latticeRepresentative N a‖ ≤ R + 2 := by
  classical
  obtain ⟨⟨w, z⟩, hwz, rfl⟩ := Finset.mem_image.mp ha
  have hint := (SHF.Flow.finite_support_cellPairTest N φ).mem_toFinset.mp hwz
  have hweight : cellTestWeight N φ w z ≠ 0 :=
    mul_ne_zero (by positivity : (N / 4 : ℝ) ≠ 0) hint
  exact (cellTestWeight_ne_zero_imp_scaled_sites_bounded hN φ hR w z hweight).1

/-- A macroscopic point whose sampled initial site contributes to the cell
support lies in a fixed ball, uniformly at every positive lattice scale. -/
theorem cellPairTest_initialSupport_sampled_norm_le {N : ℕ} (hN : 0 < N)
    (φ : C_c(Plane × Plane, ℝ)) {R : ℝ}
    (hR : ∀ p, φ p ≠ 0 → ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R)
    {a : Plane} (ha : latticePoint N a ∈
      ((SHF.Flow.finite_support_cellPairTest N φ).toFinset.image Prod.fst)) :
    ‖a‖ ≤ R + 4 := by
  have hb := cellPairTest_initialSupport_scaledNorm_le hN φ hR ha
  have hd := dist_cellSample_le_two hN a
  have hn : ‖a‖ ≤ dist a (cellSample N a) + ‖cellSample N a‖ := by
    simpa only [dist_zero_right] using dist_triangle a (cellSample N a) 0
  change ‖cellSample N a‖ ≤ R + 2 at hb
  rw [dist_comm] at hd
  linarith only [hb, hd, hn]

/-- The initial lattice support of a fixed compact pair test has size `O(N)`;
the constant is independent of the lattice scale. -/
theorem exists_cellPairTest_initialSupport_card_le (φ : C_c(Plane × Plane, ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N →
      ((((SHF.Flow.finite_support_cellPairTest N φ).toFinset.image Prod.fst).card : ℝ) ≤ C * N) := by
  classical
  obtain ⟨M, R, _hM, hR, _hφ, hφR⟩ := exists_collisionWord_compactTest_bounds
    (fun _ : Fin 1 => φ)
  obtain ⟨C, hC, hcard⟩ := card_collisionWordScaledBallSites_le
  refine ⟨C * (R + 2)^2, mul_nonneg hC (sq_nonneg _), ?_⟩
  intro N hN
  have hsub : ((SHF.Flow.finite_support_cellPairTest N φ).toFinset.image Prod.fst) ⊆
      collisionWordScaledBallSites N R := by
    intro a ha
    have hb := cellPairTest_initialSupport_scaledNorm_le hN φ (hφR 0) ha
    exact mem_collisionWordScaledBallSites_of_scaledNorm hN hR a hb
  have hc : ((((SHF.Flow.finite_support_cellPairTest N φ).toFinset.image Prod.fst).card : ℝ)) ≤
      ((collisionWordScaledBallSites N R).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
  exact hc.trans (hcard hN hR)

end Critical2DKPZ.SHF.Moments
