/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationCellSupport
public import Critical2DKPZ.SHF.Moments.WordDominationScaledBall
public import Critical2DKPZ.SHF.Moments.WordDominationPositiveTerminalAverage
import Mathlib.Tactic

/-! Compact endpoint tests admit uniform collision-word profile bounds. -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open scoped CompactlySupported

/-- A finite family of compact pair tests has one common bound on both
coordinates and on the absolute test values. -/
theorem exists_collisionWord_compactTest_bounds {h : ℕ}
    (φ : Fin h → C_c(Plane × Plane, ℝ)) :
    ∃ M R : ℝ, 0 ≤ M ∧ 0 ≤ R ∧
      (∀ i p, |φ i p| ≤ M) ∧
      (∀ i p, φ i p ≠ 0 → ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R) := by
  classical
  let B : Fin h → ℝ := fun i => Classical.choose
    ((φ i).hasCompactSupport.exists_bound_of_continuousOn
      (((φ i).continuous.abs.add continuous_fst.norm).add
        continuous_snd.norm).continuousOn)
  have hB (i : Fin h) (p : Plane × Plane) (hp : p ∈ tsupport (φ i)) :
      |φ i p| + ‖p.1‖ + ‖p.2‖ ≤ B i := by
    have hb := Classical.choose_spec
      ((φ i).hasCompactSupport.exists_bound_of_continuousOn
        (((φ i).continuous.abs.add continuous_fst.norm).add
          continuous_snd.norm).continuousOn) p hp
    change ‖(fun q : Plane × Plane =>
      |φ i q| + ‖q.1‖ + ‖q.2‖) p‖ ≤ B i at hb
    have hnonneg : 0 ≤ |φ i p| + ‖p.1‖ + ‖p.2‖ := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hb
    exact hb
  let C : ℝ := ∑ i : Fin h, max 0 (B i)
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    apply Finset.sum_nonneg
    intro i hi
    exact le_max_left 0 (B i)
  have hCi (i : Fin h) : max 0 (B i) ≤ C := by
    dsimp [C]
    exact Finset.single_le_sum
      (fun j hj => le_max_left 0 (B j)) (Finset.mem_univ i)
  refine ⟨C, C, hCnonneg, hCnonneg, ?_, ?_⟩
  · intro i p
    by_cases hp : φ i p = 0
    · simp [hp, hCnonneg]
    · have hts : p ∈ tsupport (φ i) :=
        subset_closure (Function.mem_support.mpr hp)
      have hbound := hB i p hts
      have hterm : |φ i p| ≤ max 0 (B i) := by
        have hBnonneg : 0 ≤ max 0 (B i) := le_max_left _ _
        have hBupper : B i ≤ max 0 (B i) := le_max_right _ _
        have hn1 : 0 ≤ ‖p.1‖ := norm_nonneg _
        have hn2 : 0 ≤ ‖p.2‖ := norm_nonneg _
        linarith
      exact hterm.trans (hCi i)
  · intro i p hp
    have hts : p ∈ tsupport (φ i) :=
      subset_closure (Function.mem_support.mpr hp)
    have hbound := hB i p hts
    have hterm1 : ‖p.1‖ ≤ max 0 (B i) := by
      have hBnonneg : 0 ≤ max 0 (B i) := le_max_left _ _
      have hBupper : B i ≤ max 0 (B i) := le_max_right _ _
      have ha : 0 ≤ |φ i p| := abs_nonneg _
      have hn2 : 0 ≤ ‖p.2‖ := norm_nonneg _
      linarith
    have hterm2 : ‖p.2‖ ≤ max 0 (B i) := by
      have hBnonneg : 0 ≤ max 0 (B i) := le_max_left _ _
      have hBupper : B i ≤ max 0 (B i) := le_max_right _ _
      have ha : 0 ≤ |φ i p| := abs_nonneg _
      have hn1 : 0 ≤ ‖p.1‖ := norm_nonneg _
      linarith
    exact ⟨hterm1.trans (hCi i), hterm2.trans (hCi i)⟩

/-- Membership in the radius-`R` support box implies a scaled norm bound
with the normalization used by the endpoint-average estimate. -/
theorem collisionWord_scaledNorm_le_two_mul_of_mem_scaledBall
    {N : ℕ} (hN : 1 ≤ N) {R : ℝ} (hR : 0 ≤ R) {z : Site}
    (hz : z ∈ collisionWordScaledBallSites N R) :
    ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z‖ ≤ 2 * (R + 2) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hscale : (Real.sqrt ((N : ℝ) / 2))⁻¹ = Real.sqrt 2 / Real.sqrt N := by
    have hleft : (Real.sqrt ((N : ℝ) / 2))⁻¹ ^ 2 = 2 / N := by
      rw [inv_pow, Real.sq_sqrt (by positivity : 0 ≤ (N : ℝ) / 2)]
      field_simp
    have hright : (Real.sqrt 2 / Real.sqrt N) ^ 2 = 2 / N := by
      rw [div_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ)),
        Real.sq_sqrt hNreal.le]
    have hleft_nonneg : 0 ≤ (Real.sqrt ((N : ℝ) / 2))⁻¹ := by positivity
    have hright_nonneg : 0 ≤ Real.sqrt 2 / Real.sqrt N := by positivity
    nlinarith
  have hraw : ‖siteToPlane z‖ ≤ (R + 2) * Real.sqrt (N : ℝ) :=
    (Finset.mem_filter.mp hz).2
  have hrootN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNreal
  have hroot2 : Real.sqrt 2 ≤ 2 := by
    have hsquare := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hnorm :
      ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z‖ =
        (Real.sqrt ((N : ℝ) / 2))⁻¹ * ‖siteToPlane z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hnorm, hscale]
  calc
    (Real.sqrt 2 / Real.sqrt (N : ℝ)) * ‖siteToPlane z‖ ≤
        (Real.sqrt 2 / Real.sqrt (N : ℝ)) *
          ((R + 2) * Real.sqrt (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = Real.sqrt 2 * (R + 2) := by field_simp [ne_of_gt hrootN]
    _ ≤ 2 * (R + 2) :=
      mul_le_mul_of_nonneg_right hroot2 (by positivity)

/-- Enlarge a cell-support box once so it contains the endpoints produced by
the positive-duration terminal walk average. -/
theorem collisionWord_scaledBall_subset_enlarged
    {N : ℕ} (hN : 1 ≤ N) {R : ℝ} (hR : 0 ≤ R) :
    collisionWordScaledBallSites N R ⊆ collisionWordScaledBallSites N (2 * (R + 2)) := by
  intro z hz
  apply mem_collisionWordScaledBallSites_of_scaledNorm hN (by positivity)
  exact (collisionWord_scaledNorm_le_two_mul_of_mem_scaledBall hN hR hz).trans (by nlinarith)

end Critical2DKPZ.SHF.Moments

end
