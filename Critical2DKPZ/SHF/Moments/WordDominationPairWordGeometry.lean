/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationPairWordProfiles
public import Critical2DKPZ.SHF.Moments.WordDominationBlockWordSupport
import Mathlib.Tactic

/-! # Finite support reduction for compact pair words -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.Polymer
open scoped BigOperators CompactlySupported

attribute [local instance] Classical.propDecidable

private theorem collisionWord_cellWeight_pair_support {h N : ℕ} (hN : 0 < N)
    {R : ℝ} (hR : 0 ≤ R) (φ : Fin h → C_c(Plane × Plane, ℝ))
    (hφR : ∀ i p, φ i p ≠ 0 → ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R)
    (i : Fin h) (a b : Site)
    (hw : cellTestWeight N (φ i) a b ≠ 0) :
    a ∈ collisionWordScaledBallSites N R ∧ b ∈ collisionWordScaledBallSites N R := by
  have hN1 : 1 ≤ N := by omega
  obtain ⟨ha, hb⟩ := cellTestWeight_ne_zero_imp_scaled_sites_bounded
    hN (φ i) (hφR i) a b hw
  exact ⟨mem_collisionWordScaledBallSites_of_scaledNorm hN1 hR a ha,
    mem_collisionWordScaledBallSites_of_scaledNorm hN1 hR b hb⟩

private theorem collisionWord_cellWeightProduct_zero_of_left_outside
    {h N : ℕ} (hN : 0 < N) {R : ℝ} (hR : 0 ≤ R)
    (φ : Fin h → C_c(Plane × Plane, ℝ))
    (hφR : ∀ i p, φ i p ≠ 0 → ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R)
    {x : Fin h → Site} (hx : x ∉ Fintype.piFinset
      (fun _ : Fin h => collisionWordScaledBallSites N R)) (y : Fin h → Site) :
    (∏ i, cellTestWeight N (φ i) (x i) (y i)) = 0 := by
  classical
  have hx' : ¬ ∀ i, x i ∈ collisionWordScaledBallSites N R := by
    simpa only [Fintype.mem_piFinset] using hx
  obtain ⟨i, hi⟩ := not_forall.mp hx'
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  by_contra hne
  exact hi (collisionWord_cellWeight_pair_support hN hR φ hφR i (x i) (y i) hne).1

private theorem collisionWord_cellWeightProduct_zero_of_right_outside
    {h N : ℕ} (hN : 0 < N) {R : ℝ} (hR : 0 ≤ R)
    (φ : Fin h → C_c(Plane × Plane, ℝ))
    (hφR : ∀ i p, φ i p ≠ 0 → ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R)
    (x : Fin h → Site) {y : Fin h → Site}
    (hy : y ∉ Fintype.piFinset
      (fun _ : Fin h => collisionWordScaledBallSites N R)) :
    (∏ i, cellTestWeight N (φ i) (x i) (y i)) = 0 := by
  classical
  have hy' : ¬ ∀ i, y i ∈ collisionWordScaledBallSites N R := by
    simpa only [Fintype.mem_piFinset] using hy
  obtain ⟨i, hi⟩ := not_forall.mp hy'
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  by_contra hne
  exact hi (collisionWord_cellWeight_pair_support hN hR φ hφR i (x i) (y i) hne).2

/-- Compact cell tests restrict both configuration sums of a tested block
word to the finite scaled support box. -/
theorem collisionWord_testedBlockWord_eq_sum_on_scaledBall {h N : ℕ}
    (ϑ : ℝ) (hN : 0 < N) (s t R : ℝ) (hR : 0 ≤ R)
    (φ : Fin h → C_c(Plane × Plane, ℝ))
    (hφR : ∀ i p, φ i p ≠ 0 → ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R)
    (w : List (CollisionPair h)) :
    testedBlockWord ϑ N s t φ w =
      ∑ x ∈ Fintype.piFinset (fun _ : Fin h => collisionWordScaledBallSites N R),
        ∑ y ∈ Fintype.piFinset (fun _ : Fin h => collisionWordScaledBallSites N R),
          (∏ i, cellTestWeight N (φ i) (x i) (y i)) *
            blockWordKernel (sigmaSq (criticalBeta ϑ N)) w
              (evenCeil (N * t) - evenCeil (N * s)) x y := by
  classical
  let X : Finset (Fin h → Site) :=
    Fintype.piFinset (fun _ : Fin h => collisionWordScaledBallSites N R)
  have hleft (x : Fin h → Site) (hx : x ∉ X) (y : Fin h → Site) :
      (∏ i, cellTestWeight N (φ i) (x i) (y i)) = 0 := by
    exact collisionWord_cellWeightProduct_zero_of_left_outside hN hR φ hφR hx y
  have hright (x : Fin h → Site) (y : Fin h → Site) (hy : y ∉ X) :
      (∏ i, cellTestWeight N (φ i) (x i) (y i)) = 0 := by
    exact collisionWord_cellWeightProduct_zero_of_right_outside hN hR φ hφR x hy
  unfold testedBlockWord
  rw [tsum_eq_sum (s := X)]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [tsum_eq_sum (s := X)]
    · intro y hy
      rw [hright x y hy]
      simp
  · intro x hx
    have hzero : ∀ y : Fin h → Site,
        (∏ i, cellTestWeight N (φ i) (x i) (y i)) *
          blockWordKernel (sigmaSq (criticalBeta ϑ N)) w
            (evenCeil (N * t) - evenCeil (N * s)) x y = 0 := by
      intro y
      rw [hleft x hx y]
      simp
    simp_rw [hzero]
    simp

end Critical2DKPZ.SHF.Moments

end
