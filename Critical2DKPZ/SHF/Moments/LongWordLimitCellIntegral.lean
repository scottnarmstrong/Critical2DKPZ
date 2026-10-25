/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.LongWordLimitCells
public import Critical2DKPZ.SHF.Moments.SinglePairWordInitialSupport
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-! # Exact start-cell integration for arbitrary tested collision words -/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators CompactlySupported
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

/-- The initial-cell step function whose integral is the tested word. -/
def wordCellInitialAction (ϑ : ℝ) (N n : ℕ) {h : ℕ}
    (φ : Fin h → C_c(Plane × Plane, ℝ)) (w : List (CollisionPair h))
    (x : Configuration h) : ℝ :=
  (N / 4 : ℝ) ^ h * ∑' y : Fin h → Site,
    (∏ i, cellTestWeight N (φ i) (latticePoint N (x i)) (y i)) *
      blockWordKernel (sigmaSq (criticalBeta ϑ N)) w n (fun i => latticePoint N (x i)) y

/-- Initial-cell integration recovers the tested word, for arbitrary compact
pair tests, with the exact `N/4` normalization. -/
theorem integrable_integral_wordCellInitialAction (ϑ : ℝ) {N : ℕ} (hN : 0 < N)
    (s t : ℝ) {h : ℕ} (φ : Fin h → C_c(Plane × Plane, ℝ))
    (w : List (CollisionPair h)) :
    Integrable (wordCellInitialAction ϑ N (evenCeil (N * t) - evenCeil (N * s)) φ w) ∧
      (∫ x, wordCellInitialAction ϑ N (evenCeil (N * t) - evenCeil (N * s)) φ w x) =
        testedBlockWord ϑ N s t φ w := by
  classical
  let S (i : Fin h) := (SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset.image Prod.fst
  let D := Fintype.piFinset S
  let g (x : Fin h → Site) := ∑' y : Fin h → Site,
    (∏ i, cellTestWeight N (φ i) (x i) (y i)) *
      blockWordKernel (sigmaSq (criticalBeta ϑ N)) w
        (evenCeil (N * t) - evenCeil (N * s)) x y
  have hg (z : Fin h → Site) (hz : z ∉ D) : g z = 0 := by
    have hm : ∃ i, z i ∉ S i := by simpa only [D, Fintype.mem_piFinset, not_forall] using hz
    obtain ⟨i, hi⟩ := hm
    change (∑' y : Fin h → Site, _) = 0
    trans ∑' _y : Fin h → Site, (0 : ℝ)
    swap
    · exact tsum_zero
    apply tsum_congr
    intro y
    have hw : cellTestWeight N (φ i) (z i) (y i) = 0 := by
      have hs : (z i, y i) ∉ (SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset :=
        fun hh => hi (Finset.mem_image.mpr ⟨_, hh, rfl⟩)
      have hzint : (∫ p in cell N (z i) ×ˢ cell N (y i), φ i p) = 0 := by
        by_contra hn
        exact hs ((SHF.Flow.finite_support_cellPairTest N (φ i)).mem_toFinset.mpr hn)
      simp only [cellTestWeight, hzint, mul_zero]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hw, zero_mul]
  have hD (z : Fin h → Site) (hz : z ∈ D) (i : Fin h) : z i ∈ evenLattice :=
    cellPairTest_initialSupport_even N (φ i) (Fintype.mem_piFinset.mp hz i)
  obtain ⟨hi, he₀⟩ := integrable_integral_configurationLatticeStep hN D hD g hg
  have he : (∫ x : Configuration h, g (fun i => latticePoint N (x i))) =
      (4 / (N : ℝ)) ^ h * ∑' z, g z := he₀.trans (by rw [tsum_eq_sum hg])
  refine ⟨hi.const_mul _, ?_⟩
  change (∫ x : Configuration h, (N / 4 : ℝ) ^ h * g (fun i => latticePoint N (x i))) = _
  rw [integral_const_mul, he, ← mul_assoc, ← mul_pow]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hc : (N / 4 : ℝ) * (4 / (N : ℝ)) = 1 := by field_simp
  rw [hc, one_pow, one_mul]
  rfl

end Critical2DKPZ.SHF.Moments
