/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.Expansion
import Mathlib.Tactic

/-! # Truncated correctors and connected interval components -/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.OnePoint

open Critical2DKPZ.Blocks

/-- `M_i = 1_{𝓑_i} / 𝖹_i(q_{N_{i−1}})`, the truncated inverse multiplier. -/
def truncatedInverse (β : ℝ) (t : ℕ → ℕ) (i : ℕ) (ω : Disorder) : ℝ :=
  if |blockMass β t i ω - 1| ≤ 1 / 2 then (blockMass β t i ω)⁻¹ else 0

/-- `D̃^{closed}_{u,v} = D^{closed}_{u,v} ∏_{i=u}^v M_i`. -/
def truncatedCorrector (β : ℝ) (t : ℕ → ℕ) (u v : ℕ) (ω : Disorder) : ℝ :=
  closedDiscrepancy β t u v ω * ∏ i ∈ Finset.Icc u v, truncatedInverse β t i ω

/-- A bond at `i`: an interval of `F` or of `G` contains both blocks `i` and `i + 1`. -/
def PairBond (F G : Finset (ℕ × ℕ)) (i : ℕ) : Prop :=
  ∃ I ∈ F ∪ G, I.1 ≤ i ∧ i < I.2

/-- The connected components of the union of intervals of `F` and `G`. -/
def pairComponents (r s : ℕ) (F G : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) := by
  classical
  exact (Finset.Icc r s ×ˢ Finset.Icc r s).filter fun c =>
    c.1 < c.2 ∧ (∀ i ∈ Finset.Ico c.1 c.2, PairBond F G i) ∧ ¬ PairBond F G (c.1 - 1) ∧
      ¬ PairBond F G c.2

/-- A component is isolated when the total number of intervals from the two families contained in it is one. -/
def IsIsolatedComponent (F G : Finset (ℕ × ℕ)) (c : ℕ × ℕ) : Prop := by
  classical
  exact (F.filter fun I => c.1 ≤ I.1 ∧ I.2 ≤ c.2).card +
    (G.filter fun I => c.1 ≤ I.1 ∧ I.2 ≤ c.2).card = 1

/-- The component weight is a geometric length factor times an inverse endpoint-distance power, with exponent three-halves for isolated components and two otherwise. -/
def componentWeight (ε : ℝ) (K : ℕ) (F G : Finset (ℕ × ℕ)) (c : ℕ × ℕ) : ℝ := by
  classical
  exact ε ^ (c.2 - c.1) *
    ((K : ℝ) - c.2) ^ (-(if IsIsolatedComponent F G c then (3 / 2 : ℝ) else 2))

/-- The ratio summand of an interval family. -/
def familyTerm (β : ℝ) (t : ℕ → ℕ) (F : Finset (ℕ × ℕ)) (ω : Disorder) : ℝ :=
  ∏ I ∈ F, closedDiscrepancy β t I.1 I.2 ω /
    ∏ i ∈ Finset.Icc I.1 I.2, blockMass β t i ω

/-- The truncated reciprocal is nonnegative and bounded by two. -/
theorem truncatedInverse_nonneg_le_two (β : ℝ) (t : ℕ → ℕ) (i : ℕ) (ω : Disorder) :
    0 ≤ truncatedInverse β t i ω ∧ truncatedInverse β t i ω ≤ 2 := by
  unfold truncatedInverse
  split_ifs with h
  ·
    have hmass : (1 / 2 : ℝ) ≤ blockMass β t i ω := by
      have hlow := (abs_le.mp h).1
      linarith
    have hmasspos : 0 < blockMass β t i ω := lt_of_lt_of_le (by norm_num) hmass
    constructor
    · exact inv_nonneg.mpr hmasspos.le
    ·
      have hinv : 0 ≤ (blockMass β t i ω)⁻¹ := inv_nonneg.mpr hmasspos.le
      have hmul := mul_le_mul_of_nonneg_right hmass hinv
      have hcancel : blockMass β t i ω * (blockMass β t i ω)⁻¹ = 1 :=
        mul_inv_cancel₀ hmasspos.ne'
      nlinarith
  · norm_num

/-- The truncated reciprocal differs from one by at most twice the mass defect. -/
theorem abs_truncatedInverse_sub_one_le (β : ℝ) (t : ℕ → ℕ) (i : ℕ) (ω : Disorder) :
    |truncatedInverse β t i ω - 1| ≤ 2 * |blockMass β t i ω - 1| := by
  unfold truncatedInverse
  split_ifs with h
  ·
    have hmass : (1 / 2 : ℝ) ≤ blockMass β t i ω := by
      have hlow := (abs_le.mp h).1
      linarith
    have hmasspos : 0 < blockMass β t i ω := lt_of_lt_of_le (by norm_num) hmass
    have hinv : (blockMass β t i ω)⁻¹ ≤ 2 := by
      have hinvNonneg : 0 ≤ (blockMass β t i ω)⁻¹ := inv_nonneg.mpr hmasspos.le
      have hmul := mul_le_mul_of_nonneg_right hmass hinvNonneg
      have hcancel : blockMass β t i ω * (blockMass β t i ω)⁻¹ = 1 :=
        mul_inv_cancel₀ hmasspos.ne'
      nlinarith
    have hformula : (blockMass β t i ω)⁻¹ - 1 =
        (1 - blockMass β t i ω) / blockMass β t i ω := by
      field_simp [hmasspos.ne']
    rw [hformula, abs_div, abs_of_pos hmasspos, abs_sub_comm]
    rw [div_eq_mul_inv]
    calc
      |blockMass β t i ω - 1| * (blockMass β t i ω)⁻¹ ≤
          |blockMass β t i ω - 1| * 2 :=
        mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
      _ = 2 * |blockMass β t i ω - 1| := by ring
  ·
    have hlarge : (1 / 2 : ℝ) < |blockMass β t i ω - 1| := by
      exact lt_of_not_ge h
    norm_num
    linarith

end Critical2DKPZ.OnePoint

end
