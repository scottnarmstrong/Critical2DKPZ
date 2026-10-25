/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.Core
import Mathlib.Tactic

/-! # Random suffix masses of discrepancy strings -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.Blocks

/-- The discrepancy string starting from one site and ending in the final flat polymer block. -/
def discrepancyTailMass (β : ℝ) (t : ℕ → ℕ) (u v : ℕ) (x : Site)
    (ω : Disorder) : ℝ :=
  ∑' y, discrepancyString β t u (v - u) x y ω *
    pointToPlane β (t (v - 1)) (t v - t (v - 1)) y ω

/-- The suffix with no discrepancy kernels is the final block mass. -/
theorem discrepancyTailMass_self (β : ℝ) (t : ℕ → ℕ) (v : ℕ) (x : Site) (ω : Disorder) :
    discrepancyTailMass β t v v x ω =
      pointToPlane β (t (v - 1)) (t v - t (v - 1)) x ω := by
  simp only [discrepancyTailMass, Nat.sub_self, discrepancyString, ite_mul,
    one_mul, zero_mul, tsum_ite_eq']

/-- A suffix mass has every positive finite moment. -/
theorem memLp_discrepancyTailMass (β : ℝ) (t : ℕ → ℕ) (u v : ℕ) (x : Site)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    MemLp (discrepancyTailMass β t u v x) p disorderLaw := by
  have hp2zero : 2 * p ≠ 0 := mul_ne_zero (by norm_num) hp0
  have hp2top : 2 * p ≠ ∞ := ENNReal.mul_ne_top (by norm_num) hp
  have heq : discrepancyTailMass β t u v x = fun ω =>
      ∑ y ∈ discrepancyStringSupport t u (v - u) x,
        discrepancyString β t u (v - u) x y ω *
          pointToPlane β (t (v - 1)) (t v - t (v - 1)) y ω := by
    funext ω
    apply tsum_eq_sum
    intro y hy
    rw [discrepancyString_eq_zero_of_not_mem_support β t u (v - u) x y ω hy, zero_mul]
  rw [heq]
  exact memLp_finsetSum _ fun y _ => Polymer.memLp_mul_double p
    (memLp_discrepancyString β t u (v - u) x y (2 * p) hp2zero hp2top)
    (Polymer.memLp_pointToPlane β (t (v - 1)) (t v - t (v - 1)) y (2 * p) hp2top)

/-- The suffix uses only the disorder of its own block interval. -/
theorem measurable_discrepancyTailMass_block (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t)
    (u v : ℕ) (huv : u ≤ v) (x : Site) :
    Measurable[Gaussian.disorderBlock (t (u - 1)) (t v)] (discrepancyTailMass β t u v x) := by
  let : MeasurableSpace Disorder := Gaussian.disorderBlock (t (u - 1)) (t v)
  have hstr (y) := measurable_discrepancyString_block β t ht u (v - u) v (by omega) x y
  have hlast (y : Site) : Measurable[Gaussian.disorderBlock (t (u - 1)) (t v)]
      (fun ω => pointToPlane β (t (v - 1)) (t v - t (v - 1)) y ω) := by
    have hlocal := Polymer.measurable_pointToPlane_block β (t (v - 1))
      (t v - t (v - 1)) y
    rw [Nat.add_sub_of_le (ht (by omega))] at hlocal
    exact hlocal.mono (Gaussian.disorderBlock_mono (ht (by omega)) le_rfl) le_rfl
  exact Measurable.tsum fun y => (hstr y).mul (hlast y)

/-- Closed strings are obtained by applying their initial heat profile to the suffix mass. -/
theorem closedDiscrepancy_eq_heatStart_tail (β : ℝ) (t : ℕ → ℕ)
    (u v : ℕ) (ω : Disorder) :
    closedDiscrepancy β t u v ω =
      ∑' x, srwKernel (t (u - 1)) x * discrepancyTailMass β t u v x ω := by
  unfold closedDiscrepancy discrepancyTailMass
  apply tsum_congr
  intro x
  rw [← tsum_mul_left]
  apply tsum_congr
  intro y
  ring

/-- The suffix mass factors at its first discrepancy block. -/
theorem discrepancyTailMass_leftFactor (β : ℝ) (t : ℕ → ℕ)
    {u v : ℕ} (huv : u < v) (x : Site) (ω : Disorder) :
    discrepancyTailMass β t u v x ω =
      ∑' y, blockDiscrepancy β t u x y ω * discrepancyTailMass β t (u + 1) v y ω := by
  let k := v - (u + 1)
  have hlen : v - u = k + 1 := by dsimp [k]; omega
  have hdouble : Summable (fun p : Site × Site =>
      blockDiscrepancy β t u x p.1 ω * discrepancyString β t (u + 1) k p.1 p.2 ω *
        pointToPlane β (t (v - 1)) (t v - t (v - 1)) p.2 ω) := by
    let A := blockDiscrepancySupport t u x
    let B := A.biUnion (fun y => discrepancyStringSupport t (u + 1) k y)
    apply summable_of_ne_finset_zero (s := A ×ˢ B)
    intro p hp
    by_cases hy : p.1 ∈ A
    · have hz : p.2 ∉ discrepancyStringSupport t (u + 1) k p.1 := by
        intro hz
        exact hp (Finset.mem_product.2 ⟨hy, Finset.mem_biUnion.2 ⟨p.1, hy, hz⟩⟩)
      rw [discrepancyString_eq_zero_of_not_mem_support β t (u + 1) k p.1 p.2 ω hz,
        mul_zero, zero_mul]
    · rw [blockDiscrepancy_eq_zero_of_not_mem_support β t u x p.1 ω hy,
        zero_mul, zero_mul]
  unfold discrepancyTailMass
  rw [hlen]
  calc
    _ = ∑' z, ∑' y, blockDiscrepancy β t u x y ω *
        discrepancyString β t (u + 1) k y z ω *
          pointToPlane β (t (v - 1)) (t v - t (v - 1)) z ω := by
      apply tsum_congr
      intro z
      rw [discrepancyString_leftFactor β t u k x z ω]
      exact (tsum_mul_right (f := fun y => blockDiscrepancy β t u x y ω *
        discrepancyString β t (u + 1) k y z ω)
        (a := pointToPlane β (t (v - 1)) (t v - t (v - 1)) z ω)).symm
    _ = ∑' y, ∑' z, blockDiscrepancy β t u x y ω *
        discrepancyString β t (u + 1) k y z ω *
          pointToPlane β (t (v - 1)) (t v - t (v - 1)) z ω := Summable.tsum_comm (f := fun y z : Site =>
            blockDiscrepancy β t u x y ω * discrepancyString β t (u + 1) k y z ω *
              pointToPlane β (t (v - 1)) (t v - t (v - 1)) z ω) hdouble
    _ = _ := by
      apply tsum_congr
      intro y
      calc
        _ = ∑' z, blockDiscrepancy β t u x y ω *
            (discrepancyString β t (u + 1) k y z ω *
              pointToPlane β (t (v - 1)) (t v - t (v - 1)) z ω) := by
          apply tsum_congr
          intro z
          exact mul_assoc _ _ _
        _ = _ := tsum_mul_left

end Critical2DKPZ.Blocks
