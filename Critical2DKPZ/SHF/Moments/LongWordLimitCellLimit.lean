/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.LongWordLimitCellApprox
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitMass
import Mathlib.Tactic

/-! # The fixed-start limit after cell averaging -/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped BigOperators CompactlySupported Topology
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- A reachable endpoint is even when its starting site and duration have
matching terminal parity. -/
theorem configuration_endpoint_even_of_phase {h n : ℕ} (x y : Fin h → Site)
    (hp : ∀ i, Even (x i 0 + x i 1 + (n : ℤ)))
    (hy : y ∈ collisionWordConfigurationEndpointSet n x) : ∀ i, y i ∈ evenLattice := by
  intro i
  have hh := endpoints_accessible_phase n (x i) (y i) (Fintype.mem_piFinset.mp hy i)
  have hi := hp i
  change Even (y i 0 + y i 1)
  rw [Int.even_iff] at hh hi ⊢
  simp only [Pi.sub_apply] at hh
  omega

/-- Uniform error in the product cell coefficient costs only the row mass. -/
theorem abs_wordCellInitialAction_sub_terminalTest_le {h N n : ℕ}
    (ϑ : ℝ) (φ : Fin h → C_c(Plane × Plane, ℝ)) (w : List (CollisionPair h))
    (x : Configuration h) (hp : ∀ i, Even (latticePoint N (x i) 0 +
      latticePoint N (x i) 1 + (n : ℤ))) (ε : ℝ)
    (hc : ∀ y : Fin h → Site, (∀ i, y i ∈ evenLattice) →
      |(∏ i, (N / 4 : ℝ) * cellTestWeight N (φ i) (latticePoint N (x i)) (y i)) -
        ∏ i, φ i (x i, latticeRepresentative N (y i))| ≤ ε) :
    |wordCellInitialAction ϑ N n φ w x - wordTerminalTest N (sigmaSq (criticalBeta ϑ N))
      w n (fun i => latticePoint N (x i)) (fun y => ∏ i, φ i (x i, y i))| ≤
      ε * wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) w n
        (fun i => latticePoint N (x i)) (fun _ => 1) := by
  classical
  let σ := sigmaSq (criticalBeta ϑ N)
  let a : Fin h → Site := fun i => latticePoint N (x i)
  let D := collisionWordConfigurationEndpointSet n a
  let K := blockWordKernel σ w n a
  let A (y : Fin h → Site) := ∏ i, (N / 4 : ℝ) * cellTestWeight N (φ i) (a i) (y i)
  let B (y : Fin h → Site) := ∏ i, φ i (x i, latticeRepresentative N (y i))
  have haction : wordCellInitialAction ϑ N n φ w x = ∑ y ∈ D, K y * A y :=
    wordCellInitialAction_eq_sum ϑ N n φ w x
  have hterminal : wordTerminalTest N σ w n a (fun y => ∏ i, φ i (x i, y i)) =
      ∑ y ∈ D, K y * B y := wordTerminalTest_eq_sum _ _ _ _ _ _
  have hmass : wordTerminalTest N σ w n a (fun _ => 1) = ∑ y ∈ D, K y := by
    rw [wordTerminalTest_eq_sum]
    simp only [mul_one]
    rfl
  rw [haction, hterminal, hmass, ← Finset.sum_sub_distrib, Finset.mul_sum]
  calc
    _ ≤ ∑ y ∈ D, |K y * A y - K y * B y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ D, ε * K y := by
      apply Finset.sum_le_sum
      intro y hy
      have hK : 0 ≤ K y := blockWordKernel_nonneg σ (sigmaSq_nonneg _) w n a y
      rw [← mul_sub, abs_mul, abs_of_nonneg hK]
      exact (mul_le_mul_of_nonneg_left
        (hc y (configuration_endpoint_even_of_phase a y hp hy)) hK).trans_eq (mul_comm _ _)

/-- Along an even moving clock and away from the first collision diagonal,
cell averaging preserves a given terminal-test limit. -/
theorem tendsto_wordCellInitialAction_of_terminal_limit (ϑ : ℝ) {h : ℕ}
    (hD : WordPotentialDomination ϑ h) (α : CollisionPair h) (w : List (CollisionPair h))
    (hw : (α :: w).IsChain (· ≠ ·)) {τ : ℝ} (hτ : 0 < τ) (nN : ℕ → ℕ)
    (hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ))
    (heven : ∀ N, Even (nN N)) (x : Configuration h) (hsep : x α.1.1 ≠ x α.1.2)
    (φ : Fin h → C_c(Plane × Plane, ℝ)) (L : ℝ)
    (hlim : Tendsto (fun N => wordTerminalTest N (sigmaSq (criticalBeta ϑ N))
      (α :: w) (nN N) (fun i => latticePoint N (x i)) (fun y => ∏ i, φ i (x i, y i)))
        atTop (𝓝 L)) :
    Tendsto (fun N => wordCellInitialAction ϑ N (nN N) φ (α :: w) x) atTop (𝓝 L) := by
  obtain ⟨C, hC, hmass⟩ := eventually_wordTerminalTest_mass_le_of_potentialDomination
    ϑ hD α w hw hτ nN hn (fun N i => latticePoint N (x i)) x
    (fun i => tendsto_cellSample (x i)) hsep
  have hz : Tendsto (fun N => wordCellInitialAction ϑ N (nN N) φ (α :: w) x -
      wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) (α :: w) (nN N)
        (fun i => latticePoint N (x i)) (fun y => ∏ i, φ i (x i, y i))) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hmass, eventually_prod_normalized_cellTestWeight_close φ x
      (div_pos hε (mul_pos two_pos hC))] with N hmassN hclose
    have hp (i : Fin h) : Even (latticePoint N (x i) 0 + latticePoint N (x i) 1 + (nN N : ℤ)) :=
      (latticePoint_mem_evenLattice N (x i)).add (by exact_mod_cast heven N)
    have hh := abs_wordCellInitialAction_sub_terminalTest_le ϑ φ (α :: w) x hp
      (ε / (2 * C)) hclose
    rw [Real.dist_eq, sub_zero]
    calc
      _ ≤ ε / (2 * C) * wordTerminalTest N (sigmaSq (criticalBeta ϑ N))
          (α :: w) (nN N) (fun i => latticePoint N (x i)) (fun _ => 1) := hh
      _ ≤ ε / (2 * C) * C := mul_le_mul_of_nonneg_left hmassN (by positivity)
      _ = ε / 2 := by field_simp
      _ < ε := half_lt_self hε
  simpa only [zero_add, sub_add_cancel] using hz.add hlim

end Critical2DKPZ.SHF.Moments
