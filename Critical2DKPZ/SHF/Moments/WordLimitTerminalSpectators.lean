/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitTerminal
public import Critical2DKPZ.SHF.Moments.WordLimitSpectators
import Critical2DKPZ.Polymer.Profiles
import Mathlib.Tactic

/-! # Spectator factors in fixed-start terminal tests -/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

/-- A one-letter terminal tensor test is its two-particle test times free spectator tests. -/
theorem wordTerminalTest_single_tensor {h : ℕ} (N : ℕ) (σ : ℝ)
    (α : CollisionPair h) (n : ℕ) (x : Fin h → Site) (ψ : Fin h → Plane → ℝ) :
    wordTerminalTest N σ [α] n x (fun y => ∏ i, ψ i (y i)) =
      wordTerminalTest N σ [pairTwo] n (pairRestrict α x)
        (fun y => ∏ j, (pairRestrict α ψ) j (y j)) *
        ∏ i : Spectator α, ∑ z ∈ endpoints (x i.1) n,
          srwKernel n (z - x i.1) * ψ i.1 (latticeRepresentative N z) := by
  classical
  let D : Fin h → Finset Site := fun i => endpoints (x i) n
  let F : (Fin 2 → Site) → ℝ := fun q =>
    blockWordKernel σ [pairTwo] n (pairRestrict α x) q *
      ∏ j, (pairRestrict α ψ) j (latticeRepresentative N (q j))
  let G : Spectator α → Site → ℝ := fun i z =>
    srwKernel n (z - x i.1) * ψ i.1 (latticeRepresentative N z)
  have hpoint (y : Fin h → Site) :
      blockWordKernel σ [α] n x y *
          (∏ i, ψ i (latticeRepresentative N (y i))) =
        F (pairRestrict α y) * ∏ i : Spectator α, G i (y i.1) := by
    have htest :
        (∏ i, ψ i (latticeRepresentative N (y i))) =
          (∏ j, (pairRestrict α ψ) j (latticeRepresentative N (pairRestrict α y j))) *
            ∏ i : Spectator α, ψ i.1 (latticeRepresentative N (y i.1)) := by
      simpa [pairRestrict, Fin.prod_univ_two] using
        wordLimit_prod_pair_spectators α (fun i => ψ i (latticeRepresentative N (y i)))
    rw [blockWordKernel_single_eq, htest]
    simp only [F, G, Finset.prod_mul_distrib]
    ring
  have hD :
      (fun j : Fin 2 => D (if j = 0 then α.1.1 else α.1.2)) =
        fun j : Fin 2 => endpoints (pairRestrict α x j) n := by
    funext j
    fin_cases j <;> rfl
  have hpair :
      (∑ q ∈ Fintype.piFinset (fun j : Fin 2 => D (if j = 0 then α.1.1 else α.1.2)),
        F q) =
        wordTerminalTest N σ [pairTwo] n (pairRestrict α x)
          (fun y => ∏ j, (pairRestrict α ψ) j (y j)) := by
    rw [wordTerminalTest_eq_sum, hD]
    rfl
  calc
    _ = ∑ y ∈ Fintype.piFinset D,
        blockWordKernel σ [α] n x y * ∏ i, ψ i (latticeRepresentative N (y i)) :=
      wordTerminalTest_eq_sum N σ [α] n x _
    _ = ∑ y ∈ Fintype.piFinset D,
        F (pairRestrict α y) * ∏ i : Spectator α, G i (y i.1) := by
      apply Finset.sum_congr rfl
      intro y hy
      exact hpoint y
    _ = (∑ q ∈ Fintype.piFinset
          (fun j : Fin 2 => D (if j = 0 then α.1.1 else α.1.2)), F q) *
        ∏ i : Spectator α, ∑ z ∈ D i.1, G i z :=
      wordLimit_sum_pair_spectator_coordinates α D F G
    _ = _ := by rw [hpair]

/-- Spectator strands have mass one, so a one-letter row mass depends only on its pair. -/
theorem wordTerminalTest_single_one_eq_pair {h : ℕ} (N : ℕ) (σ : ℝ)
    (α : CollisionPair h) (n : ℕ) (x : Fin h → Site) :
    wordTerminalTest N σ [α] n x (fun _ => 1) =
      wordTerminalTest N σ [pairTwo] n (pairRestrict α x) (fun _ => 1) := by
  have h := wordTerminalTest_single_tensor N σ α n x (fun _ _ => 1)
  simpa [pairRestrict, sum_srwKernel_endpoints] using h

end Critical2DKPZ.SHF.Moments
