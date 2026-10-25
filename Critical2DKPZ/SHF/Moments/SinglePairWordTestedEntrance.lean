/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureGrid
import Mathlib.Tactic

/-! # Exact tested entrance formula for the two-particle word -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter Polymer DeltaBose
open scoped CompactlySupported Topology

private theorem collisionSlice_finite_weighted_sum {α : Type*}
    (J : Finset α) (c : α → ℝ) (f : α → Site → ℝ) (r : ℕ) (a b : Site) :
    (∑ j ∈ J, c j * collisionSlice r a b (f j)) =
      collisionSlice r a b (fun z => ∑ j ∈ J, c j * f j z) := by
  simp only [collisionSlice, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _hz
  apply Finset.sum_congr rfl
  intro j _hj
  ring

private theorem sum_weighted_collisionSlices {α : Type*}
    (J : Finset α) (c : α → ℝ) (f : α → ℕ → Site → ℝ)
    (Q : Finset ℕ) (a b : Site) :
    (∑ j ∈ J, c j * ∑ q ∈ Q, collisionSlice q a b (f j q)) =
      ∑ q ∈ Q, collisionSlice q a b (fun z => ∑ j ∈ J, c j * f j q z) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _hq => collisionSlice_finite_weighted_sum J c (fun j => f j q) q a b

/-- Averaging the terminal tests before summing the first entrance gives an
exact finite formula with the complete tested future tail. -/
theorem testedBlockWord_pairTwo_testedTailEntranceExpansion
    (ϑ : ℝ) (N : ℕ) (s t : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) :
    testedBlockWord ϑ N s t φ [pairTwo] =
      ∑ x ∈ Fintype.piFinset (fun i : Fin 2 =>
        ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset.image Prod.fst)),
        ∑ q ∈ Finset.Icc 1 (evenCeil (N * t) - evenCeil (N * s)),
          collisionSlice q (x 0) (x 1)
            (pairTwoFutureTestedTail (sigmaSq (criticalBeta ϑ N)) N
              (evenCeil (N * t) - evenCeil (N * s)) q φ x) := by
  classical
  refine (testedBlockWord_pairTwo_firstEntranceExpansion ϑ N s t φ).trans ?_
  apply Finset.sum_congr rfl
  intro x _hx
  let Y := Fintype.piFinset (fun i : Fin 2 =>
    ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset.image Prod.snd))
  let c : (Fin 2 → Site) → ℝ := fun y => ∏ i, cellTestWeight N (φ i) (x i) (y i)
  let f : (Fin 2 → Site) → ℕ → Site → ℝ := fun y q =>
    pairTwoFutureTest (sigmaSq (criticalBeta ϑ N))
      (evenCeil (N * t) - evenCeil (N * s)) y q
  exact sum_weighted_collisionSlices Y c f
    (Finset.Icc 1 (evenCeil (N * t) - evenCeil (N * s))) (x 0) (x 1)

private theorem collision_phase_remaining {L q : ℕ} (hL : Even L) (hq : q ≤ L)
    {a z : Site} (ha : a ∈ evenLattice) (hz : z ∈ endpoints a q) :
    Even (z 0 + z 1 + ((L - q : ℕ) : ℤ)) := by
  have hp := endpoints_accessible_phase q a z hz
  have hLe : Even (L : ℤ) := by exact_mod_cast hL
  change Even (a 0 + a 1) at ha
  have h := (hp.add ha).add hLe
  have hcast : ((L - q : ℕ) : ℤ) = (L : ℤ) - q := Int.ofNat_sub hq
  rw [hcast]
  have heq : z 0 + z 1 + ((L : ℤ) - q) =
      (((z - a) 0 + (z - a) 1 + q) + (a 0 + a 1) + L) - 2 * q := by
    simp only [Pi.sub_apply]
    ring
  rw [heq]
  exact h.sub (even_two_mul (q : ℤ))

/-- On phase-correct collision entrances, the sampled extension represents
the original complete future tail exactly. -/
theorem collisionEntrance_pairTwoFutureSampleProfile_grid
    (ϑ : ℝ) {N : ℕ} (hN : 0 < N) (L lo hi : ℕ) (hL : Even L) (hhi : hi ≤ L)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (x : Fin 2 → Site)
    (hx : x 0 ∈ evenLattice) :
    collisionEntrance N lo hi (x 0) (x 1) (pairTwoFutureSampleProfile ϑ N L φ x) =
      (N : ℝ)^2 * ∑ q ∈ Finset.Icc lo hi,
        collisionSlice q (x 0) (x 1) (pairTwoFutureTestedTail (criticalSigmaSq ϑ N) N L q φ x) := by
  rw [collisionEntrance, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [collisionSlice, collisionSlice, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [pairTwoFutureSampleProfile_grid ϑ hN L q φ x z
    (collision_phase_remaining hL ((Finset.mem_Icc.mp hq).2.trans hhi) hx hz)]
  ring

end Critical2DKPZ.SHF.Moments
