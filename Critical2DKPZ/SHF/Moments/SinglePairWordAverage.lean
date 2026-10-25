/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWord
import Mathlib.Tactic

/-! # Averaged future profile for the two-particle word -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open Polymer
open scoped CompactlySupported

/-- The two-particle future tail after averaging its two terminal cell tests. -/
def pairTwoFutureTestedTail (σ : ℝ) (N n s : ℕ)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (x : Fin 2 → Site) (z : Site) : ℝ :=
  ∑ y ∈ Fintype.piFinset (fun i : Fin 2 =>
      ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset.image
        Prod.snd)),
    (∏ i, cellTestWeight N (φ i) (x i) (y i)) * pairTwoFutureTest σ n y s z

/-- Translating a walk endpoint to its displacement preserves reachability. -/
theorem mem_endpoints_sub {z w : Site} {r : ℕ} :
    w ∈ Polymer.endpoints z r ↔ w - z ∈ Polymer.endpoints 0 r := by
  rw [Polymer.mem_endpoints_iff, Polymer.mem_endpoints_iff]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_⟩
    rw [Polymer.walkPosition_eq_start_add] at hp
    rw [← hp]
    abel
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_⟩
    rw [Polymer.walkPosition_eq_start_add, hp]
    abel

/-- The averaged future tail is a finite sum of spatial renewal masses against
the product of the two one-replica terminal profiles. -/
theorem pairTwoFutureTestedTail_eq_terminalFactorSum
    (σ : ℝ) (N n s : ℕ) (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (x : Fin 2 → Site) (z : Site) :
    pairTwoFutureTestedTail σ N n s φ x z =
      σ * ∑ r ∈ Finset.range (n - s + 1),
        ∑ w ∈ Polymer.endpoints z r,
          Collision.spatialRenewal σ r (w - z) *
            ∏ i : Fin 2,
              pairTwoFutureTerminalCellFactor N (n - s - r) φ x w i := by
  classical
  let Y : Fin 2 → Finset Site := fun i =>
    ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset.image
      Prod.snd)
  let A : (Fin 2 → Site) → ℕ → Finset Site := fun y r =>
    Polymer.endpoints (y 0) (n - s - r) ∩ Polymer.endpoints (y 1) (n - s - r)
  let W : ℕ → Finset Site := fun r => Polymer.endpoints z r
  let g : (Fin 2 → Site) → ℕ → Site → ℝ := fun y r w =>
    Collision.spatialRenewal σ r (w - z) *
      (srwKernel (n - s - r) (y 0 - w) * srwKernel (n - s - r) (y 1 - w))
  have hzero (y : Fin 2 → Site) (r : ℕ) (w : Site)
      (hwA : w ∈ A y r) (hwW : w ∉ W r) : g y r w = 0 := by
    have hz : w - z ∉ Polymer.endpoints 0 r := by
      intro hmem
      exact hwW ((mem_endpoints_sub).2 hmem)
    simp [g, spatialRenewal_eq_zero_of_not_mem_endpoints σ r (w - z) hz]
  have hsum (y : Fin 2 → Site) (r : ℕ) :
      (∑ w ∈ A y r, g y r w) =
        ∑ w ∈ W r, (if w ∈ A y r then g y r w else 0) := by
    let S := A y r
    let T := W r
    have hleft : ∀ w ∈ S, w ∉ S ∩ T → g y r w = 0 := by
      intro w hwS hnot
      apply hzero y r w hwS
      intro hwT
      exact hnot (Finset.mem_inter.mpr ⟨hwS, hwT⟩)
    have hleft' : ∀ w ∈ S, w ∉ S ∩ T →
        (if w ∈ S then g y r w else 0) = 0 := by
      intro w hwS hnot
      simp [hwS, hleft w hwS hnot]
    have hright : ∀ w ∈ T, w ∉ S ∩ T → (if w ∈ S then g y r w else 0) = 0 := by
      intro w hwT hnot
      have hwS : w ∉ S := by
        intro hmem
        exact hnot (Finset.mem_inter.mpr ⟨hmem, hwT⟩)
      simp [hwS]
    calc
      _ = ∑ w ∈ S, (if w ∈ S then g y r w else 0) := by
        apply Finset.sum_congr rfl
        intro w hw
        rw [ite_eq_left hw]
      _ = ∑ w ∈ S ∩ T, (if w ∈ S then g y r w else 0) :=
        (Finset.sum_subset Finset.inter_subset_left hleft').symm
      _ = ∑ w ∈ T, (if w ∈ S then g y r w else 0) :=
        Finset.sum_subset Finset.inter_subset_right hright
  let c : (Fin 2 → Site) → ℝ := fun y =>
    ∏ i, cellTestWeight N (φ i) (x i) (y i)
  have hsumR (r : ℕ) :
      (∑ y ∈ Fintype.piFinset Y, c y * ∑ w ∈ A y r, g y r w) =
        ∑ w ∈ W r, Collision.spatialRenewal σ r (w - z) *
          ∏ i : Fin 2, pairTwoFutureTerminalCellFactor N (n - s - r) φ x w i := by
    calc
      _ = ∑ y ∈ Fintype.piFinset Y,
          ∑ w ∈ W r, c y * (if w ∈ A y r then g y r w else 0) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [show c y * (∑ w ∈ A y r, g y r w) =
            c y * (∑ w ∈ W r, (if w ∈ A y r then g y r w else 0)) by
              exact congrArg (fun q : ℝ => c y * q) (hsum y r), Finset.mul_sum]
      _ = ∑ w ∈ W r,
          ∑ y ∈ Fintype.piFinset Y,
            c y * (if w ∈ A y r then g y r w else 0) := Finset.sum_comm
      _ = ∑ w ∈ W r, Collision.spatialRenewal σ r (w - z) *
          ∏ i : Fin 2, pairTwoFutureTerminalCellFactor N (n - s - r) φ x w i := by
        apply Finset.sum_congr rfl
        intro w hw
        have hfactor := pairTwoFutureTerminalCellFactorization N (n - s - r) φ x w
        have hfactor' :
            (∑ y ∈ Fintype.piFinset Y,
              c y * (if w ∈ A y r then
                srwKernel (n - s - r) (y 0 - w) * srwKernel (n - s - r) (y 1 - w)
              else 0)) =
              ∏ i : Fin 2, pairTwoFutureTerminalCellFactor N (n - s - r) φ x w i := by
          simpa [Y, A, c, Finset.mem_inter] using hfactor
        calc
          _ = Collision.spatialRenewal σ r (w - z) *
              (∑ y ∈ Fintype.piFinset Y,
                c y * (if w ∈ A y r then
                  srwKernel (n - s - r) (y 0 - w) * srwKernel (n - s - r) (y 1 - w)
                else 0)) := by
              calc
                _ = ∑ y ∈ Fintype.piFinset Y,
                    Collision.spatialRenewal σ r (w - z) *
                      (c y * (if w ∈ A y r then
                        srwKernel (n - s - r) (y 0 - w) *
                          srwKernel (n - s - r) (y 1 - w) else 0)) := by
                  apply Finset.sum_congr rfl
                  intro y hy
                  by_cases hA : w ∈ A y r
                  · simp [g, hA]
                    ring
                  · simp [hA]
                _ = _ := by rw [Finset.mul_sum]
          _ = _ := by rw [hfactor']
  calc
    _ = σ * ∑ y ∈ Fintype.piFinset Y,
          c y * ∑ r ∈ Finset.range (n - s + 1),
            ∑ w ∈ A y r, g y r w := by
      change (∑ y ∈ Fintype.piFinset Y,
          c y * (σ * ∑ r ∈ Finset.range (n - s + 1),
            ∑ w ∈ A y r, g y r w)) = _
      calc
        _ = ∑ y ∈ Fintype.piFinset Y,
              σ * (c y * ∑ r ∈ Finset.range (n - s + 1),
                ∑ w ∈ A y r, g y r w) := by
          apply Finset.sum_congr rfl
          intro y hy
          ring
        _ = _ := by rw [Finset.mul_sum]
    _ = σ * ∑ r ∈ Finset.range (n - s + 1),
          ∑ y ∈ Fintype.piFinset Y, c y * ∑ w ∈ A y r, g y r w := by
      congr 1
      calc
        _ = ∑ y ∈ Fintype.piFinset Y,
              ∑ r ∈ Finset.range (n - s + 1),
                c y * ∑ w ∈ A y r, g y r w := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [Finset.mul_sum]
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply congrArg (fun q : ℝ => σ * q)
      apply Finset.sum_congr rfl
      intro r hr
      exact hsumR r
