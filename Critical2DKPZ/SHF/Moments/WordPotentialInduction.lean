/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitDominationBlock
public import Critical2DKPZ.SHF.Moments.WordLimitDominationTimes

/-! # The potential-preserving step of the word induction -/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- For at most four replicas, an inverse-square-root time-envelope bound implies a first-block gap-potential estimate. -/
theorem exists_wordFirstBlock_gapPotential_bound_of_time_envelope
    (A : ℝ) (hA : 0 < A)
    (htime : ∀ m : ℕ, wordGapTimeEnvelope m ≤ A / Real.sqrt ((m : ℝ) + 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ {h : ℕ}, h ≤ 4 → ∀ (ρ : ℝ) (α β : CollisionPair h), α ≠ β →
      ∀ (s r n : ℕ) (x : LatticeConfiguration h),
      (∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
        wordFirstBlockKernel ρ α s r x v * wordGapPotential n (v β.1.2 - v β.1.1)) ≤
        (C / Real.sqrt ((s : ℝ) + r + 1)) *
          (srwKernel (2 * s) (x α.1.2 - x α.1.1) *
            (sigmaSq ρ * Renewal.renewalMass (fun k => sigmaSq ρ * Renewal.returnWeight k) r)) := by
  obtain ⟨D, hD, hblock⟩ := exists_wordFirstBlock_gapPotential_bound_explicit
  refine ⟨D * A, mul_pos hD hA, fun {h} hh ρ α β hαβ s r n x => ?_⟩
  have hmass : 0 ≤ srwKernel (2 * s) (x α.1.2 - x α.1.1) *
      (sigmaSq ρ * Renewal.renewalMass (fun k => sigmaSq ρ * Renewal.returnWeight k) r) := by
    rw [← sum_wordFirstBlockKernel ρ α s r x]
    exact Finset.sum_nonneg (fun v _ => wordFirstBlockKernel_nonneg ρ α s r x v)
  have ht := htime (s + r)
  simp only [Nat.cast_add] at ht
  calc
    _ ≤ (D * wordGapTimeEnvelope (s + r)) *
        (srwKernel (2 * s) (x α.1.2 - x α.1.1) *
          (sigmaSq ρ * Renewal.renewalMass (fun k => sigmaSq ρ * Renewal.returnWeight k) r)) :=
      hblock hh ρ α β hαβ s r n x
    _ ≤ (D * (A / Real.sqrt ((s : ℝ) + r + 1))) *
        (srwKernel (2 * s) (x α.1.2 - x α.1.1) *
          (sigmaSq ρ * Renewal.renewalMass (fun k => sigmaSq ρ * Renewal.returnWeight k) r)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht hD.le) hmass
    _ = _ := by ring

/-- A tail dominated by the potential remains dominated after a first
collision block, provided the next pair is smoothed by that block. -/
theorem wordTerminalTest_cons_mass_le_of_potential_step {h : ℕ}
    (N : ℕ) (ρ : ℝ) (α β : CollisionPair h) (w : List (CollisionPair h))
    (n : ℕ) (x : LatticeConfiguration h) (C A B : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (htail : ∀ L : ℕ, L ≤ n → ∀ v : LatticeConfiguration h,
      wordTerminalTest N (sigmaSq ρ) (β :: w) L v (fun _ => 1) ≤
        C * Real.sqrt (N : ℝ) * wordGapPotential L (v β.1.2 - v β.1.1))
    (hblock : ∀ s r : ℕ,
      (∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
        wordFirstBlockKernel ρ α s r x v * wordGapPotential n (v β.1.2 - v β.1.1)) ≤
        (A / Real.sqrt ((s : ℝ) + r + 1)) *
          (srwKernel (2 * s) (x α.1.2 - x α.1.1) *
            (sigmaSq ρ * Renewal.renewalMass (fun k => sigmaSq ρ * Renewal.returnWeight k) r)))
    (hrun : ∀ L : ℕ, L ≤ n → sigmaSq ρ * Renewal.renewalFunction
      (fun k => sigmaSq ρ * Renewal.returnWeight k) L ≤ B) :
    wordTerminalTest N (sigmaSq ρ) (α :: β :: w) n x (fun _ => 1) ≤
      (C * A * B) * Real.sqrt (N : ℝ) * wordGapPotential n (x α.1.2 - x α.1.1) := by
  have hcoef : 0 ≤ C * Real.sqrt (N : ℝ) := mul_nonneg hC (Real.sqrt_nonneg _)
  have hslice (s r : ℕ) :
      (∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
        wordFirstBlockKernel ρ α s r x v *
          wordTerminalTest N (sigmaSq ρ) (β :: w) (n - s - r) v (fun _ => 1)) ≤
      (C * Real.sqrt (N : ℝ)) * ((A / Real.sqrt ((s : ℝ) + r + 1)) *
        (srwKernel (2 * s) (x α.1.2 - x α.1.1) *
          (sigmaSq ρ * Renewal.renewalMass (fun k => sigmaSq ρ * Renewal.returnWeight k) r))) := by
    have hL : n - s - r ≤ n := (Nat.sub_le _ _).trans (Nat.sub_le _ _)
    have htail' (v : LatticeConfiguration h) :
        wordTerminalTest N (sigmaSq ρ) (β :: w) (n - s - r) v (fun _ => 1) ≤
          (C * Real.sqrt (N : ℝ)) * wordGapPotential n (v β.1.2 - v β.1.1) :=
      (htail (n - s - r) hL v).trans
        (mul_le_mul_of_nonneg_left (wordGapPotential_mono_time _ hL) hcoef)
    calc
      _ ≤ ∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
          wordFirstBlockKernel ρ α s r x v *
            ((C * Real.sqrt (N : ℝ)) * wordGapPotential n (v β.1.2 - v β.1.1)) :=
        Finset.sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (htail' v)
          (wordFirstBlockKernel_nonneg ρ α s r x v))
      _ = (C * Real.sqrt (N : ℝ)) *
          ∑ v ∈ collisionWordConfigurationEndpointSet (s + r) x,
            wordFirstBlockKernel ρ α s r x v * wordGapPotential n (v β.1.2 - v β.1.1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v hv
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hblock s r) hcoef
  rw [wordTerminalTest_cons_firstBlock]
  calc
    _ ≤ ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
        (C * Real.sqrt (N : ℝ)) * ((A / Real.sqrt ((s : ℝ) + r + 1)) *
          (srwKernel (2 * s) (x α.1.2 - x α.1.1) *
            (sigmaSq ρ * Renewal.renewalMass (fun k => sigmaSq ρ * Renewal.returnWeight k) r))) :=
      Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun r _ => hslice s r))
    _ = (C * A * Real.sqrt (N : ℝ)) *
        ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
          srwKernel (2 * s) (x α.1.2 - x α.1.1) *
            (sigmaSq ρ * Renewal.renewalMass (fun k => sigmaSq ρ * Renewal.returnWeight k) r) /
              Real.sqrt ((s : ℝ) + r + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ (C * A * Real.sqrt (N : ℝ)) * (B * wordGapPotential n (x α.1.2 - x α.1.1)) :=
      mul_le_mul_of_nonneg_left
        (sum_entrance_run_inv_sqrt_le_gapPotential ρ n (x α.1.2 - x α.1.1) B hrun)
        (mul_nonneg (mul_nonneg hC hA) (Real.sqrt_nonneg _))
    _ = _ := by ring

end Critical2DKPZ.SHF.Moments
