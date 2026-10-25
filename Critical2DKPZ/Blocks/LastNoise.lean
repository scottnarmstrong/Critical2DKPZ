/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.ArrivalKernel
import Mathlib.Tactic

/-! # Pathwise last-noise expansion for terminal profiles -/

@[expose] public noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.Blocks

/-- The contribution whose last selected noise time is `a + r + 1`. -/
def lastNoiseTerm (β : ℝ) (a n r : ℕ) (w : Site) (f : Site → ℝ)
    (ω : Disorder) : ℝ :=
  ∑' x, preTerminalKernel β a r w x ω * Polymer.xi β (a + r + 1, x) ω *
    Collision.terminalWalkMean (n - (r + 1)) x f

private theorem lastNoiseTerm_heatStep (β : ℝ) (a n r : ℕ)
    (w : Site) (f : Site → ℝ) (ω : Disorder) :
    lastNoiseTerm β a (n + 1) (r + 1) w f ω =
      ∑ i : Fin 4, (4 : ℝ)⁻¹ * Polymer.boltzmann β (a + 1, w + srwStep i) ω *
        lastNoiseTerm β (a + 1) n r (w + srwStep i) f ω := by
  have htime : a + (r + 1) + 1 = a + 1 + r + 1 := by omega
  have hgap : n + 1 - (r + 1 + 1) = n - (r + 1) := by omega
  let F : Site → ℝ := fun x => Polymer.xi β (a + 1 + r + 1, x) ω *
    Collision.terminalWalkMean (n - (r + 1)) x f
  have hs (i : Fin 4) (_ : i ∈ Finset.univ) : Summable (fun x : Site =>
      ((4 : ℝ)⁻¹ * Polymer.boltzmann β (a + 1, w + srwStep i) ω *
        preTerminalKernel β (a + 1) r (w + srwStep i) x ω) * F x) := by
    apply summable_of_ne_finset_zero (s := Polymer.endpoints (w + srwStep i) (r + 1))
    intro x hx
    rw [preTerminalKernel_eq_zero_of_not_mem β (a + 1) r (w + srwStep i) x ω hx,
      mul_zero, zero_mul]
  simp only [lastNoiseTerm, htime, hgap, mul_assoc]
  change (∑' x, preTerminalKernel β a (r + 1) w x ω * F x) =
    ∑ i : Fin 4, (4 : ℝ)⁻¹ * (Polymer.boltzmann β (a + 1, w + srwStep i) ω *
      ∑' x, preTerminalKernel β (a + 1) r (w + srwStep i) x ω * F x)
  simp_rw [preTerminalKernel_succ, Finset.sum_mul]
  rw [Summable.tsum_finsetSum hs]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_assoc, tsum_mul_left]

private theorem lastNoiseTerm_zero (β : ℝ) (a n : ℕ) (w : Site)
    (f : Site → ℝ) (ω : Disorder) :
    lastNoiseTerm β a (n + 1) 0 w f ω =
      ∑ i : Fin 4, (4 : ℝ)⁻¹ *
        (Polymer.xi β (a + 1, w + srwStep i) ω *
          Collision.terminalWalkMean n (w + srwStep i) f) := by
  simp only [lastNoiseTerm, preTerminalKernel_zero, Nat.add_zero,
    Nat.add_sub_cancel, mul_assoc]
  change Collision.terminalWalkMean 1 w (fun x =>
    Polymer.xi β (a + 1, x) ω * Collision.terminalWalkMean n x f) = _
  rw [show (1 : ℕ) = 0 + 1 from rfl, Collision.terminalWalkMean_succ]
  simp only [Collision.terminalWalkMean_zero]

/-- The terminal polymer pairing is its walk mean plus a sum indexed by the last selected disorder time. -/
theorem terminalProfile_lastNoise (β : ℝ) (a n : ℕ) (w : Site)
    (f : Site → ℝ) (ω : Disorder) :
    (∑' z, pointToPoint β a n w z ω * f z) =
      Collision.terminalWalkMean n w f +
        ∑ r : Fin n, lastNoiseTerm β a n r.val w f ω := by
  induction n generalizing a w with
  | zero =>
    simp [Polymer.pointToPoint_zero, Collision.terminalWalkMean_zero]
  | succ n ih =>
    have hfree : (∑ i : Fin 4, (4 : ℝ)⁻¹ *
        Polymer.boltzmann β (a + 1, w + srwStep i) ω *
          Collision.terminalWalkMean n (w + srwStep i) f) =
        Collision.terminalWalkMean (n + 1) w f + lastNoiseTerm β a (n + 1) 0 w f ω := by
      rw [Collision.terminalWalkMean_succ, lastNoiseTerm_zero, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      unfold Polymer.boltzmann Polymer.xi
      ring
    rw [Polymer.terminalProfile_succ]
    have hfun (i : Fin 4) := ih (a + 1) (w + srwStep i)
    simp_rw [hfun, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    unfold Polymer.boltzmann at hfree
    rw [hfree, Finset.sum_comm, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ]
    have hterms : (∑ r : Fin n, ∑ i : Fin 4,
        (4 : ℝ)⁻¹ * Polymer.boltzmann β (a + 1, w + srwStep i) ω *
          lastNoiseTerm β (a + 1) n r.val (w + srwStep i) f ω) =
        ∑ r : Fin n, lastNoiseTerm β a (n + 1) (r.val + 1) w f ω := by
      apply Finset.sum_congr rfl
      intro r _
      exact (lastNoiseTerm_heatStep β a n r.val w f ω).symm
    unfold Polymer.boltzmann at hterms
    rw [hterms]
    ring

end Critical2DKPZ.Blocks
