/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.Core
public import Critical2DKPZ.Polymer.Chaos
public import Critical2DKPZ.Collision.WeightedTerminal
import Mathlib.Tactic

/-! # Pathwise first-noise expansion of polymer kernels -/

@[expose] public noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.Blocks

/-- The term with its first selected disorder coordinate at relative time `r`. -/
def firstNoiseTerm (β : ℝ) (a n r : ℕ) (w : Site) (f : Site → ℝ)
    (ω : Disorder) : ℝ :=
  Collision.terminalWalkMean r w (fun x => Polymer.xi β (a + r, x) ω *
    ∑' z, pointToPoint β (a + r) (n - r) x z ω * f z)

private theorem firstNoiseTerm_heatStep (β : ℝ) (a n r : ℕ)
    (w : Site) (f : Site → ℝ) (ω : Disorder) :
    firstNoiseTerm β a (n + 1) (r + 1) w f ω =
      ∑ i : Fin 4, (4 : ℝ)⁻¹ * firstNoiseTerm β (a + 1) n r (w + srwStep i) f ω := by
  unfold firstNoiseTerm
  rw [Collision.terminalWalkMean_succ]
  have htime : a + (r + 1) = a + 1 + r := by omega
  simp only [htime, Nat.add_sub_add_right]

private theorem firstNoiseTerm_one (β : ℝ) (a n : ℕ) (w : Site)
    (f : Site → ℝ) (ω : Disorder) :
    firstNoiseTerm β a (n + 1) 1 w f ω =
      ∑ i : Fin 4, (4 : ℝ)⁻¹ *
        (Polymer.xi β (a + 1, w + srwStep i) ω *
          ∑' z, pointToPoint β (a + 1) n (w + srwStep i) z ω * f z) := by
  unfold firstNoiseTerm
  rw [show (1 : ℕ) = 0 + 1 from rfl, Collision.terminalWalkMean_succ]
  simp only [Collision.terminalWalkMean_zero, Nat.add_sub_cancel]

/-- The terminal polymer pairing is its walk mean plus a sum indexed by the first selected disorder time. -/
theorem terminalProfile_firstNoise (β : ℝ) (a n : ℕ) (w : Site)
    (f : Site → ℝ) (ω : Disorder) :
    (∑' z, pointToPoint β a n w z ω * f z) =
      Collision.terminalWalkMean n w f +
        ∑ r ∈ Finset.Icc 1 n, firstNoiseTerm β a n r w f ω := by
  induction n generalizing a w with
  | zero =>
    simp [Polymer.pointToPoint_zero, Collision.terminalWalkMean_zero]
  | succ n ih =>
    have hsplit : (∑' z, pointToPoint β a (n + 1) w z ω * f z) =
        (∑ i : Fin 4, (4 : ℝ)⁻¹ *
          (∑' z, pointToPoint β (a + 1) n (w + srwStep i) z ω * f z)) +
        firstNoiseTerm β a (n + 1) 1 w f ω := by
      rw [Polymer.terminalProfile_succ, firstNoiseTerm_one, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      unfold Polymer.xi
      ring
    have hprop : (∑ i : Fin 4, (4 : ℝ)⁻¹ *
        (∑' z, pointToPoint β (a + 1) n (w + srwStep i) z ω * f z)) =
        Collision.terminalWalkMean (n + 1) w f +
          ∑ r ∈ Finset.Icc 1 n, firstNoiseTerm β a (n + 1) (r + 1) w f ω := by
      simp_rw [ih, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      rw [← Collision.terminalWalkMean_succ, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      exact (firstNoiseTerm_heatStep β a n r w f ω).symm
    rw [hsplit, hprop, Polymer.sum_Icc_first]
    ring

/-- First-noise expansion with a fixed terminal endpoint. -/
theorem pointToPoint_firstNoise (β : ℝ) (a n : ℕ) (w y : Site) (ω : Disorder) :
    pointToPoint β a n w y ω = srwKernel n (y - w) +
      ∑ r ∈ Finset.Icc 1 n, ∑' x,
        srwKernel r (x - w) * Polymer.xi β (a + r, x) ω *
          pointToPoint β (a + r) (n - r) x y ω := by
  have h := terminalProfile_firstNoise β a n w
    (fun z => if z = y then 1 else 0) ω
  simpa only [firstNoiseTerm, Collision.terminalWalkMean, mul_ite, mul_one,
    mul_zero, tsum_ite_eq, mul_assoc] using h


/-- The terminal walk mean is the uniform average over all nearest neighbor step sequences. -/
theorem terminalWalkMean_walkSum (n : ℕ) (w : Site) (f : Site → ℝ) :
    Collision.terminalWalkMean n w f =
      ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n * f (walkPosition w s n) := by
  have h := Polymer.tsum_pointToPoint_mul 0 0 n w f (fun _ => 0)
  simpa only [Polymer.pointToPoint_zero_beta, Polymer.pathWeight_zero_beta,
    mul_one, Collision.terminalWalkMean] using h



/-- The deterministic walk means compose across time. -/
theorem terminalWalkMean_comp (n m : ℕ) (w : Site) (f : Site → ℝ) :
    Collision.terminalWalkMean (n + m) w f =
      Collision.terminalWalkMean n w (fun y => Collision.terminalWalkMean m y f) := by
  have h := Polymer.terminalProfile_chapmanKolmogorov 0 0 n m w f (fun _ => 0)
  simpa only [Polymer.pointToPoint_zero_beta, Collision.terminalWalkMean] using h


/-- Terminal walk averaging preserves subtraction. -/
theorem terminalWalkMean_sub (n : ℕ) (w : Site) (f g : Site → ℝ) :
    Collision.terminalWalkMean n w (fun x => f x - g x) =
      Collision.terminalWalkMean n w f - Collision.terminalWalkMean n w g := by
  simp only [terminalWalkMean_walkSum, mul_sub, Finset.sum_sub_distrib]



end Critical2DKPZ.Blocks
