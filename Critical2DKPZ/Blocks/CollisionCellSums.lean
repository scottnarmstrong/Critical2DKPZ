/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.CollisionSupport
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-! # Absolute and relative first-last collision cells -/

@[expose] public noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.Blocks

/-- A cell sum grouped by the absolute first and last collision times. -/
def collisionCellSum (σ2 : ℝ) (A B : ℕ) (W : ℕ → Site → ℝ) (F : ℕ → Site → ℝ) : ℝ :=
  ∑ a ∈ Finset.Ioc A B, ∑ b ∈ Finset.Icc a B, ∑' x, ∑' y,
    W a x * (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x)) * F b y

/-- The same cell coordinates in relative first time and relative collision gap. -/
def relativeCollisionCellSum (σ2 : ℝ) (A B : ℕ)
    (W : ℕ → Site → ℝ) (F : ℕ → Site → ℝ) : ℝ :=
  σ2 * ∑ s ∈ Finset.Icc 1 (B - A), ∑' x, W (A + s) x *
    (∑ r : Fin (B - A - s + 1), ∑' y,
      Collision.spatialRenewal σ2 r.val (y - x) * F (A + s + r.val) y)

private theorem sum_Ioc_relative (A B : ℕ) (F : ℕ → ℝ) :
    (∑ a ∈ Finset.Ioc A B, F a) = ∑ s ∈ Finset.Icc 1 (B - A), F (A + s) := by
  apply Finset.sum_bij (fun a _ => a - A)
  · intro a ha
    have ha' := Finset.mem_Ioc.1 ha
    apply Finset.mem_Icc.2
    omega
  · intro a ha b hb hab
    have ha' := Finset.mem_Ioc.1 ha
    have hb' := Finset.mem_Ioc.1 hb
    omega
  · intro s hs
    have hs' := Finset.mem_Icc.1 hs
    refine ⟨A + s, Finset.mem_Ioc.2 (by omega), by omega⟩
  · intro a ha
    have ha' := Finset.mem_Ioc.1 ha
    congr 1
    omega

private theorem sum_Icc_gap {a B : ℕ} (ha : a ≤ B) (F : ℕ → ℝ) :
    (∑ b ∈ Finset.Icc a B, F b) = ∑ r : Fin (B - a + 1), F (a + r.val) := by
  have hI : Finset.Icc a B = Finset.Ico a (B + 1) := by
    ext b
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hI, Finset.sum_Ico_eq_sum_range]
  have hcount : B + 1 - a = B - a + 1 := by omega
  rw [hcount, Finset.sum_range]

/-- Reindex a first-last cell using relative time and relative gap.
The spatial support hypothesis permits commuting the finite gap sum with the walk-site sum. -/
theorem collisionCellSum_eq_relative (σ2 : ℝ) (A B : ℕ)
    (W : ℕ → Site → ℝ) (F : ℕ → Site → ℝ) (S : ℕ → Finset Site)
    (hW : ∀ a x, x ∉ S a → W a x = 0) :
    collisionCellSum σ2 A B W F = relativeCollisionCellSum σ2 A B W F := by
  unfold collisionCellSum relativeCollisionCellSum
  rw [sum_Ioc_relative, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hs' := Finset.mem_Icc.1 hs
  have has : A + s ≤ B := by omega
  rw [sum_Icc_gap has]
  rw [show B - (A + s) + 1 = B - A - s + 1 by omega]
  simp only [Nat.add_sub_cancel_left]
  have hsumm (r : Fin (B - A - s + 1)) (_ : r ∈ Finset.univ) :
      Summable (fun x : Site => ∑' y,
        W (A + s) x * (σ2 * Collision.spatialRenewal σ2 r.val (y - x)) *
          F (A + s + r.val) y) := by
    apply summable_of_ne_finset_zero (s := S (A + s))
    intro x hx
    simp only [hW (A + s) x hx, zero_mul, tsum_zero]
  rw [← Summable.tsum_finsetSum (s := Finset.univ)
    (f := fun (r : Fin (B - A - s + 1)) (x : Site) => ∑' y,
      W (A + s) x * (σ2 * Collision.spatialRenewal σ2 r.val (y - x)) *
        F (A + s + r.val) y) hsumm]
  calc
    _ = ∑' x, σ2 * (W (A + s) x *
        (∑ r : Fin (B - A - s + 1), ∑' y,
          Collision.spatialRenewal σ2 r.val (y - x) * F (A + s + r.val) y)) := by
      apply tsum_congr
      intro x
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [← tsum_mul_left (a := W (A + s) x), ← tsum_mul_left (a := σ2)]
      apply tsum_congr
      intro y
      ring
    _ = _ := tsum_mul_left

end Critical2DKPZ.Blocks
