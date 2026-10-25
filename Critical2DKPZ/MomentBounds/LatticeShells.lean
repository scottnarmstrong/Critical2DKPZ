/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.SiteToPlane
import Critical2DKPZ.RandomWalk.GaussianBridge
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
# Exact counting of planar lattice shells

The elementary replacement for the sum-integral step in LZ21 Lemma A.1 uses
supremum-norm shells. The shell of positive integer radius k has exactly 8k sites.
No radial sum-integral comparison is assumed.
-/

@[expose] public section

namespace Critical2DKPZ.MomentBounds

/-- Integer coordinates identify lattice sites with the Cartesian planar lattice. -/
def siteEquivProd : Site ≃ ℤ × ℤ where
  toFun z := (z 0, z 1)
  invFun p := ![p.1, p.2]
  left_inv z := by ext i; fin_cases i <;> rfl
  right_inv p := rfl

/-- The integer supremum-norm radius. -/
def latticeRadius (z : Site) : ℕ := max (z 0).natAbs (z 1).natAbs

/-- Closed square of lattice radius k. -/
def latticeBox (k : ℕ) : Finset Site :=
  ((Finset.Icc (-(k : ℤ)) k).product (Finset.Icc (-(k : ℤ)) k)).map
    siteEquivProd.symm.toEmbedding

/-- The positive-radius shell between consecutive closed squares. -/
def latticeShell (k : ℕ) : Finset Site := latticeBox (k + 1) \ latticeBox k

/-- Membership in a lattice box is equivalent to the coordinate radius bound. -/
theorem mem_latticeBox (z : Site) (k : ℕ) :
    z ∈ latticeBox k ↔ latticeRadius z ≤ k := by
  rw [latticeBox, Finset.mem_map_equiv, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  rw [Equiv.symm_symm]
  change (-(k : ℤ) ≤ z 0 ∧ z 0 ≤ k) ∧ (-(k : ℤ) ≤ z 1 ∧ z 1 ≤ k) ↔ _
  rw [latticeRadius, max_le_iff]
  have hi (a : ℤ) : (-(k : ℤ) ≤ a ∧ a ≤ k) ↔ a.natAbs ≤ k := by
    rw [← abs_le, ← Int.natCast_natAbs, Nat.cast_le (α := ℤ)]
  rw [hi, hi]

/-- Lattice boxes increase with their radius. -/
theorem latticeBox_mono {k l : ℕ} (h : k ≤ l) : latticeBox k ⊆ latticeBox l := by
  intro z hz
  exact (mem_latticeBox z l).mpr (((mem_latticeBox z k).mp hz).trans h)

/-- A planar lattice box has the stated square cardinality. -/
theorem card_latticeBox (k : ℕ) : (latticeBox k).card = (2 * k + 1) ^ 2 := by
  rw [latticeBox, Finset.card_map, Finset.product_eq_sprod, Finset.card_product, Int.card_Icc]
  have hi : ((k : ℤ) + 1 - -(k : ℤ)).toNat = 2 * k + 1 := by omega
  rw [hi]
  ring

/-- A lattice shell consists of sites with the specified lattice radius. -/
theorem mem_latticeShell (z : Site) (k : ℕ) :
    z ∈ latticeShell k ↔ latticeRadius z = k + 1 := by
  rw [latticeShell, Finset.mem_sdiff, mem_latticeBox, mem_latticeBox]
  omega

/-- Exact shell count, including the radius-one shell. -/
theorem card_latticeShell (k : ℕ) : (latticeShell k).card = 8 * (k + 1) := by
  rw [latticeShell, Finset.card_sdiff_of_subset (latticeBox_mono (Nat.le_succ k)),
    card_latticeBox, card_latticeBox]
  have h : (2 * (k + 1) + 1) ^ 2 = (2 * k + 1) ^ 2 + 8 * (k + 1) := by ring
  change (2 * (k + 1) + 1) ^ 2 - (2 * k + 1) ^ 2 = 8 * (k + 1)
  rw [h, Nat.add_sub_cancel_left]

/-- A site has lattice radius zero exactly when it is the origin. -/
theorem latticeRadius_eq_zero_iff (z : Site) : latticeRadius z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    have h0 : (z 0).natAbs = 0 := by have h := le_max_left (z 0).natAbs (z 1).natAbs; change _ ≤ latticeRadius z at h; omega
    have h1 : (z 1).natAbs = 0 := by have h := le_max_right (z 0).natAbs (z 1).natAbs; change _ ≤ latticeRadius z at h; omega
    have he0 := Int.natAbs_eq_zero.mp h0
    have he1 := Int.natAbs_eq_zero.mp h1
    ext i
    fin_cases i <;> assumption
  · intro h
    subst z
    rfl

/-- The squared lattice radius is bounded by the squared Euclidean norm. -/
theorem latticeRadius_sq_le_norm_sq (z : Site) :
    (latticeRadius z : ℝ) ^ 2 ≤ ‖siteToPlane z‖ ^ 2 := by
  rw [Critical2DKPZ.norm_siteToPlane_sq, latticeRadius]
  rcases le_total (z 0).natAbs (z 1).natAbs with h | h
  · rw [max_eq_right h]
    have he : ((z 1).natAbs : ℝ) ^ 2 = (z 1 : ℝ) ^ 2 := by
      have hh := congrArg (fun a : ℤ => (a : ℝ)) (Int.natAbs_sq (z 1))
      simpa only [Int.cast_natCast, Nat.cast_pow, Int.cast_pow] using hh
    rw [he]
    linarith only [sq_nonneg (z 0 : ℝ)]
  · rw [max_eq_left h]
    have he : ((z 0).natAbs : ℝ) ^ 2 = (z 0 : ℝ) ^ 2 := by
      have hh := congrArg (fun a : ℤ => (a : ℝ)) (Int.natAbs_sq (z 0))
      simpa only [Int.cast_natCast, Nat.cast_pow, Int.cast_pow] using hh
    rw [he]
    linarith only [sq_nonneg (z 1 : ℝ)]

/-- Membership in a lattice shell gives a lower bound on the squared Euclidean norm. -/
theorem norm_sq_ge_of_mem_latticeShell {z : Site} {k : ℕ} (hz : z ∈ latticeShell k) :
    ((k + 1 : ℕ) : ℝ) ^ 2 ≤ ‖siteToPlane z‖ ^ 2 := by
  rw [← (mem_latticeShell z k).mp hz]
  exact latticeRadius_sq_le_norm_sq z

end Critical2DKPZ.MomentBounds
