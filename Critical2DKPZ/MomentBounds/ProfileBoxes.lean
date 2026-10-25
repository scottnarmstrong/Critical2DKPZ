/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.LatticeShells
import Mathlib.Analysis.Normed.Lp.PiLp

/-! # Finite lattice boxes around real profile centres -/

@[expose] public noncomputable section

namespace Critical2DKPZ.MomentBounds

/-- The site obtained by taking the integer floor of each coordinate of a real centre. -/
def floorSite (x : Plane) : Site := fun i => ⌊x i⌋

/-- A finite box containing the Euclidean radius-`R` ball about a real centre. -/
def profileBox (x : Plane) (R : ℝ) : Finset Site :=
  (latticeBox ⌈R + 1⌉₊).image (fun z => z + floorSite x)

/-- Profile boxes increase with their radius. -/
theorem profileBox_mono (x : Plane) {R S : ℝ} (hRS : R ≤ S) :
    profileBox x R ⊆ profileBox x S :=
  Finset.image_mono (fun z => z + floorSite x)
    (latticeBox_mono (Nat.ceil_le_ceil (show R + 1 ≤ S + 1 by linarith only [hRS])))

/-- Every site within Euclidean distance `R` belongs to the finite profile box. -/
theorem mem_profileBox_of_norm_le {x : Plane} {R : ℝ} {z : Site}
    (hz : ‖siteToPlane z - x‖ ≤ R) : z ∈ profileBox x R := by
  let K := ⌈R + 1⌉₊
  have hcoord (i : Fin 2) : ((z - floorSite x) i).natAbs ≤ K := by
    have hi : |(z i : ℝ) - x i| ≤ R :=
      (PiLp.norm_apply_le (siteToPlane z - x) i).trans hz
    have hf := Int.floor_le (x i)
    have hf' := Int.lt_floor_add_one (x i)
    have hb : |(((z - floorSite x) i : ℤ) : ℝ)| ≤ (K : ℝ) := by
      have hceil : R + 1 ≤ (K : ℝ) := Nat.le_ceil _
      change |((z i - ⌊x i⌋ : ℤ) : ℝ)| ≤ _
      rw [Int.cast_sub]
      rw [abs_le]
      constructor <;> linarith only [(abs_le.1 hi).1, (abs_le.1 hi).2, hf, hf', hceil]
    have hcast : (((z - floorSite x) i).natAbs : ℝ) ≤ K := by
      rw [Nat.cast_natAbs, Int.cast_abs]
      exact hb
    exact_mod_cast hcast
  have hmem : z - floorSite x ∈ latticeBox K :=
    (mem_latticeBox _ _).2 (max_le (hcoord 0) (hcoord 1))
  exact Finset.mem_image.2 ⟨z - floorSite x, hmem, sub_add_cancel _ _⟩

/-- The cardinality bound is independent of the real centre. -/
theorem card_profileBox_le (x : Plane) (R : ℝ) :
    (profileBox x R).card ≤ (2 * ⌈R + 1⌉₊ + 1) ^ 2 := by
  exact Finset.card_image_le.trans_eq (card_latticeBox _)

/-- Sites in the box stay within a controlled Euclidean distance of its centre. -/
theorem norm_le_of_mem_profileBox {x : Plane} {R : ℝ} (hR : 0 ≤ R) {z : Site}
    (hz : z ∈ profileBox x R) : ‖siteToPlane z - x‖ ≤ 2 * (R + 3) := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hz
  let K := ⌈R + 1⌉₊
  have hvK : latticeRadius v ≤ K := (mem_latticeBox _ _).1 hv
  have hc (i : Fin 2) : |((v + floorSite x) i : ℝ) - x i| ≤ (K : ℝ) + 1 := by
    have hvi : (v i).natAbs ≤ K := by
      fin_cases i
      · exact (le_max_left _ _).trans hvK
      · exact (le_max_right _ _).trans hvK
    have hvabs : |(v i : ℝ)| ≤ (K : ℝ) := by
      rw [← Int.cast_abs, ← Nat.cast_natAbs]
      exact_mod_cast hvi
    have hf := Int.floor_le (x i)
    have hf' := Int.lt_floor_add_one (x i)
    change |((v i + ⌊x i⌋ : ℤ) : ℝ) - x i| ≤ _
    rw [Int.cast_add, abs_le]
    constructor <;> linarith only [(abs_le.1 hvabs).1, (abs_le.1 hvabs).2, hf, hf']
  have hsq (i : Fin 2) : (((v + floorSite x) i : ℝ) - x i) ^ 2 ≤ ((K : ℝ) + 1) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hc i) 2
  have hn : ‖siteToPlane (v + floorSite x) - x‖ ^ 2 =
      (((v + floorSite x) 0 : ℝ) - x 0) ^ 2 +
        (((v + floorSite x) 1 : ℝ) - x 1) ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, siteToPlane, Fin.sum_univ_two]
  have hK : (K : ℝ) ≤ R + 2 := by
    simpa only [add_assoc, one_add_one_eq_two] using
      (Nat.ceil_lt_add_one (show 0 ≤ R + 1 by linarith)).le
  have hb : ‖siteToPlane (v + floorSite x) - x‖ ≤ 2 * ((K : ℝ) + 1) := by
    nlinarith only [hsq 0, hsq 1, hn, norm_nonneg (siteToPlane (v + floorSite x) - x),
      (show (0 : ℝ) ≤ K from Nat.cast_nonneg K)]
  linarith only [hb, hK]

end Critical2DKPZ.MomentBounds
