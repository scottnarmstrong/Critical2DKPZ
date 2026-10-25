/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.ProfileBoxes

/-! # Concentration of probability profiles in finite lattice boxes -/

@[expose] public noncomputable section

namespace Critical2DKPZ.MomentBounds

private theorem mass_finset_ge_of_tail_majorant (φ g : Site → ℝ) (hmass : HasSum φ 1)
    (A : Finset Site) (hg : ∀ z, 0 ≤ g z) (hgs : Summable g)
    (htail : ∀ z ∉ A, φ z ≤ g z) : 1 - (∑' z, g z) ≤ ∑ z ∈ A, φ z := by
  let f : Site → ℝ := fun z => if z ∈ A then φ z else 0
  have hfs : Summable f := summable_of_ne_finset_zero (s := A) (fun z hz => by simp only [f, ite_eq_right hz])
  have hf : (∑' z, f z) = ∑ z ∈ A, φ z := by
    rw [tsum_eq_sum (s := A) (fun z hz => by simp only [f, ite_eq_right hz])]
    exact Finset.sum_congr rfl (fun z hz => by simp only [f, ite_eq_left hz])
  have hle : ∀ z, φ z ≤ f z + g z := by
    intro z
    by_cases hz : z ∈ A
    · simpa only [f, ite_eq_left hz] using le_add_of_nonneg_right (hg z)
    · simpa only [f, ite_eq_right hz, zero_add] using htail z hz
  have h := hmass.summable.tsum_le_tsum hle (hfs.add hgs)
  rw [hmass.tsum_eq, hfs.tsum_add hgs, hf] at h
  linarith only [h]

/-- Exponential Markov bound in a box with a cardinality independent of the centre. -/
theorem profileBox_mass_ge_exponential (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z)
    (hmass : HasSum φ 1) (x : Plane) {a R C : ℝ} (ha : 0 ≤ a)
    (hs : Summable (fun z => φ z * Real.exp (a * ‖siteToPlane z - x‖)))
    (hC : (∑' z, φ z * Real.exp (a * ‖siteToPlane z - x‖)) ≤ C) :
    1 - Real.exp (-a * R) * C ≤ ∑ z ∈ profileBox x R, φ z := by
  let g : Site → ℝ := fun z => Real.exp (-a * R) * (φ z * Real.exp (a * ‖siteToPlane z - x‖))
  have hg : ∀ z, 0 ≤ g z := fun z => mul_nonneg (Real.exp_pos _).le (mul_nonneg (hφ z) (Real.exp_pos _).le)
  have hgs : Summable g := hs.mul_left _
  have htail : ∀ z ∉ profileBox x R, φ z ≤ g z := by
    intro z hz
    have hd : R ≤ ‖siteToPlane z - x‖ := le_of_lt (lt_of_not_ge (fun h => hz (mem_profileBox_of_norm_le h)))
    have hex : 1 ≤ Real.exp (-a * R) * Real.exp (a * ‖siteToPlane z - x‖) := by
      rw [← Real.exp_add, show -a * R + a * ‖siteToPlane z - x‖ = a * (‖siteToPlane z - x‖ - R) by ring]
      exact Real.one_le_exp_iff.2 (mul_nonneg ha (sub_nonneg.2 hd))
    calc
      φ z ≤ φ z * (Real.exp (-a * R) * Real.exp (a * ‖siteToPlane z - x‖)) :=
        le_mul_of_one_le_right (hφ z) hex
      _ = _ := by dsimp [g]; ring
  have h := mass_finset_ge_of_tail_majorant φ g hmass _ hg hgs htail
  have hsumg : (∑' z, g z) ≤ Real.exp (-a * R) * C := by
    rw [show (∑' z, g z) = Real.exp (-a * R) * (∑' z, φ z * Real.exp (a * ‖siteToPlane z - x‖)) from tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hC (Real.exp_pos _).le
  linarith only [h, hsumg]

/-- Quadratic Markov bound for the same boxes. -/
theorem profileBox_mass_ge_quadratic (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z)
    (hmass : HasSum φ 1) (x : Plane) {R D : ℝ} (hR : 0 < R)
    (hs : Summable (fun z => ‖siteToPlane z - x‖ ^ 2 * φ z))
    (hD : (∑' z, ‖siteToPlane z - x‖ ^ 2 * φ z) ≤ D) :
    1 - D / R ^ 2 ≤ ∑ z ∈ profileBox x R, φ z := by
  let g : Site → ℝ := fun z => (‖siteToPlane z - x‖ ^ 2 * φ z) / R ^ 2
  have hg : ∀ z, 0 ≤ g z := fun z => div_nonneg (mul_nonneg (sq_nonneg _) (hφ z)) (sq_nonneg _)
  have hgs : Summable g := hs.div_const _
  have htail : ∀ z ∉ profileBox x R, φ z ≤ g z := by
    intro z hz
    have hd : R ≤ ‖siteToPlane z - x‖ := le_of_lt (lt_of_not_ge (fun h => hz (mem_profileBox_of_norm_le h)))
    apply (le_div_iff₀ (sq_pos_of_pos hR)).2
    exact (mul_comm _ _).trans_le (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hR.le hd 2) (hφ z))
  have h := mass_finset_ge_of_tail_majorant φ g hmass _ hg hgs htail
  have hsumg : (∑' z, g z) ≤ D / R ^ 2 := by
    rw [show (∑' z, g z) = (∑' z, ‖siteToPlane z - x‖ ^ 2 * φ z) / R ^ 2 from tsum_div_const]
    exact div_le_div_of_nonneg_right hD (sq_nonneg _)
  linarith only [h, hsumg]

end Critical2DKPZ.MomentBounds
