/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CSZ25Green
import Critical2DKPZ.Polymer.SummableCovariance
import Critical2DKPZ.Lattice.Basic

/-! # Summability and finite-time calculus of Green energies -/

@[expose] public noncomputable section

namespace Critical2DKPZ.MomentBounds

/-- The truncated Green function is nonnegative. -/
theorem truncatedGreen_nonneg (L : ℕ) (z : Site) : 0 ≤ truncatedGreen L z :=
  Finset.sum_nonneg fun n _ => srwKernel_nonneg (2 * n) z

/-- The truncated Green function is bounded by the time horizon. -/
theorem truncatedGreen_le (L : ℕ) (z : Site) : truncatedGreen L z ≤ L := by
  calc
    _ ≤ ∑ _n ∈ Finset.Icc 1 L, (1 : ℝ) :=
      Finset.sum_le_sum fun n _ => Polymer.srwKernel_le_one (2 * n) z
    _ = _ := by simp

private theorem summable_profile_bounded_kernel (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z)
    (hsum : Summable φ) (K : Site → Site → ℝ) {C : ℝ}
    (hK : ∀ z w, 0 ≤ K z w) (hKC : ∀ z w, K z w ≤ C) :
    Summable (fun p : Site × Site => φ p.1 * K p.1 p.2 * φ p.2) := by
  apply Summable.of_nonneg_of_le
    (fun p => mul_nonneg (mul_nonneg (hφ _) (hK _ _)) (hφ _))
    (fun p => ?_) ((hsum.mul_of_nonneg hsum hφ hφ).mul_left C)
  calc
    φ p.1 * K p.1 p.2 * φ p.2 ≤ φ p.1 * C * φ p.2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hKC _ _) (hφ _)) (hφ _)
    _ = _ := by ring

/-- Absolute summability of the two-site Green energy, before either sum is taken. -/
theorem summable_greenEnergy_terms (L : ℕ) (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z)
    (hsum : Summable φ) :
    Summable (fun p : Site × Site => φ p.1 * truncatedGreen L (p.1 - p.2) * φ p.2) :=
  summable_profile_bounded_kernel φ hφ hsum (fun z w => truncatedGreen L (z - w)) (C := L)
    (fun z w => truncatedGreen_nonneg L (z - w)) (fun z w => truncatedGreen_le L (z - w))

/-- Absolute summability of the energy at a single even walk time. -/
theorem summable_evenTimeEnergy_terms (n : ℕ) (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z)
    (hsum : Summable φ) :
    Summable (fun p : Site × Site => φ p.1 * srwKernel (2 * n) (p.1 - p.2) * φ p.2) :=
  summable_profile_bounded_kernel φ hφ hsum (fun z w => srwKernel (2 * n) (z - w)) (C := 1)
    (fun z w => srwKernel_nonneg (2 * n) (z - w))
    (fun z w => Polymer.srwKernel_le_one (2 * n) (z - w))

/-- The Green energy is nonnegative. -/
theorem greenEnergy_nonneg (L : ℕ) (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z) :
    0 ≤ greenEnergy L φ :=
  tsum_nonneg fun z => tsum_nonneg fun w =>
    mul_nonneg (mul_nonneg (hφ z) (truncatedGreen_nonneg _ _)) (hφ w)

/-- Green energy increases with the time horizon. -/
theorem greenEnergy_mono {M L : ℕ} (hML : M ≤ L) (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z)
    (hsum : Summable φ) :
    greenEnergy M φ ≤ greenEnergy L φ := by
  have hM := summable_greenEnergy_terms M φ hφ hsum
  have hL := summable_greenEnergy_terms L φ hφ hsum
  apply hM.prod.tsum_le_tsum _ hL.prod
  intro z
  apply (hM.prod_factor z).tsum_le_tsum _ (hL.prod_factor z)
  intro w
  apply mul_le_mul_of_nonneg_right _ (hφ w)
  apply mul_le_mul_of_nonneg_left _ (hφ z)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hML)
    (fun n _ _ => srwKernel_nonneg _ _)

/-- The Green energy is the finite sum of the even-time energies. -/
theorem greenEnergy_eq_sum (L : ℕ) (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z)
    (hsum : Summable φ) :
    greenEnergy L φ = ∑ n ∈ Finset.Icc 1 L, ∑' z, ∑' w,
      φ z * srwKernel (2 * n) (z - w) * φ w := by
  unfold greenEnergy truncatedGreen
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  have hinner (z : Site) : (∑' w, ∑ n ∈ Finset.Icc 1 L,
      φ z * srwKernel (2 * n) (z - w) * φ w) =
      ∑ n ∈ Finset.Icc 1 L, ∑' w, φ z * srwKernel (2 * n) (z - w) * φ w :=
    Summable.tsum_finsetSum (fun n _ => (summable_evenTimeEnergy_terms n φ hφ hsum).prod_factor z)
  simp_rw [hinner]
  exact Summable.tsum_finsetSum (fun n _ => (summable_evenTimeEnergy_terms n φ hφ hsum).prod)

end Critical2DKPZ.MomentBounds
