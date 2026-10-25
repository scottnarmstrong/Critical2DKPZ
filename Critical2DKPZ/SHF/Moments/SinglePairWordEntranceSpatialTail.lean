/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.EntranceSpatialTailWindow
public import Critical2DKPZ.SHF.Moments.SinglePairWordEntranceWindowsHorizon
import Mathlib.Tactic

/-! # Spatial-cutoff errors in the tested two-particle entrance formula -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter
open scoped CompactlySupported Topology

private theorem entrance_clock_ratio_upper {N K : ℕ} (hN : 0 < N) {T : ℝ}
    (hK : (K : ℝ) ≤ T * N) : ((K : ℝ) + 1) / N ≤ T + 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  apply (div_le_iff₀ hNr).mpr
  linarith only [hK, hNr1]

private theorem entrance_clock_sqrt_upper {N K : ℕ} (hN : 0 < N) {T : ℝ}
    (hK : (K : ℝ) ≤ T * N) :
    (Real.sqrt ((N : ℝ) / 2))⁻¹ * Real.sqrt ((K : ℝ) + 1) ≤ Real.sqrt (2 * (T + 1)) := by
  rw [← Real.sqrt_inv, inv_div, ← Real.sqrt_mul (by positivity : 0 ≤ 2 / (N : ℝ))]
  apply Real.sqrt_le_sqrt
  calc
    2 / (N : ℝ) * ((K : ℝ) + 1) = 2 * (((K : ℝ) + 1) / N) := by ring
    _ ≤ 2 * (T + 1) := mul_le_mul_of_nonneg_left (entrance_clock_ratio_upper hN hK) (by norm_num)

private theorem normalized_card_product_le {n a b C D B : ℝ}
    (hn : 0 < n) (hb : 0 ≤ b) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (haC : a ≤ C * n) (hbD : b ≤ D * n) :
    (n^2)⁻¹ * (a * b * B) ≤ C * D * B := by
  have hab := mul_le_mul haC hbD hb (mul_nonneg hC hn.le)
  calc
    _ ≤ (n^2)⁻¹ * ((C * n) * (D * n) * B) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hab hB) (by positivity)
    _ = C * D * B := by field_simp

/-- Spatial collision cutoffs have an `O(1/R)` tested-word error uniformly over bounded horizons, microscopic clocks and admissible cutoffs. Initial averaging includes coincident starting sites. -/
theorem eventually_pairTwoTestedEntranceWindow_spatialTail_le
    (ϑ T : ℝ) (hT : 0 < T) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) :
    ∃ C R₀ : ℝ, 0 ≤ C ∧ 0 < R₀ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ L lo hi : ℕ, (L : ℝ) ≤ T * N → (hi : ℝ) ≤ T * N →
      ∀ R : ℝ, R₀ ≤ R → ∀ η : ℝ × Plane → ℝ,
      (∀ p, |η p| ≤ 1) → (∀ u z, ‖z‖ ≤ R → η (u, z) = 0) →
        |pairTwoTestedEntranceWindow ϑ N L lo hi φ η| ≤ C / R := by
  obtain ⟨Cr, Cm, hCr, hCm, htail⟩ := collisionEntrance_spatialTail_window_le
  obtain ⟨_M, Rbase, _hM, hRbase, _hφ, hφR⟩ := exists_collisionWord_compactTest_bounds φ
  obtain ⟨Cs₀, hCs₀, hs₀⟩ := exists_cellPairTest_initialSupport_card_le (φ 0)
  obtain ⟨Cs₁, hCs₁, hs₁⟩ := exists_cellPairTest_initialSupport_card_le (φ 1)
  obtain ⟨Cf, hCf, hf⟩ := eventually_pairTwoFutureSampleProfile_bdd_horizon ϑ T hT φ
  let Q : ℝ := Cr * (T + 1) + 2 * Cm * Real.sqrt (2 * (T + 1))
  let Cp : ℝ := 2 * Cf * Q
  let C : ℝ := Cs₀ * Cs₁ * Cp
  let R₀ : ℝ := 2 * (Rbase + 2)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hCp : 0 ≤ Cp := mul_nonneg (mul_nonneg (by norm_num) hCf) hQ
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg hCs₀ hCs₁) hCp
  have hR₀ : 0 < R₀ := by dsimp [R₀]; positivity
  refine ⟨C, R₀, hC, hR₀, ?_⟩
  filter_upwards [hf, eventually_gt_atTop 0] with N hfN hN L lo hi hL hhi R hR η hη hzero
  have hRpos : 0 < R := hR₀.trans_le hR
  let S : Fin 2 → Finset Site := fun i =>
    ((SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset.image Prod.fst)
  let F : (Fin 2 → Site) → ℝ × Plane → ℝ :=
    fun x q => η q * pairTwoFutureSampleProfile ϑ N L φ x q
  have hpoint (x : Fin 2 → Site) (hx : x ∈ Fintype.piFinset S) :
      |collisionEntrance N lo hi (x 0) (x 1) (F x)| ≤ Cp / R := by
    have hstart (i : Fin 2) : ‖latticeRepresentative N (x i)‖ ≤ R / 2 := by
      have hb := cellPairTest_initialSupport_scaledNorm_le hN (φ i) (hφR i)
        ((Fintype.mem_piFinset.mp hx) i)
      have hR' : 2 * (Rbase + 2) ≤ R := hR
      linarith only [hb, hR']
    have hF (u : ℝ) (z : Plane) : |F x (u, z)| ≤ Cf := by
      dsimp only [F]
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul (hη (u, z)) (hfN L hL x (u, z))
        (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have hFzero (u : ℝ) (z : Plane) (hz : ‖z‖ ≤ R) : F x (u, z) = 0 := by
      dsimp only [F]
      rw [hzero u z hz, zero_mul]
    have he := htail N lo hi hN (x 0) (x 1) R Cf hRpos hCf (hstart 0) (hstart 1) (F x) hF hFzero
    have hratio := entrance_clock_ratio_upper hN hhi
    have hroot := entrance_clock_sqrt_upper hN hhi
    have htime : Cr * (((hi : ℝ) + 1) / N) +
        2 * Cm * (Real.sqrt ((N : ℝ) / 2))⁻¹ * Real.sqrt ((hi : ℝ) + 1) ≤ Q := by
      dsimp only [Q]
      calc
        _ = Cr * (((hi : ℝ) + 1) / N) +
            (2 * Cm) * ((Real.sqrt ((N : ℝ) / 2))⁻¹ * Real.sqrt ((hi : ℝ) + 1)) := by ring
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hratio hCr.le)
          (mul_le_mul_of_nonneg_left hroot (by positivity))
    calc
      _ ≤ (2 * Cf / R) * Q := he.trans (mul_le_mul_of_nonneg_left htime (by positivity))
      _ = Cp / R := by dsimp only [Cp]; ring
  have hsum : (∑ x ∈ Fintype.piFinset S, |collisionEntrance N lo hi (x 0) (x 1) (F x)|) ≤
      ((S 0).card : ℝ) * (S 1).card * (Cp / R) := by
    calc
      _ ≤ ∑ _x ∈ Fintype.piFinset S, Cp / R := Finset.sum_le_sum hpoint
      _ = _ := by
        rw [sum_initialConfigurations_eq_double]
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  rw [pairTwoTestedEntranceWindow, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((N : ℝ)^2)⁻¹)]
  calc
    _ ≤ ((N : ℝ)^2)⁻¹ * ∑ x ∈ Fintype.piFinset S,
        |collisionEntrance N lo hi (x 0) (x 1) (F x)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ ((N : ℝ)^2)⁻¹ * (((S 0).card : ℝ) * (S 1).card * (Cp / R)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ Cs₀ * Cs₁ * (Cp / R) := normalized_card_product_le
      (by exact_mod_cast hN) (Nat.cast_nonneg _) hCs₀
      (div_nonneg hCp hRpos.le) (hs₀ N hN) (hs₁ N hN)
    _ = C / R := by dsimp only [C]; ring

end Critical2DKPZ.SHF.Moments
