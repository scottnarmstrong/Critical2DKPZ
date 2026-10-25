/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordEntranceBoundary
public import Critical2DKPZ.SHF.Moments.SinglePairWordEntranceSpatialTail
import Mathlib.Tactic

/-! # Uniform discrete space-time cutoff errors for two-particle entrances -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open Filter
open scoped CompactlySupported

/-- A tested entrance window depends only on the cutoff values on its clocks. -/
theorem pairTwoTestedEntranceWindow_congr_on_clocks
    (ϑ : ℝ) (N L lo hi : ℕ) (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (η ξ : ℝ × Plane → ℝ)
    (h : ∀ r ∈ Finset.Icc lo hi, ∀ z : Plane, η ((r : ℝ) / N, z) = ξ ((r : ℝ) / N, z)) :
    pairTwoTestedEntranceWindow ϑ N L lo hi φ η =
      pairTwoTestedEntranceWindow ϑ N L lo hi φ ξ := by
  unfold pairTwoTestedEntranceWindow
  congr 1
  apply Finset.sum_congr rfl
  intro x _hx
  unfold collisionEntrance
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  funext z
  dsimp only
  rw [h r hr]

/-- An interior plateau leaves only the two short clock strips and the
spatial tail. Every constant is uniform in the microscopic clocks and the
cutoff function. -/
theorem eventually_pairTwoTestedEntranceWindow_cutoff_error
    (ϑ T : ℝ) (hT : 0 < T) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) :
    ∃ C D R₀ : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ 0 < R₀ ∧ ∀ᶠ N : ℕ in atTop,
      ∀ L lo A B hi : ℕ, lo ≤ A → A < B → B < hi →
      (L : ℝ) ≤ T * N → (hi : ℝ) ≤ T * N →
      ∀ R : ℝ, R₀ ≤ R → ∀ η : ℝ × Plane → ℝ,
      (∀ p, η p ∈ Set.Icc (0 : ℝ) 1) →
      (∀ r ∈ Finset.Icc (A + 1) B, ∀ z : Plane, ‖z‖ ≤ R → η ((r : ℝ) / N, z) = 1) →
      |pairTwoTestedEntranceWindow ϑ N L lo hi φ (fun _ => 1) -
        pairTwoTestedEntranceWindow ϑ N L lo hi φ η| ≤
          C * (((Finset.Icc lo A).card : ℝ) / N + ((Finset.Icc (B + 1) hi).card : ℝ) / N) + D / R := by
  classical
  obtain ⟨C, hC, hb⟩ := eventually_pairTwoTestedEntranceWindow_le_card_horizon ϑ T hT φ
  obtain ⟨D, R₀, hD, hR₀, htail⟩ :=
    eventually_pairTwoTestedEntranceWindow_spatialTail_le ϑ T hT φ
  refine ⟨C, D, R₀, hC, hD, hR₀, ?_⟩
  filter_upwards [hb, htail] with N hbN htN L lo A B hi hlo hAB hBhi hL hhi R hR η hη hone
  let f : ℝ × Plane → ℝ := fun p => 1 - η p
  have hf (p : ℝ × Plane) : |f p| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hη p).2)]
    exact sub_le_self 1 (hη p).1
  let ξ : ℝ × Plane → ℝ := fun p =>
    if ∃ r ∈ Finset.Icc (A + 1) B, p.1 = (r : ℝ) / N then f p else 0
  have hξ (p : ℝ × Plane) : |ξ p| ≤ 1 := by
    dsimp only [ξ]
    split_ifs
    · exact hf p
    · norm_num
  have hzero (u : ℝ) (z : Plane) (hz : ‖z‖ ≤ R) : ξ (u, z) = 0 := by
    dsimp only [ξ]
    split_ifs with h
    · obtain ⟨r, hr, hur⟩ := h
      dsimp only [f]
      rw [hur, hone r hr z hz, sub_self]
    · rfl
  have heq : pairTwoTestedEntranceWindow ϑ N L (A + 1) B φ f =
      pairTwoTestedEntranceWindow ϑ N L (A + 1) B φ ξ := by
    apply pairTwoTestedEntranceWindow_congr_on_clocks
    intro r hr z
    dsimp only [ξ]
    rw [ite_eq_left ⟨r, hr, rfl⟩]
  have hmiddle := htN L (A + 1) B hL
    ((by exact_mod_cast hBhi.le : (B : ℝ) ≤ hi).trans hhi) R hR ξ hξ hzero
  rw [← heq] at hmiddle
  have hleft := hbN L lo A hL f hf
  have hright := hbN L (B + 1) hi hL f hf
  rw [← pairTwoTestedEntranceWindow_sub_cutoff]
  change |pairTwoTestedEntranceWindow ϑ N L lo hi φ f| ≤ _
  rw [pairTwoTestedEntranceWindow_split ϑ N L lo A hi hlo (hAB.trans hBhi),
    pairTwoTestedEntranceWindow_split ϑ N L (A + 1) B hi hAB hBhi]
  calc
    _ ≤ |pairTwoTestedEntranceWindow ϑ N L lo A φ f| +
        (|pairTwoTestedEntranceWindow ϑ N L (A + 1) B φ f| +
          |pairTwoTestedEntranceWindow ϑ N L (B + 1) hi φ f|) :=
      (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))
    _ ≤ C * (((Finset.Icc lo A).card : ℝ) / N) +
        (D / R + C * (((Finset.Icc (B + 1) hi).card : ℝ) / N)) :=
      add_le_add hleft (add_le_add hmiddle hright)
    _ = _ := by ring

end Critical2DKPZ.SHF.Moments
