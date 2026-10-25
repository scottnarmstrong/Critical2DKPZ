/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordEntranceWindows
public import Critical2DKPZ.SHF.Moments.SinglePairWordInitialFullHorizon
import Mathlib.Tactic

/-! # Tested entrance windows on arbitrary finite horizons -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter
open scoped CompactlySupported Topology

/-- Compact collision cutoffs in the exact word representation converge,
including the complete incoming-location average. -/
theorem tendsto_pairTwoTestedEntranceWindow_cutoff_horizon
    (ϑ T : ℝ) (hT : 0 < T) (L : ℕ → ℕ)
    (hL : Tendsto (fun N => (L N : ℝ) / N) atTop (𝓝 T))
    {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (η : C_c(ℝ × Plane, ℝ))
    (hη : ∀ p ∈ tsupport η, 0 < p.1 ∧ p.1 < T) :
    Tendsto (fun N => pairTwoTestedEntranceWindow ϑ N (L N)
      (evenCeil (N * s) + 1) (evenCeil (N * t)) φ η) atTop
      (𝓝 ((1 / 16 : ℝ) * ∫ p : Plane × Plane, pairTwoContinuumCutoffEntrance
        (ϑ - Real.eulerMascheroniConstant) T s t φ η p)) := by
  have hlim := ((integrable_and_tendsto_integral_pairTwoCutoffInitialStep_horizon
    ϑ T hT L hL hs hst φ η hη).2).const_mul (1 / 16 : ℝ)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact (pairTwoTestedEntranceWindow_eq_initialIntegral ϑ hN (L N) _ _ φ η).2.symm

/-- A tested entrance window is bounded by its macroscopic clock length,
uniformly over its horizon and every collision cutoff bounded by one. This
also controls coincident initial sites after the incoming-location average. -/
theorem eventually_pairTwoTestedEntranceWindow_le_card_horizon
    (ϑ T : ℝ) (hT : 0 < T) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ L lo hi : ℕ, (L : ℝ) ≤ T * N →
      ∀ η : ℝ × Plane → ℝ, (∀ p, |η p| ≤ 1) →
      |pairTwoTestedEntranceWindow ϑ N L lo hi φ η| ≤
        C * (((Finset.Icc lo hi).card : ℝ) / N) := by
  obtain ⟨Cs, hCs, hs⟩ := exists_cellPairTest_initialSupport_card_le (φ 0)
  obtain ⟨Cf, hCf, hf⟩ := eventually_pairTwoFutureSampleProfile_bdd_horizon ϑ T hT φ
  refine ⟨Cs * Cf, mul_nonneg hCs hCf, ?_⟩
  filter_upwards [hf, eventually_gt_atTop 0] with N hfN hN L lo hi hL η hη
  let S : Fin 2 → Finset Site := fun i =>
    ((SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset.image Prod.fst)
  let F : (Fin 2 → Site) → ℝ × Plane → ℝ :=
    fun x q => η q * pairTwoFutureSampleProfile ϑ N L φ x q
  have htest (x : Fin 2 → Site) (_hx : x ∈ Fintype.piFinset S) (q : ℝ × Plane) : |F x q| ≤ Cf := by
    dsimp only [F]
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (hη q) (hfN L hL x q) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hb := scaled_sum_piFinset_collisionEntrance_abs_le hN lo hi S Cs Cf hCf (hs N hN) F htest
  rw [pairTwoTestedEntranceWindow, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((N : ℝ)^2)⁻¹)]
  exact (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)).trans hb

end Critical2DKPZ.SHF.Moments
