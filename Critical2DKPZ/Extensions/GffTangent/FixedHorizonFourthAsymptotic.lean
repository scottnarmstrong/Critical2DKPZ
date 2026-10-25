/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonFourthScaled
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonFourthProfileCost
import Mathlib.Tactic

/-! # Sharp fourth moments on moving macroscopic windows -/

@[expose] public noncomputable section

open MeasureTheory Filter Critical2DKPZ.MomentBounds
open scoped BigOperators Topology

namespace Critical2DKPZ.Extensions.GffTangent

/-- A compact test controls the fourth moment of every positive profile
below its absolute cell masses. The leading constant is independent of the
positive macroscopic window length c. -/
theorem eventually_fourth_positive_cell_profile_le (f : TestFn)
    {Cf : ℝ} (hCf : 0 ≤ Cf) (hfC : ∀ x : Plane, |f x| ≤ Cf)
    (φ : ℕ → Site → ℝ) (hφ : ∀ N w, 0 ≤ φ N w)
    (hdom : ∀ N w, φ N w ≤ absoluteCellProfile N f w)
    (l β : ℕ → ℝ) (hl : Tendsto l atTop atTop)
    (hratio : Tendsto (fun N => l N / Real.log (N : ℝ)) atTop (𝓝 0))
    (hβ : ∀ᶠ N : ℕ in atTop, 0 < β N)
    (hσ : ∀ᶠ N : ℕ in atTop, Polymer.sigmaSq (β N) = criticalSigmaSq (-l N) N)
    {m : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hm : Tendsto (fun N : ℕ => (m N : ℝ) / N) atTop (𝓝 c))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∫ ω, finiteEntranceFluctuation (β N) (Real.sqrt (l N)) 0 (m N)
        (fixedHorizonCellSites N f) (φ N) ω ^ 4 ∂disorderLaw) ≤
      ((2 : ℝ) ^ 32 * Real.pi ^ 2 * (4 * Cf * ∫ x : Plane, |f x|) ^ 2) * c ^ 2 + ε := by
  let M := ∫ x : Plane, |f x|
  have hM : 0 ≤ M := integral_nonneg (fun _ => abs_nonneg _)
  obtain ⟨D, hD, hcost⟩ := eventually_fourth_cell_profile_cost_bounded f φ hφ hdom hm
  have hrem := tendsto_fourthRemainderCoefficient_zero l β hl hratio hβ hσ hc hm
  have hfree : Tendsto (fun N => l N * Polymer.sigmaSq (β N) *
      Renewal.freeSecondMoment (β N) (m N)) atTop (𝓝 Real.pi) :=
    tendsto_quasiCritical_free_second_moment_macroscopic l β hl hratio hβ hσ hc hm
  let V : ℕ → ℝ := fun N =>
    (2 : ℝ) ^ 32 * (l N * Polymer.sigmaSq (β N) * Renewal.freeSecondMoment (β N) (m N)) ^ 2 *
      ((m N : ℝ) / N) ^ 2 * (4 * Cf * M) ^ 2 +
      D * |fourthRemainderCoefficient (l N) (β N) N (m N)|
  have hV : Tendsto V atTop
      (𝓝 (((2 : ℝ) ^ 32 * Real.pi ^ 2 * (4 * Cf * M) ^ 2) * c ^ 2)) := by
    have h := (((hfree.pow 2).const_mul ((2 : ℝ) ^ 32)).mul (hm.pow 2)).mul_const
      ((4 * Cf * M) ^ 2)
    have he := h.add (hrem.abs.const_mul D)
    simpa only [V, abs_zero, mul_zero, add_zero, mul_assoc, mul_left_comm, mul_comm] using he
  have hthreshold : 0 < min 1 fourthMomentSigmaThreshold :=
    lt_min (by norm_num) fourth_norm_constants_pos.2.2.2.2
  have hsmall := (tendsto_quasiCritical_fourth_run_ratio l β hl hratio hβ hσ hc hm).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hsigma := (tendsto_quasiCritical_sigma_zero l β hratio hσ).eventually
    (gt_mem_nhds hthreshold)
  filter_upwards [eventually_ge_atTop 2, hl.eventually_gt_atTop 0, hsigma, hsmall,
    eventually_quasiCritical_sigma_overlap_lt_one l β hl hratio hβ hσ hc hm,
    hcost, hV.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε))] with N hN hlN hsN hsmN hgapN hcostN hVN
  have hbound := integral_fourth_sqrt_finiteEntranceFluctuation_le N (m N) (β N) (l N) hlN
    (fixedHorizonCellSites N f) (φ N) (hφ N)
    (fun w hw => dominated_cell_profile_zero_of_not_mem N f (φ N) (hφ N) (hdom N) hw)
    (B := 4 * Cf / N) (by positivity)
    (fun w _ => (hdom N w).trans (absoluteCellProfile_le N (by omega) f hCf hfC w))
    (fourthWeightScale_pos (by omega)) (fourthWeightScale_le_one hN) hsN.le hgapN hsmN
  apply hbound.trans
  apply le_trans _ hVN.le
  have hmass := sum_dominated_cell_profile_le N f (φ N) (hdom N)
  have hmass0 : 0 ≤ ∑ w ∈ fixedHorizonCellSites N f, φ N w :=
    Finset.sum_nonneg (fun w _ => hφ N w)
  have hBmass : (4 * Cf / (N : ℝ) * ∑ w ∈ fixedHorizonCellSites N f, φ N w) ^ 2 ≤
      (4 * Cf / (N : ℝ) * M) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hmass (by positivity)) 2
  have hlead := mul_le_mul_of_nonneg_left hBmass
    (show 0 ≤ (2 : ℝ) ^ 32 * (l N * Polymer.sigmaSq (β N) * Renewal.freeSecondMoment (β N) (m N)) ^ 2 * (m N : ℝ) ^ 2 by positivity)
  have heq : (m N : ℝ) ^ 2 * (4 * Cf / (N : ℝ) * M) ^ 2 =
      ((m N : ℝ) / N) ^ 2 * (4 * Cf * M) ^ 2 := by ring
  have hrembound :
      (fourthBoundaryCost (fourthWeightScale N) (m N) (fixedHorizonCellSites N f) (φ N) *
        fourthCollisionCost (fourthWeightScale N)) * fourthRemainderCoefficient (l N) (β N) N (m N) ≤
      D * |fourthRemainderCoefficient (l N) (β N) N (m N)| := by
    have hcost0 : 0 ≤ fourthBoundaryCost (fourthWeightScale N) (m N)
        (fixedHorizonCellSites N f) (φ N) * fourthCollisionCost (fourthWeightScale N) := by
      unfold fourthCollisionCost fourthBoundaryCost
      have hmassw : 0 ≤ ∑ w ∈ fixedHorizonCellSites N f,
          φ N w * Real.exp (fourthWeightScale N * ‖siteToPlane w‖) :=
        Finset.sum_nonneg (fun w _ => mul_nonneg (hφ N w) (Real.exp_nonneg _))
      have hcB := zero_le_one.trans fourth_norm_constants_pos.1
      have hcC := zero_le_one.trans fourth_norm_constants_pos.2.2.2.1
      have hnorm := finiteLpNorm_nonneg (fixedHorizonCellSites N f) 2
        (fun w => φ N w * Real.exp (fourthWeightScale N * ‖siteToPlane w‖))
      positivity
    exact (mul_le_mul_of_nonneg_left (le_abs_self _) hcost0).trans
      (mul_le_mul_of_nonneg_right hcostN (abs_nonneg _))
  apply add_le_add _ hrembound
  apply hlead.trans_eq
  rw [mul_assoc ((2 : ℝ) ^ 32 * (l N * Polymer.sigmaSq (β N) * Renewal.freeSecondMoment (β N) (m N)) ^ 2), heq]
  ring

end Critical2DKPZ.Extensions.GffTangent
