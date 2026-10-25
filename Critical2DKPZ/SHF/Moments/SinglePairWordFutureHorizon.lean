/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureConvergence
public import Critical2DKPZ.SHF.Moments.SinglePairWordTimeIntegralHorizon
public import Critical2DKPZ.SHF.Moments.SinglePairWordRenewalWindowHorizon
import Mathlib.Tactic

/-! # Complete moving two-particle future tails on arbitrary finite horizons -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter Polymer
open scoped CompactlySupported Topology

/-- Along moving horizons with a positive finite limit, the complete tested future tail converges without truncating renewal endpoints or spatial tails. -/
theorem tendsto_pairTwoFutureTestedTail_moving
    (ϑ H : ℝ) (hH : 0 < H) (L : ℕ → ℕ)
    (hL : Tendsto (fun N : ℕ => (L N : ℝ) / N) atTop (𝓝 H))
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (xN : ℕ → Fin 2 → Site)
    (hx : ∀ᶠ N : ℕ in atTop, ∀ i : Fin 2, xN N i ∈ evenLattice)
    (a : Fin 2 → Plane)
    (ha : ∀ i : Fin 2, Tendsto (fun N : ℕ => latticeRepresentative N (xN N i)) atTop (𝓝 (a i)))
    (zN : ℕ → Site) (z : Plane)
    (hz : Tendsto (fun N : ℕ => latticeRepresentative N (zN N)) atTop (𝓝 z))
    (hphase : ∀ᶠ N : ℕ in atTop, Even (zN N 0 + zN N 1 + (L N : ℤ))) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ 2 *
      pairTwoFutureTestedTail (criticalSigmaSq ϑ N) N (L N) 0 φ (xN N) (zN N)) atTop
      (𝓝 (∫ u in (0 : ℝ)..H,
        pairTwoTestedSpatialProfile (ϑ - Real.eulerMascheroniConstant) u (H - u) φ a z)) := by
  let M : Fin 2 → ℝ := fun i => ‖(φ i).toBoundedContinuousFunction‖
  have hM (i : Fin 2) : 0 ≤ M i := norm_nonneg _
  have hφ (i : Fin 2) (p : Plane × Plane) : |φ i p| ≤ M i :=
    (φ i).toBoundedContinuousFunction.norm_coe_le_norm p
  let F : ℝ → ℝ := fun u =>
    pairTwoTestedSpatialProfile (ϑ - Real.eulerMascheroniConstant) u (H - u) φ a z
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η : ℝ := ε / 8
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δD, hδD, _hδD1, hD⟩ := pairTwoTestedRenewalWindow_initial_small ϑ φ M hM hφ η hη
  obtain ⟨C, hC, hT⟩ := pairTwoTestedRenewalWindow_away_zero_le_horizon
    ϑ (H / 2) (H + 1) (half_pos hH) φ M hM hφ
  let R : ℝ := min (H / 4) (min (δD / 2) (η / (4 * (C + 1))))
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨δ, hδ, _hδH, hδR, hContinuum⟩ :=
    pairTwoTestedSpatialProfile_endpoint_strips_small_below
      (ϑ - Real.eulerMascheroniConstant) H hH R hR φ η hη
  have hδH4 : δ ≤ H / 4 := hδR.trans (min_le_left _ _)
  have hδD' : δ < δD :=
    (hδR.trans ((min_le_right _ _).trans (min_le_left _ _))).trans_lt (half_lt_self hδD)
  have hδC : δ ≤ η / (4 * (C + 1)) :=
    hδR.trans ((min_le_right _ _).trans (min_le_right _ _))
  let t : ℝ := H - δ
  have hδt : δ < t := by dsimp [t]; linarith only [hδH4, hH]
  have htH : t < H := sub_lt_self H hδ
  have htHalf : H / 2 < t := by dsimp [t]; linarith only [hδH4, hH]
  let A : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * δ)
  let B : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * t)
  have hAr : Tendsto (fun N : ℕ => (A N : ℝ) / N) atTop (𝓝 δ) :=
    tendsto_evenCeil_div δ hδ.le
  have hBr : Tendsto (fun N : ℕ => (B N : ℝ) / N) atTop (𝓝 t) :=
    tendsto_evenCeil_div t (hδ.trans hδt).le
  have hBL := eventually_nat_le_of_scaled_limit_lt B L hBr hL htH
  have hcard := tendsto_terminal_window_card_ratio B L hBr hL htH
  have hInt := tendsto_pairTwo_testedFuture_interior_horizon ϑ H L hL φ xN hx a ha zN z hz hphase
    hδ hδt htH
  have hInt' : Tendsto
      (fun N => pairTwoTestedRenewalWindow ϑ N (L N) φ (xN N) (zN N) (Finset.Icc (A N + 1) (B N)))
      atTop (𝓝 (∫ u in δ..t, F u)) := hInt
  have hc := hContinuum a z
  have hδH' : δ ≤ H := hδH4.trans (by linarith only [hH] : H / 4 ≤ H)
  have hmid := (abs_integral_pairTwoTestedSpatialProfile_le_scalar
    (ϑ - Real.eulerMascheroniConstant) H φ a z hδ.le hδt.le htH.le).1
  have hsumC : (∫ u in (0 : ℝ)..H, F u) =
      (∫ u in (0 : ℝ)..δ, F u) + (∫ u in δ..t, F u) + (∫ u in t..H, F u) := by
    have h₀ : IntervalIntegrable F volume 0 δ := hc.1
    have h₁ : IntervalIntegrable F volume δ t := hmid
    have h₂ : IntervalIntegrable F volume t H := hc.2.1
    rw [← intervalIntegral.integral_add_adjacent_intervals (h₀.trans h₁) h₂,
      ← intervalIntegral.integral_add_adjacent_intervals h₀ h₁]
  filter_upwards [hD, hT, hBL, eventually_gt_atTop 0,
    hAr.eventually (Iio_mem_nhds hδD'), hBr.eventually (Ioi_mem_nhds htHalf),
    hL.eventually (Iio_mem_nhds (lt_add_one H)),
    hcard.eventually (Iio_mem_nhds (show H - t < 2 * δ by dsimp [t]; linarith only [hδ])),
    (Metric.tendsto_nhds.mp hInt') η hη]
      with N hDN hTN hBLN hN hAN hBN hLN hcardN hIntN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hAK : (A N : ℝ) ≤ δD * N := ((div_lt_iff₀ hNr).mp hAN).le
  have hLN' : (L N : ℝ) ≤ (H + 1) * N := ((div_lt_iff₀ hNr).mp hLN).le
  have hAB : A N ≤ B N :=
    Critical2DKPZ.evenCeil_mono (mul_le_mul_of_nonneg_left hδt.le hNr.le)
  have hbottom := hDN (A N) hAK (L N) (xN N) (zN N)
  have htop := hTN (Finset.Icc (B N + 1) (L N)) (fun r hr => by
    have hr' := Finset.mem_Icc.mp hr
    constructor
    · have hBreal : (B N : ℝ) ≤ r := by exact_mod_cast (show B N ≤ r by omega)
      exact ((lt_div_iff₀ hNr).mp hBN).le.trans hBreal
    · exact (show (r : ℝ) ≤ L N by exact_mod_cast hr'.2).trans hLN') (L N) (xN N) (zN N)
  have htop' : |pairTwoTestedRenewalWindow ϑ N (L N) φ (xN N) (zN N)
      (Finset.Icc (B N + 1) (L N))| ≤ η :=
    htop.trans ((mul_le_mul_of_nonneg_left hcardN.le hC).trans
      (terminal_window_error_budget hC hδ.le hδC))
  have hmiddle : |pairTwoTestedRenewalWindow ϑ N (L N) φ (xN N) (zN N)
      (Finset.Icc (A N + 1) (B N)) - ∫ u in δ..t, F u| ≤ η := by
    simpa only [Real.dist_eq] using hIntN.le
  rw [Real.dist_eq, ← pairTwoTestedRenewalWindow_full, hsumC,
    pairTwoTestedRenewalWindow_three_parts ϑ N (L N) (A N) (B N) hAB hBLN]
  have he := three_part_error_le _ _ _ _ _ _ η hbottom hmiddle htop' hc.2.2.1 hc.2.2.2
  exact he.trans_lt (by dsimp [η]; linarith only [hε])

end Critical2DKPZ.SHF.Moments
