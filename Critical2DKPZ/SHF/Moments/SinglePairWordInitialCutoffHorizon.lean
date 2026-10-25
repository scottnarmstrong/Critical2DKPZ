/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordInitialCutoff
public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureSamplingHorizon
public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureBoundHorizon
import Mathlib.Tactic

/-! # Incoming integrated cutoff entrance limits at arbitrary finite horizons -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter
open scoped CompactlySupported Topology

private theorem initialStep_pointwise_limit_horizon
    (ϑ T : ℝ) (L : ℕ → ℕ)
    (hL : Tendsto (fun N => (L N : ℝ) / N) atTop (𝓝 T))
    {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (η : C_c(ℝ × Plane, ℝ))
    (hη : ∀ p ∈ tsupport η, 0 < p.1 ∧ p.1 < T) (p : Plane × Plane) :
    Tendsto (fun N => pairTwoCutoffInitialStep ϑ N (L N)
      (evenCeil (N * s) + 1) (evenCeil (N * t)) φ η p) atTop
      (𝓝 (pairTwoContinuumCutoffEntrance (ϑ - Real.eulerMascheroniConstant) T s t φ η p)) := by
  let a : Fin 2 → Plane := ![p.1, p.2]
  let xN : ℕ → Fin 2 → Site := fun N => ![latticePoint N p.1, latticePoint N p.2]
  have hx (N : ℕ) (i : Fin 2) : xN N i ∈ evenLattice := by
    fin_cases i <;> exact latticePoint_mem_evenLattice N _
  have ha (i : Fin 2) : Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (a i)) := by
    fin_cases i <;> exact tendsto_cellSample _
  exact tendsto_pairTwoFutureSampleProfile_collisionEntrance_cutoff_horizon ϑ T L hL hs hst
    (fun N => evenCeil (N * s)) (fun N => evenCeil (N * t))
    (tendsto_evenCeil_div s hs.le) (tendsto_evenCeil_div t (hs.trans hst).le)
    φ xN hx a ha η hη

private theorem initialStep_uniform_bound_horizon
    (ϑ T : ℝ) (hT : 0 < T) (L : ℕ → ℕ)
    (hL : Tendsto (fun N => (L N : ℝ) / N) atTop (𝓝 T))
    {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (η : C_c(ℝ × Plane, ℝ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop, ∀ p : Plane × Plane,
      |pairTwoCutoffInitialStep ϑ N (L N)
        (evenCeil (N * s) + 1) (evenCeil (N * t)) φ η p| ≤ B := by
  obtain ⟨Cf, hCf, hf⟩ := eventually_pairTwoFutureSampleProfile_bdd_horizon ϑ (T + 1) (by linarith only [hT]) φ
  obtain ⟨C, hC, hc⟩ := collisionEntrance_abs_le_positiveTime_card hs
  let M : ℝ := ‖η.toBoundedContinuousFunction‖ * Cf
  have hM : 0 ≤ M := mul_nonneg (norm_nonneg _) hCf
  let B : ℝ := (M * C / s) * (t + 3)
  have hB : 0 ≤ B := mul_nonneg (div_nonneg (mul_nonneg hM hC.le) hs.le)
    (by linarith only [hs, hst])
  refine ⟨B, hB, ?_⟩
  have hLu := hL.eventually (Iio_mem_nhds (lt_add_one T))
  filter_upwards [hf, hLu, eventually_gt_atTop 0] with N hfN hLN hN p
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hLe : (L N : ℝ) ≤ (T + 1) * N := ((div_lt_iff₀ hNr).mp hLN).le
  let x : Fin 2 → Site := ![latticePoint N p.1, latticePoint N p.2]
  have htest (q : ℝ × Plane) : |η q * pairTwoFutureSampleProfile ϑ N (L N) φ x q| ≤ M := by
    rw [abs_mul]
    exact mul_le_mul (η.toBoundedContinuousFunction.norm_coe_le_norm q)
      (hfN (L N) hLe x q) (abs_nonneg _) (norm_nonneg _)
  have htime : ∀ r ∈ Finset.Icc (evenCeil (N * s) + 1) (evenCeil (N * t)),
      s * (N : ℝ) ≤ r := by
    intro r hr
    have hlo : evenCeil (N * s) ≤ r :=
      (Nat.le_succ _).trans (Finset.mem_Icc.mp hr).1
    calc
      s * (N : ℝ) = (N : ℝ) * s := mul_comm _ _
      _ ≤ evenCeil (N * s) := Critical2DKPZ.le_evenCeil _
      _ ≤ r := by exact_mod_cast hlo
  have hcard : ((Finset.Icc (evenCeil (N * s) + 1) (evenCeil (N * t))).card : ℝ) / N ≤ t + 3 := by
    have hcNat : (Finset.Icc (evenCeil (N * s) + 1) (evenCeil (N * t))).card ≤
        evenCeil (N * t) + 1 :=
      (Finset.card_le_card (Finset.Icc_subset_Icc_left (Nat.zero_le _))).trans_eq (by simp)
    have hcReal : ((Finset.Icc (evenCeil (N * s) + 1) (evenCeil (N * t))).card : ℝ) ≤
        (evenCeil (N * t) : ℝ) + 1 := by exact_mod_cast hcNat
    have hceil := Critical2DKPZ.evenCeil_lt_add_two (mul_nonneg hNr.le (hs.trans hst).le)
    apply (div_le_iff₀ hNr).mpr
    linarith only [hcReal, hceil, hNr1]
  have hb := hc N _ _ (x 0) (x 1) _ M hN hM htest htime
  exact hb.trans (mul_le_mul_of_nonneg_left hcard (div_nonneg (mul_nonneg hM hC.le) hs.le))

/-- Integrability of the continuum incoming-location cutoff integral. -/
theorem integrableOn_pairTwoContinuumCutoffEntrance_horizon
    (ϑ T : ℝ) (hT : 0 < T) (L : ℕ → ℕ)
    (hL : Tendsto (fun N => (L N : ℝ) / N) atTop (𝓝 T))
    {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (η : C_c(ℝ × Plane, ℝ))
    (hη : ∀ p ∈ tsupport η, 0 < p.1 ∧ p.1 < T)
    (K : Set (Plane × Plane)) (hK : volume K ≠ ⊤) :
    IntegrableOn (pairTwoContinuumCutoffEntrance (ϑ - Real.eulerMascheroniConstant) T s t φ η) K := by
  obtain ⟨B, _hB, hb⟩ := initialStep_uniform_bound_horizon ϑ T hT L hL hs hst φ η
  have hlim := fun p => initialStep_pointwise_limit_horizon ϑ T L hL hs hst φ η hη p
  have hm : AEStronglyMeasurable
      (pairTwoContinuumCutoffEntrance (ϑ - Real.eulerMascheroniConstant) T s t φ η)
      (volume.restrict K) := aestronglyMeasurable_of_tendsto_ae atTop
    (fun N => (measurable_pairTwoCutoffInitialStep ϑ N (L N) _ _ φ η).aestronglyMeasurable)
    (Eventually.of_forall hlim)
  apply (integrableOn_const (C := B) hK).mono' hm
  apply Eventually.of_forall
  intro p
  rw [Real.norm_eq_abs]
  exact le_of_tendsto (hlim p).abs (hb.mono fun N hN => hN p)

/-- The cutoff entrance limit can be integrated over any finite-measure set
of incoming locations. The singular coincident-start set needs no exclusion. -/
theorem tendsto_integral_pairTwoCutoffInitialStep_horizon
    (ϑ T : ℝ) (hT : 0 < T) (L : ℕ → ℕ)
    (hL : Tendsto (fun N => (L N : ℝ) / N) atTop (𝓝 T))
    {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (η : C_c(ℝ × Plane, ℝ))
    (hη : ∀ p ∈ tsupport η, 0 < p.1 ∧ p.1 < T)
    (K : Set (Plane × Plane)) (hK : volume K ≠ ⊤) :
    Tendsto (fun N => ∫ p in K, pairTwoCutoffInitialStep ϑ N (L N)
      (evenCeil (N * s) + 1) (evenCeil (N * t)) φ η p) atTop
      (𝓝 (∫ p in K, pairTwoContinuumCutoffEntrance
        (ϑ - Real.eulerMascheroniConstant) T s t φ η p)) := by
  obtain ⟨B, _hB, hb⟩ := initialStep_uniform_bound_horizon ϑ T hT L hL hs hst φ η
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => B)
  · exact Eventually.of_forall fun N => (measurable_pairTwoCutoffInitialStep ϑ N (L N) _ _ φ η).aestronglyMeasurable
  · filter_upwards [hb] with N hN
    exact Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hN p
  · exact integrableOn_const hK
  · exact Eventually.of_forall fun p => initialStep_pointwise_limit_horizon ϑ T L hL hs hst φ η hη p

end Critical2DKPZ.SHF.Moments
