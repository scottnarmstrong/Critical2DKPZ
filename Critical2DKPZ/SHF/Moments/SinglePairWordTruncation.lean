/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordUniform
import Critical2DKPZ.Blocks.StringSumPropagation
import Mathlib.Tactic

/-! # Uniform truncation bounds for the two-particle future profile -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open Polymer
open Filter
open scoped CompactlySupported Topology


/-- Any finite renewal-time window is controlled by its scalar renewal mass.
The terminal duration may depend arbitrarily on the renewal duration. -/
theorem abs_pairTwo_testedRenewalWindow_le_scalarMass
    {N : ℕ} (hN : 0 < N) (σ : ℝ) (hσ : 0 ≤ σ) (J : Finset ℕ) (k : ℕ → ℕ)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (x : Fin 2 → Site) (z : Site)
    (M : Fin 2 → ℝ) (hM : ∀ i, 0 ≤ M i) (hφ : ∀ i p, |φ i p| ≤ M i) :
    |(N : ℝ) ^ 2 * σ * ∑ r ∈ J, ∑ d ∈ endpoints 0 r,
      Collision.spatialRenewal σ r d * pairTwoFutureTerminalCellFactor N (k r) φ x (z + d) 0 *
        pairTwoFutureTerminalCellFactor N (k r) φ x (z + d) 1| ≤
      16 * σ * M 0 * M 1 * ∑ r ∈ J,
        Renewal.renewalMass (fun j => σ * Renewal.returnWeight j) r := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hterminal (r : ℕ) (w : Site) (i : Fin 2) :
      |(N : ℝ) * pairTwoFutureTerminalCellFactor N (k r) φ x w i| ≤ 4 * M i := by
    have h := abs_pairTwoFutureTerminalCellFactor_le (k := k r) hN φ x w i (M i) (hM i) (hφ i)
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    calc
      _ ≤ (N : ℝ) * (4 * M i / N) := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg N)
      _ = _ := by field_simp
  have hmass (r : ℕ) : (∑ d ∈ endpoints 0 r, Collision.spatialRenewal σ r d) =
      Renewal.renewalMass (fun j => σ * Renewal.returnWeight j) r := by
    rw [← tsum_spatialRenewal_eq_renewalMass]
    symm
    apply tsum_eq_sum
    intro d hd
    exact spatialRenewal_eq_zero_of_not_mem_endpoints σ r d hd
  have hpoint (r : ℕ) (d : Site) :
      |(N : ℝ) ^ 2 * σ *
        (Collision.spatialRenewal σ r d * pairTwoFutureTerminalCellFactor N (k r) φ x (z + d) 0 *
          pairTwoFutureTerminalCellFactor N (k r) φ x (z + d) 1)| ≤
      (16 * σ * M 0 * M 1) * Collision.spatialRenewal σ r d := by
    have hU := Blocks.spatialRenewal_nonneg hσ r d
    have hform : (N : ℝ) ^ 2 * σ *
        (Collision.spatialRenewal σ r d * pairTwoFutureTerminalCellFactor N (k r) φ x (z + d) 0 *
          pairTwoFutureTerminalCellFactor N (k r) φ x (z + d) 1) =
        (σ * Collision.spatialRenewal σ r d) *
          (((N : ℝ) * pairTwoFutureTerminalCellFactor N (k r) φ x (z + d) 0) *
            ((N : ℝ) * pairTwoFutureTerminalCellFactor N (k r) φ x (z + d) 1)) := by ring
    rw [hform, abs_mul, abs_of_nonneg (mul_nonneg hσ hU), abs_mul]
    have hp := mul_le_mul (hterminal r (z + d) 0) (hterminal r (z + d) 1)
      (abs_nonneg _) (mul_nonneg (by norm_num) (hM 0))
    calc
      _ ≤ (σ * Collision.spatialRenewal σ r d) * ((4 * M 0) * (4 * M 1)) :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg hσ hU)
      _ = _ := by ring
  have hsum : (N : ℝ) ^ 2 * σ * (∑ r ∈ J, ∑ d ∈ endpoints 0 r,
      Collision.spatialRenewal σ r d * pairTwoFutureTerminalCellFactor N (k r) φ x (z + d) 0 *
        pairTwoFutureTerminalCellFactor N (k r) φ x (z + d) 1) =
      ∑ r ∈ J, ∑ d ∈ endpoints 0 r, (N : ℝ) ^ 2 * σ *
        (Collision.spatialRenewal σ r d * pairTwoFutureTerminalCellFactor N (k r) φ x (z + d) 0 *
          pairTwoFutureTerminalCellFactor N (k r) φ x (z + d) 1) := by simp only [Finset.mul_sum]
  rw [hsum]
  calc
    _ ≤ ∑ r ∈ J, ∑ d ∈ endpoints 0 r,
        |(N : ℝ) ^ 2 * σ *
          (Collision.spatialRenewal σ r d * pairTwoFutureTerminalCellFactor N (k r) φ x (z + d) 0 *
            pairTwoFutureTerminalCellFactor N (k r) φ x (z + d) 1)| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro r hr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ J, ∑ d ∈ endpoints 0 r,
        (16 * σ * M 0 * M 1) * Collision.spatialRenewal σ r d := by
      exact Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun d _ => hpoint r d
    _ = (16 * σ * M 0 * M 1) * ∑ r ∈ J,
        Renewal.renewalMass (fun j => σ * Renewal.returnWeight j) r := by
      simp_rw [← Finset.mul_sum, hmass]

private theorem criticalRenewalFunction_small_horizon_uniform (ϑ : ℝ) :
    ∀ ε > 0, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ᶠ N : ℕ in atTop,
      ∀ K : ℕ, (K : ℝ) ≤ δ * N →
        criticalSigmaSq ϑ N * Renewal.criticalRenewalFunction ϑ N K ≤ ε := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := Renewal.criticalRenewalFunction_log_bound_zero_horizon ϑ 1
  let A : ℝ := C / ε + 1
  let δ : ℝ := 1 / (2 * Real.exp A)
  have hA : 0 < A := by dsimp [A]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδle : δ ≤ 1 := by
    have he : 1 ≤ Real.exp A := Real.one_le_exp hA.le
    dsimp [δ]
    apply (div_le_one (by positivity : (0 : ℝ) < 2 * Real.exp A)).2
    linarith only [he]
  obtain ⟨B, hB⟩ := exists_nat_gt (1 / δ)
  refine ⟨δ, hδ, hδle, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop B, eventually_ge_atTop 1] with N hboundN hNB hN
  intro K hK
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hδN : 1 < δ * (N : ℝ) := by
    have hBN : (B : ℝ) ≤ N := by exact_mod_cast hNB
    have h : 1 < δ * (B : ℝ) := by
      have h' := (div_lt_iff₀ hδ).mp hB
      nlinarith only [h']
    exact h.trans_le (mul_le_mul_of_nonneg_left hBN hδ.le)
  have hKN : (K : ℝ) ≤ N := by
    exact hK.trans ((mul_le_mul_of_nonneg_right hδle hNr.le).trans_eq (one_mul _))
  have hKplus : (K : ℝ) + 1 ≤ 2 * δ * N := by linarith only [hK, hδN]
  have hratio : Real.exp A ≤ (N : ℝ) / (K + 1) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < K + 1)).2
    calc
      Real.exp A * (K + 1) ≤ Real.exp A * (2 * δ * N) :=
        mul_le_mul_of_nonneg_left hKplus (Real.exp_nonneg _)
      _ = N := by dsimp [δ]; field_simp
  have hlog : A ≤ Real.log (1 + (N : ℝ) / (K + 1)) := by
    have harg : Real.exp A ≤ 1 + (N : ℝ) / (K + 1) := by linarith only [hratio]
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos A) harg
  have hquotient : C / A ≤ ε := by
    apply (div_le_iff₀ hA).2
    dsimp [A]
    have hεne : ε ≠ 0 := hε.ne'
    field_simp
    nlinarith only [hε]
  calc
    criticalSigmaSq ϑ N * Renewal.criticalRenewalFunction ϑ N K ≤
        C / Real.log (1 + (N : ℝ) / (K + 1)) := hboundN K (by simpa only [one_mul] using hKN)
    _ ≤ C / A := div_le_div_of_nonneg_left hC.le hA hlog
    _ ≤ ε := hquotient

/-- The short-renewal strip is uniformly small with arbitrary terminal clocks.
This removes the renewal-time zero endpoint of the future profile. -/
theorem pairTwo_testedRenewalWindow_small_uniform
    (ϑ : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (M : Fin 2 → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hφ : ∀ i p, |φ i p| ≤ M i) :
    ∀ ε > 0, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ᶠ N : ℕ in atTop,
      ∀ K : ℕ, (K : ℝ) ≤ δ * N → ∀ k : ℕ → ℕ,
        ∀ x : Fin 2 → Site, ∀ z : Site,
          |(N : ℝ) ^ 2 * criticalSigmaSq ϑ N *
            ∑ r ∈ Finset.range (K + 1), ∑ d ∈ endpoints 0 r,
              Collision.spatialRenewal (criticalSigmaSq ϑ N) r d *
                pairTwoFutureTerminalCellFactor N (k r) φ x (z + d) 0 *
                pairTwoFutureTerminalCellFactor N (k r) φ x (z + d) 1| ≤ ε := by
  intro ε hε
  let P : ℝ := 16 * M 0 * M 1
  have hP : 0 ≤ P := by
    exact mul_nonneg (mul_nonneg (by norm_num) (hM 0)) (hM 1)
  let η : ℝ := ε / (P + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δ, hδ, hδle, hsmall⟩ := criticalRenewalFunction_small_horizon_uniform ϑ η hη
  refine ⟨δ, hδ, hδle, ?_⟩
  filter_upwards [hsmall, Renewal.criticalSigmaSq_eventually_pos ϑ,
    eventually_gt_atTop 0] with N hsmallN hσ hN
  intro K hK k x z
  have he := abs_pairTwo_testedRenewalWindow_le_scalarMass hN (criticalSigmaSq ϑ N)
    hσ.le (Finset.range (K + 1)) k φ x z M hM hφ
  rw [Renewal.sum_renewalMass_range] at he
  have he' : |(N : ℝ) ^ 2 * criticalSigmaSq ϑ N *
      ∑ r ∈ Finset.range (K + 1), ∑ d ∈ endpoints 0 r,
        Collision.spatialRenewal (criticalSigmaSq ϑ N) r d *
          pairTwoFutureTerminalCellFactor N (k r) φ x (z + d) 0 *
          pairTwoFutureTerminalCellFactor N (k r) φ x (z + d) 1| ≤
      P * (criticalSigmaSq ϑ N * Renewal.criticalRenewalFunction ϑ N K) := by
    convert he using 1
    dsimp [P, Renewal.criticalRenewalFunction]
    ring
  calc
    _ ≤ P * (criticalSigmaSq ϑ N * Renewal.criticalRenewalFunction ϑ N K) := he'
    _ ≤ P * η := mul_le_mul_of_nonneg_left (hsmallN K hK) hP
    _ ≤ ε := by
      dsimp [η]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < P + 1)).2
      nlinarith only [hε]


end Critical2DKPZ.SHF.Moments

end
