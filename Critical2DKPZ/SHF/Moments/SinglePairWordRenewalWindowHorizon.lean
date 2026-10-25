/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureWindows
import Mathlib.Tactic

/-! # Tested renewal clock-window bounds on arbitrary finite horizons -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter Polymer
open scoped CompactlySupported Topology

/-- The critical weighted renewal mass is `O(1/N)` on every fixed positive time slab. -/
theorem exists_eventually_criticalRenewalMass_weight_le_div_N_horizon
    (ϑ τ T : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ r : ℕ,
      τ * N ≤ r → (r : ℝ) ≤ T * N →
        criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N r ≤ C / N := by
  let B : ℝ := ϑ - Real.eulerMascheroniConstant
  let D : ℝ := Real.exp 1 / τ * Real.exp (Real.exp (B + 1) * T)
  let C : ℝ := 2 * Real.pi * (D + 1)
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hprofile : TendstoUniformlyOn Renewal.criticalRenewalMassProfile
      (fun p : ℝ × ℝ => DeltaBose.scalarDensity (p.1 - Real.eulerMascheroniConstant) p.2)
      atTop (Set.Icc ϑ ϑ ×ˢ Set.Icc τ T) :=
    Renewal.tendstoUniformlyOn_criticalRenewalMassProfile
      (isCompact_Icc.prod isCompact_Icc) (fun p hp => hτ.trans_le hp.2.1)
  have hprofileClose : ∀ᶠ N : ℕ in atTop,
      ∀ p ∈ Set.Icc ϑ ϑ ×ˢ Set.Icc τ T,
        |Renewal.criticalRenewalMassProfile N p -
          DeltaBose.scalarDensity (p.1 - Real.eulerMascheroniConstant) p.2| < 1 := by
    have h := (Metric.tendstoUniformlyOn_iff.mp hprofile) 1 (by norm_num)
    filter_upwards [h] with N hN p hp
    have hp' := hN p hp
    simpa only [Real.dist_eq, abs_sub_comm] using hp'
  have hσlog := Renewal.tendsto_sigma_mul_log ϑ
  have hσupper : ∀ᶠ N : ℕ in atTop,
      criticalSigmaSq ϑ N * Real.log N < 2 * Real.pi :=
    hσlog.eventually (Iio_mem_nhds (by linarith [Real.pi_pos]))
  refine ⟨C, hC, ?_⟩
  filter_upwards [hprofileClose, hσupper,
      Renewal.criticalSigmaSq_eventually_pos ϑ, eventually_ge_atTop 2]
      with N hprofileN hσNupper hσN hN
  intro r hrlo hrhi
  have hNreal : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogne : Real.log N ≠ 0 := hlog.ne'
  have htlo : τ ≤ (r : ℝ) / N := (le_div_iff₀ hNreal).2 (by exact_mod_cast hrlo)
  have hthi : (r : ℝ) / N ≤ T := (div_le_iff₀ hNreal).2 hrhi
  have hfloor : Nat.floor ((N : ℝ) * ((r : ℝ) / N)) = r := by
    have hmul : (N : ℝ) * ((r : ℝ) / N) = r := by field_simp [hNreal.ne']
    rw [hmul, Nat.floor_natCast]
  have hprofileEq : Renewal.criticalRenewalMassProfile N
      (ϑ, (r : ℝ) / N) =
        (N / Real.log N) * Renewal.criticalRenewalMass ϑ N r := by
    simp [Renewal.criticalRenewalMassProfile, hfloor]
  have hlocal := hprofileN (ϑ, (r : ℝ) / N)
    ⟨⟨le_rfl, le_rfl⟩, ⟨htlo, hthi⟩⟩
  have hdensity : DeltaBose.scalarDensity B ((r : ℝ) / N) ≤ D := by
    have h := DeltaBose.scalarDensity_le_exp (θ := B) (B := B)
      le_rfl (lt_of_lt_of_le hτ htlo)
    dsimp [D, B]
    calc
      DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) ((r : ℝ) / N)
          ≤ Real.exp 1 / ((r : ℝ) / N) *
              Real.exp (Real.exp (ϑ - Real.eulerMascheroniConstant + 1) *
                ((r : ℝ) / N)) := h
      _ ≤ Real.exp 1 / τ * Real.exp
          (Real.exp (ϑ - Real.eulerMascheroniConstant + 1) * T) := by
        apply mul_le_mul
        · exact div_le_div_of_nonneg_left (Real.exp_nonneg _) hτ htlo
        · apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_left hthi (Real.exp_nonneg _)
        · positivity
        · positivity
  have hprofileUpper :
      Renewal.criticalRenewalMassProfile N (ϑ, (r : ℝ) / N) ≤ D + 1 := by
    have hupper := (abs_lt.mp hlocal).2
    dsimp [B] at hdensity
    linarith
  have hmassNonneg : 0 ≤ Renewal.criticalRenewalMass ϑ N r := by
    change 0 ≤ Renewal.renewalMass
      (fun j => criticalSigmaSq ϑ N * Renewal.returnWeight j) r
    apply Renewal.renewalMass_nonneg
    intro j
    exact mul_nonneg hσN.le (srwKernel_nonneg (2 * j) 0)
  have hprofileNonneg : 0 ≤ Renewal.criticalRenewalMassProfile N
      (ϑ, (r : ℝ) / N) := by
    rw [hprofileEq]
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg N) hlog.le) hmassNonneg
  have hproduct :
      criticalSigmaSq ϑ N * Real.log N *
        Renewal.criticalRenewalMassProfile N (ϑ, (r : ℝ) / N) ≤
      2 * Real.pi * (D + 1) := by
    exact mul_le_mul hσNupper.le hprofileUpper hprofileNonneg (by positivity)
  have hscale :
      criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N r =
        (criticalSigmaSq ϑ N * Real.log N *
          Renewal.criticalRenewalMassProfile N (ϑ, (r : ℝ) / N)) / N := by
    rw [hprofileEq]
    field_simp [hNreal.ne', hlogne]
  rw [hscale]
  calc
    _ ≤ (2 * Real.pi * (D + 1)) / N :=
      div_le_div_of_nonneg_right hproduct (Nat.cast_nonneg N)
    _ = C / N := by rfl

/-- Arbitrary tested windows on a finite positive renewal-time slab are bounded by clock cardinality. -/
theorem pairTwo_testedRenewalWindow_away_zero_scaled_le_horizon
    (ϑ τ T : ℝ) (hτ : 0 < τ) (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (M : Fin 2 → ℝ) (hM : ∀ i, 0 ≤ M i) (hφ : ∀ i p, |φ i p| ≤ M i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ J : Finset ℕ,
      (∀ r ∈ J, τ * N ≤ (r : ℝ) ∧ (r : ℝ) ≤ T * N) → ∀ k : ℕ → ℕ,
        ∀ x : Fin 2 → Site, ∀ z : Site,
          |(N : ℝ) ^ 2 * criticalSigmaSq ϑ N * ∑ r ∈ J, ∑ d ∈ endpoints 0 r,
            Collision.spatialRenewal (criticalSigmaSq ϑ N) r d *
              pairTwoFutureTerminalCellFactor N (k r) φ x (z + d) 0 *
              pairTwoFutureTerminalCellFactor N (k r) φ x (z + d) 1| ≤ C * (J.card / N) := by
  obtain ⟨C₀, hC₀, hmass⟩ := exists_eventually_criticalRenewalMass_weight_le_div_N_horizon ϑ τ T hτ
  let P : ℝ := 16 * M 0 * M 1
  have hP : 0 ≤ P := mul_nonneg (mul_nonneg (by norm_num) (hM 0)) (hM 1)
  refine ⟨P * C₀, mul_nonneg hP hC₀.le, ?_⟩
  filter_upwards [hmass, Renewal.criticalSigmaSq_eventually_pos ϑ,
    eventually_gt_atTop 0] with N hmassN hσ hN
  intro J hJ k x z
  have he := abs_pairTwo_testedRenewalWindow_le_scalarMass hN (criticalSigmaSq ϑ N)
    hσ.le J k φ x z M hM hφ
  have hsum : (∑ r ∈ J, criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N r) ≤
      J.card * (C₀ / N) := by
    calc
      _ ≤ ∑ _r ∈ J, C₀ / N :=
        Finset.sum_le_sum fun r hr => hmassN r (hJ r hr).1 (hJ r hr).2
      _ = _ := by simp
  have hform : 16 * criticalSigmaSq ϑ N * M 0 * M 1 *
      (∑ r ∈ J, Renewal.renewalMass
        (fun j => criticalSigmaSq ϑ N * Renewal.returnWeight j) r) =
      P * ∑ r ∈ J, criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N r := by
    rw [← Finset.mul_sum]
    dsimp [P, Renewal.criticalRenewalMass]
    ring
  calc
    _ ≤ P * ∑ r ∈ J, criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N r := he.trans_eq hform
    _ ≤ P * (J.card * (C₀ / N)) := mul_le_mul_of_nonneg_left hsum hP
    _ = (P * C₀) * (J.card / N) := by ring
/-- On renewal-time intervals bounded away from zero, a future-tail clock window is bounded by a constant times its clock cardinality divided by `N`. -/
theorem pairTwoTestedRenewalWindow_away_zero_le_horizon
    (ϑ τ T : ℝ) (hτ : 0 < τ) (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (M : Fin 2 → ℝ) (hM : ∀ i, 0 ≤ M i) (hφ : ∀ i p, |φ i p| ≤ M i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ J : Finset ℕ,
      (∀ r ∈ J, τ * N ≤ (r : ℝ) ∧ (r : ℝ) ≤ T * N) → ∀ L : ℕ,
        ∀ x : Fin 2 → Site, ∀ z : Site,
          |pairTwoTestedRenewalWindow ϑ N L φ x z J| ≤ C * (J.card / N) := by
  obtain ⟨C, hC, he⟩ := pairTwo_testedRenewalWindow_away_zero_scaled_le_horizon ϑ τ T hτ φ M hM hφ
  refine ⟨C, hC, ?_⟩
  filter_upwards [he] with N hN
  intro J hJ L x z
  exact hN J hJ (fun r => L - r) x z

end Critical2DKPZ.SHF.Moments
