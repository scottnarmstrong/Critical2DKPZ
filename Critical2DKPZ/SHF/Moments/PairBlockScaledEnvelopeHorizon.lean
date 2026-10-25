/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.PairBlockGaussianBound
public import Critical2DKPZ.Renewal.CriticalParameter
public import Critical2DKPZ.SHF.DeltaBose.ScalarBounds
public import Critical2DKPZ.Collision.SpatialGaussian
public import Mathlib.Tactic
public import Critical2DKPZ.SHF.Moments.PairBlockSpatialRenewalHorizon
import Mathlib.Tactic

/-! The pair-block Gaussian envelope extends uniformly to compact positive-time intervals. -/

@[expose] public section
noncomputable section
open Filter
namespace Critical2DKPZ.SHF.Moments

/-- The rescaled spatial pair-block renewal has a uniform Gaussian envelope on compact parameter and positive-time intervals. -/
theorem exists_eventually_scaled_spatialRenewal_le_gaussian_horizon
    (A δ T : ℝ) (hδ : 0 < δ) (hT : 0 < T) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ n : ℕ, δ * N ≤ n → (n : ℝ) ≤ T * N →
        ∀ z : Site, Even ((n : ℤ) + z 0 + z 1) →
          (N / 4 : ℝ) * (N / Real.log N) *
              Collision.spatialRenewal (Critical2DKPZ.criticalSigmaSq ϑ N) n z ≤
            C * Real.exp (-c *
              ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z‖ ^ 2) := by
  obtain ⟨C₀, c₀, hC₀, hc₀, hpair⟩ := exists_spatialRenewal_le_scalarMass_gaussian
  let B : ℝ := A + |Real.eulerMascheroniConstant|
  let D : ℝ := Real.exp 1 / δ * Real.exp (Real.exp (B + 1) * T)
  let C : ℝ := C₀ * (D + 1) / (4 * δ)
  let c : ℝ := c₀ / (2 * T)
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hprofile : TendstoUniformlyOn Renewal.criticalRenewalMassProfile
      (fun p : ℝ × ℝ => DeltaBose.scalarDensity (p.1 - Real.eulerMascheroniConstant) p.2)
      atTop (Set.Icc (-A) A ×ˢ Set.Icc δ T) :=
    Renewal.tendstoUniformlyOn_criticalRenewalMassProfile
      (isCompact_Icc.prod isCompact_Icc) (fun p hp => hδ.trans_le hp.2.1)
  have hclose : ∀ᶠ N : ℕ in atTop, ∀ p ∈ Set.Icc (-A) A ×ˢ Set.Icc δ T,
      dist (DeltaBose.scalarDensity (p.1 - Real.eulerMascheroniConstant) p.2)
        (Renewal.criticalRenewalMassProfile N p) < 1 := by
    have h := (Metric.tendstoUniformlyOn_iff.mp hprofile) 1 (by norm_num)
    simpa only [one_smul] using h
  obtain ⟨Nclose, hNclose⟩ := Filter.eventually_atTop.mp hclose
  obtain ⟨Nσ, hNσ⟩ := Filter.eventually_atTop.mp
    (Renewal.criticalSigmaSq_eventually_pos (-A))
  refine ⟨C, c, hC, hc, max Nclose (max Nσ 2), ?_⟩
  intro N hN0
  have hNcloseN : Nclose ≤ N := le_trans (le_max_left _ _) hN0
  have hinner : max Nσ 2 ≤ N := le_trans (le_max_right _ _) hN0
  have hσlo : 0 < Critical2DKPZ.criticalSigmaSq (-A) N :=
    hNσ N (le_trans (le_max_left _ _) hinner)
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hinner
  intro ϑ hϑ n hδn hnN z hpar
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnpos : (0 : ℝ) < n := by
    have hreal : δ * (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hδn
    have : 0 < δ * (N : ℝ) := mul_pos hδ hNpos
    exact this.trans_le hreal
  have htime : δ ≤ (n : ℝ) / N := (le_div_iff₀ hNpos).2 (by
    have hreal : δ * (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hδn
    exact hreal)
  have htime1 : (n : ℝ) / N ≤ T := (div_le_iff₀ hNpos).2 hnN
  have htheta : ϑ - Real.eulerMascheroniConstant ≤ B := by
    dsimp [B]
    linarith [neg_le_abs Real.eulerMascheroniConstant, hϑ.2]
  have hscalar' : DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant)
      ((n : ℝ) / N) ≤ D := by
    dsimp [D]
    calc
      DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) ((n : ℝ) / N)
          ≤ Real.exp 1 / ((n : ℝ) / N) *
              Real.exp (Real.exp (B + 1) * ((n : ℝ) / N)) :=
            DeltaBose.scalarDensity_le_exp htheta (lt_of_lt_of_le hδ htime)
      _ ≤ Real.exp 1 / δ * Real.exp (Real.exp (B + 1) * T) := by
        apply mul_le_mul
        · exact div_le_div_of_nonneg_left (Real.exp_nonneg _) hδ htime
        · exact Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left htime1 (by positivity))
        · positivity
        · positivity
  have hprofileClose := hNclose N hNcloseN (ϑ, (n : ℝ) / N)
    ⟨hϑ, htime, htime1⟩
  have hprofileAbs :
      |DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) ((n : ℝ) / N) -
        Renewal.criticalRenewalMassProfile N (ϑ, (n : ℝ) / N)| < 1 := by
    simpa [Real.dist_eq] using hprofileClose
  have hprofileUpper :
      Renewal.criticalRenewalMassProfile N (ϑ, (n : ℝ) / N) ≤ D + 1 := by
    have hlower := (abs_lt.mp hprofileAbs).1
    have hupper : Renewal.criticalRenewalMassProfile N (ϑ, (n : ℝ) / N) -
        DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) ((n : ℝ) / N) < 1 := by
      linarith
    linarith
  have hσ : 0 ≤ Critical2DKPZ.criticalSigmaSq ϑ N := by
    have hmono := Critical2DKPZ.Renewal.criticalSigmaSq_mono_parameter hN2 hϑ.1
    exact (hσlo.trans_le hmono).le
  have hmass :
      Renewal.criticalRenewalMassProfile N (ϑ, (n : ℝ) / N) =
        (N / Real.log N) *
          Renewal.renewalMass
            (fun r => Critical2DKPZ.criticalSigmaSq ϑ N * Renewal.returnWeight r) n := by
    rw [Renewal.criticalRenewalMassProfile, Renewal.criticalRenewalMass]
    have hfloor : ⌊(N : ℝ) * ((n : ℝ) / N)⌋₊ = n := by
      rw [show (N : ℝ) * ((n : ℝ) / N) = (n : ℝ) by field_simp]
      exact Nat.floor_natCast n
    rw [hfloor]
  have hlog : 0 < Real.log N := by
    apply Real.log_pos
    exact_mod_cast (show 1 < N by omega)
  have hfactor : 0 ≤ (N / 4 : ℝ) * (N / Real.log N) := by positivity
  have hbase := hpair (Critical2DKPZ.criticalSigmaSq ϑ N) n hσ
    (by exact_mod_cast hnpos) z hpar
  have hscaled := mul_le_mul_of_nonneg_left hbase hfactor
  have hratio : (N : ℝ) / n ≤ 1 / δ := by
    apply (div_le_iff₀ hnpos).2
    calc
      (N : ℝ) = (δ * (N : ℝ)) / δ := by field_simp
      _ ≤ (n : ℝ) / δ := div_le_div_of_nonneg_right
        (by exact_mod_cast hδn) hδ.le
      _ = (1 / δ) * n := by ring
  have hNratio : 1 / T ≤ (N : ℝ) / n := by
    apply (div_le_div_iff₀ hT hnpos).mpr
    simpa only [one_mul, mul_one, mul_comm] using hnN
  have hsqrt : 0 < Real.sqrt ((N : ℝ) / 2) := Real.sqrt_pos.2 (by positivity)
  let yNorm : ℝ := ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z‖ ^ 2
  have hyNorm : yNorm = 2 / N * ‖siteToPlane z‖ ^ 2 := by
    dsimp [yNorm]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsqrt), mul_pow,
      inv_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have hspace :
      ‖siteToPlane z‖ ^ 2 / n = ((N : ℝ) / n) / 2 * yNorm := by
    rw [hyNorm]
    field_simp
  have hexp :
      Real.exp (-c₀ * ‖siteToPlane z‖ ^ 2 / n) ≤ Real.exp (-c * yNorm) := by
    apply Real.exp_le_exp.mpr
    have hcoefBase : (1 : ℝ) / (2 * T) ≤ ((N : ℝ) / n) / 2 := by
      have hh := div_le_div_of_nonneg_right hNratio (by norm_num : (0 : ℝ) ≤ 2)
      convert hh using 1
      ring
    have hcoef := mul_le_mul_of_nonneg_left hcoefBase hc₀.le
    have hyNonneg : 0 ≤ yNorm := by dsimp [yNorm]; positivity
    have hmul := mul_le_mul_of_nonneg_right hcoef hyNonneg
    have hmul' : c₀ / (2 * T) * yNorm ≤ c₀ * (‖siteToPlane z‖ ^ 2 / n) := by
      calc
        c₀ / (2 * T) * yNorm ≤ c₀ * (((N : ℝ) / n) / 2) * yNorm := by
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
        _ = c₀ * (‖siteToPlane z‖ ^ 2 / n) := by
          rw [show c₀ * (((N : ℝ) / n) / 2) * yNorm =
            c₀ * ((((N : ℝ) / n) / 2) * yNorm) by ring, hspace]
    calc
      -c₀ * ‖siteToPlane z‖ ^ 2 / n = -(c₀ * (‖siteToPlane z‖ ^ 2 / n)) := by ring
      _ ≤ -(c₀ / (2 * T) * yNorm) := neg_le_neg hmul'
      _ = -c * yNorm := by simp [c]
  have hprofileFactor :
      (C₀ / 4) * ((N : ℝ) / n) *
          Renewal.criticalRenewalMassProfile N (ϑ, (n : ℝ) / N) ≤
        (C₀ / (4 * δ)) * (D + 1) := by
    calc
      _ ≤ (C₀ / 4) * ((N : ℝ) / n) * (D + 1) := by
        apply mul_le_mul_of_nonneg_left hprofileUpper
        positivity
      _ ≤ (C₀ / (4 * δ)) * (D + 1) := by
        apply mul_le_mul_of_nonneg_right
        · calc
            (C₀ / 4) * ((N : ℝ) / n) ≤ (C₀ / 4) * (1 / δ) :=
              mul_le_mul_of_nonneg_left hratio (by positivity)
            _ = C₀ / (4 * δ) := by ring
        · positivity
  calc
    (N / 4 : ℝ) * (N / Real.log N) *
        Collision.spatialRenewal (Critical2DKPZ.criticalSigmaSq ϑ N) n z ≤
      (N / 4 : ℝ) * (N / Real.log N) *
        (C₀ / n * Real.exp (-c₀ * ‖siteToPlane z‖ ^ 2 / n) *
          Renewal.renewalMass
            (fun r => Critical2DKPZ.criticalSigmaSq ϑ N * Renewal.returnWeight r) n) :=
          hscaled
    _ = (C₀ / 4) * ((N : ℝ) / n) *
        Renewal.criticalRenewalMassProfile N (ϑ, (n : ℝ) / N) *
          Real.exp (-c₀ * ‖siteToPlane z‖ ^ 2 / n) := by
          calc
            _ = (C₀ / 4) * ((N : ℝ) / n) *
                ((N / Real.log N) *
                  Renewal.renewalMass
                    (fun r => Critical2DKPZ.criticalSigmaSq ϑ N * Renewal.returnWeight r) n) *
                Real.exp (-c₀ * ‖siteToPlane z‖ ^ 2 / n) := by
                  field_simp [hlog.ne', hnpos.ne']
            _ = _ := by rw [← hmass]
    _ ≤ ((C₀ / (4 * δ)) * (D + 1)) * Real.exp (-c * yNorm) := by
          exact mul_le_mul hprofileFactor hexp (Real.exp_nonneg _) (by positivity)
    _ = C * Real.exp (-c *
        ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z‖ ^ 2) := by
          simp only [yNorm]
          dsimp [C]
          ring


end Critical2DKPZ.SHF.Moments
