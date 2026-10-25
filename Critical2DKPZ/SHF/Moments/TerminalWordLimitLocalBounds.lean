/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.PairBlockSpatialRenewalHorizon
public import Critical2DKPZ.SHF.DeltaBose.ScalarDensity
public import Critical2DKPZ.RandomWalk.GaussianBridge
import Mathlib.Tactic

/-! # Uniform kernel bounds on interior time slabs -/

@[expose] public noncomputable section

open Filter
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

/-- The normalized free kernel is uniformly bounded on every positive time
slab, with no restriction on its spatial argument. -/
theorem exists_scaled_srwKernel_interior_bound {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N n : ℕ), a * N ≤ (n : ℝ) →
      ∀ z : Site, ((N : ℝ) / 4) * srwKernel n z ≤ C := by
  obtain ⟨B, c, hB, hc, hgauss⟩ := srwKernel_gaussianBound_all_times
  refine ⟨B / a, div_pos hB ha, ?_⟩
  intro N n hn z
  have hexp : Real.exp (-c * ‖siteToPlane z‖ ^ 2 / ((n : ℝ) + 1)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (sq_nonneg _)) (by positivity)
  have hwalk : srwKernel n z ≤ B / ((n : ℝ) + 1) :=
    (hgauss n z).trans (mul_le_of_le_one_right (by positivity) hexp)
  have hratio : (N : ℝ) / ((n : ℝ) + 1) ≤ 1 / a := by
    apply (div_le_div_iff₀ (by positivity) ha).2
    linarith only [hn]
  calc
    _ ≤ ((N : ℝ) / 4) * (B / ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hwalk (by positivity)
    _ = (B / 4) * ((N : ℝ) / ((n : ℝ) + 1)) := by ring
    _ ≤ (B / 4) * (1 / a) := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = (B / 4) / a := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [hB]) ha.le

/-- The normalized spatial renewal kernel is uniformly bounded on compact
positive-time slabs and diffusive spatial windows. -/
theorem eventually_scaled_spatialRenewal_interior_bound (ϑ a T R : ℝ)
    (ha : 0 < a) (haT : a ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
      a * N ≤ (n : ℝ) → (n : ℝ) ≤ T * N → ∀ z : Site,
      Even ((n : ℤ) + z 0 + z 1) → ‖siteToPlane z‖ ≤ R * Real.sqrt (N : ℝ) →
      |((N : ℝ) / 4) * (N / Real.log N) *
        Collision.spatialRenewal (criticalSigmaSq ϑ N) n z| ≤ C := by
  have hdcont : ContinuousOn (fun u : ℝ => scalarDensity (ϑ - Real.eulerMascheroniConstant) u)
      (Set.Icc a T) :=
    continuousOn_scalarDensity.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun u hu => ha.trans_le hu.1)
  obtain ⟨D₀, hD₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hdcont
  let D := |D₀| + 1
  let H := (Real.pi * a)⁻¹
  have hD : 0 < D := by dsimp [D]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨1 + D * H, by positivity, ?_⟩
  filter_upwards [spatialRenewal_localLimit_horizon |ϑ| a T R ha haT 1 (by norm_num),
      eventually_gt_atTop 0] with N hlocal hN
  intro n hnlo hnhi z hphase hz
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have htime : (n : ℝ) / N ∈ Set.Icc a T :=
    ⟨(le_div_iff₀ hNr).2 hnlo, (div_le_iff₀ hNr).2 hnhi⟩
  have ht : 0 < (n : ℝ) / (2 * N) := by
    have hp := ha.trans_le htime.1
    exact div_pos ((div_pos_iff_of_pos_right hNr).mp hp) (by positivity)
  have hhalf : a / 2 ≤ (n : ℝ) / (2 * N) := by
    calc
      _ ≤ ((n : ℝ) / N) / 2 := div_le_div_of_nonneg_right htime.1 (by norm_num)
      _ = _ := by ring
  have hheat : |heatKernel ((n : ℝ) / (2 * N)) (latticeRepresentative N z)| ≤ H := by
    rw [abs_of_nonneg (Critical2DKPZ.heatKernel_pos ht _).le]
    calc
      _ ≤ (2 * Real.pi * ((n : ℝ) / (2 * N)))⁻¹ := heatKernel_le_at_zero ht.le _
      _ ≤ H := by
        apply (inv_le_inv₀ (by positivity) (mul_pos Real.pi_pos ha)).2
        have hh := mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ 2 * Real.pi)
        nlinarith only [hh]
  have hdensity : |scalarDensity (ϑ - Real.eulerMascheroniConstant) ((n : ℝ) / N)| ≤ D := by
    have hh : |scalarDensity (ϑ - Real.eulerMascheroniConstant) ((n : ℝ) / N)| ≤ D₀ := by
      simpa only [Real.norm_eq_abs] using hD₀ _ htime
    exact hh.trans (by dsimp [D]; linarith only [le_abs_self D₀])
  have herr := hlocal ϑ ⟨neg_abs_le _, le_abs_self _⟩ n hnlo hnhi z hphase hz
  have htarget : |scalarDensity (ϑ - Real.eulerMascheroniConstant) ((n : ℝ) / N) *
      heatKernel ((n : ℝ) / (2 * N)) (latticeRepresentative N z)| ≤ D * H := by
    rw [abs_mul]
    exact mul_le_mul hdensity hheat (abs_nonneg _) hD.le
  calc
    _ ≤ |((N : ℝ) / 4) * (N / Real.log N) * Collision.spatialRenewal (criticalSigmaSq ϑ N) n z -
          scalarDensity (ϑ - Real.eulerMascheroniConstant) ((n : ℝ) / N) *
            heatKernel ((n : ℝ) / (2 * N)) (latticeRepresentative N z)| +
        |scalarDensity (ϑ - Real.eulerMascheroniConstant) ((n : ℝ) / N) *
          heatKernel ((n : ℝ) / (2 * N)) (latticeRepresentative N z)| := by
      have he : ∀ A B : ℝ, |A| ≤ |A - B| + |B| := fun A B => by
        calc
          |A| = |(A - B) + B| := by rw [sub_add_cancel]
          _ ≤ _ := abs_add_le _ _
      exact he _ _
    _ ≤ _ := add_le_add herr htarget

end Critical2DKPZ.SHF.Moments
