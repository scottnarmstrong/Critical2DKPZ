/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.PairBlockScaledEnvelopeHorizon
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitUniformSpatialBound
public import Critical2DKPZ.Collision.SpatialRenewalHatGaussian
import Mathlib.Tactic

/-! # Global Gaussian bounds for interior first-letter blocks -/

@[expose] public noncomputable section
open Filter MeasureTheory
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds
namespace Critical2DKPZ.SHF.Moments

/-- A bounded displacement changes a Gaussian envelope only by a constant
and a factor two in its exponent. -/
theorem exp_neg_norm_sq_le_of_norm_sub_le {E : Type*} [NormedAddCommGroup E]
    {c R : ℝ} (hc : 0 ≤ c) (hR : 0 ≤ R) (p d : E) (hpd : ‖p - d‖ ≤ R) :
    Real.exp (-c * ‖d‖ ^ 2) ≤
      Real.exp (c * R ^ 2) * Real.exp (-(c / 2) * ‖p‖ ^ 2) := by
  have ht : ‖p‖ ≤ R + ‖d‖ := (norm_le_norm_sub_add p d).trans (add_le_add hpd le_rfl)
  have hsq : ‖p‖ ^ 2 ≤ 2 * R ^ 2 + 2 * ‖d‖ ^ 2 := by
    have hs := (sq_le_sq₀ (norm_nonneg p) (add_nonneg hR (norm_nonneg d))).mpr ht
    nlinarith only [hs, sq_nonneg (R - ‖d‖)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_nonneg hc (sub_nonneg.mpr hsq)]

/-- The spatial renewal Gaussian envelope also holds off the reachable
parity class, since the parity-correct domination there is zero. -/
theorem eventually_scaled_spatialRenewal_le_gaussian_all_parities
    (ϑ η T : ℝ) (hη : 0 < η) (hT : 0 < T) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
      η * N ≤ (n : ℝ) → (n : ℝ) ≤ T * N → ∀ z : Site,
      (N / 4 : ℝ) * (N / Real.log N) * Collision.spatialRenewal (criticalSigmaSq ϑ N) n z ≤
        C * Real.exp (-c * ‖latticeRepresentative N z‖ ^ 2) := by
  obtain ⟨C, c, hC, hc, N₀, hg⟩ :=
    exists_eventually_scaled_spatialRenewal_le_gaussian_horizon |ϑ| η T hη hT
  obtain ⟨c₀, hc₀, hu⟩ := Collision.spatialRenewal_le_hatGaussian_uniform
  obtain ⟨D, hD, hd⟩ := hu (c₀ / 2) (by positivity) (by linarith)
  refine ⟨C, c, hC, hc, ?_⟩
  filter_upwards [eventually_ge_atTop N₀, eventually_gt_atTop 1, criticalBeta_spec ϑ]
    with N hN₀ hN hσ
  intro n hn hnT z
  by_cases hp : Even ((n : ℤ) + z 0 + z 1)
  · exact hg N hN₀ ϑ ⟨neg_abs_le _, le_abs_self _⟩ n hn hnT z hp
  · have hn0 : 0 < n := by
      have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      have hnr : (0 : ℝ) < n := (mul_pos hη hNr).trans_le hn
      exact_mod_cast hnr
    have hσ0 : 0 ≤ criticalSigmaSq ϑ N := hσ ▸ sigmaSq_nonneg (criticalBeta ϑ N)
    have hz : Collision.spatialRenewal (criticalSigmaSq ϑ N) n z ≤ 0 := by
      simpa only [Collision.hatGaussian, ite_eq_right hn0.ne', ite_eq_right hp, mul_zero] using
        hd (criticalSigmaSq ϑ N) hσ0 n hn0 z
    have hcoef : 0 ≤ (N / 4 : ℝ) * (N / Real.log N) := by
      have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
      positivity
    calc
      _ ≤ 0 := by simpa only [← mul_assoc, mul_zero] using mul_le_mul_of_nonneg_left hz hcoef
      _ ≤ _ := (mul_pos hC (Real.exp_pos _)).le

/-- The normalized walk has a Gaussian bound in macroscopic coordinates,
uniform on a bounded positive time slab and without any parity condition. -/
theorem exists_scaled_srwKernel_gaussian_interior {η T : ℝ}
    (hη : 0 < η) (hT : 0 < T) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ {N : ℕ}, 1 ≤ N → ∀ n : ℕ,
      η * N ≤ (n : ℝ) → (n : ℝ) ≤ T * N → ∀ z : Site,
      ((N : ℝ) / 4) * srwKernel n z ≤
        C * Real.exp (-c * ‖latticeRepresentative N z‖ ^ 2) := by
  obtain ⟨B, c, hB, hc, hb⟩ := srwKernel_gaussianBound_all_times
  refine ⟨B / η, c / (2 * (T + 1)), by positivity, by positivity, ?_⟩
  intro N hN n hn hnT z
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hraw : ‖siteToPlane z‖ ^ 2 = ((N : ℝ) / 2) * ‖latticeRepresentative N z‖ ^ 2 := by
    rw [norm_latticeRepresentative_sq]
    field_simp
  have hclock : (n : ℝ) + 1 ≤ (T + 1) * N := by linarith only [hnT, hN1]
  have hratio : (N : ℝ) / ((n : ℝ) + 1) ≤ 1 / η := by
    apply (div_le_div_iff₀ hden hη).mpr
    linarith only [hn]
  have hcoef : ((N : ℝ) / 4) * (B / ((n : ℝ) + 1)) ≤ B / η := by
    calc
      _ = (B / 4) * ((N : ℝ) / ((n : ℝ) + 1)) := by ring
      _ ≤ (B / 4) * (1 / η) := mul_le_mul_of_nonneg_left hratio (by positivity)
      _ ≤ B / η := by
        have he : (B / 4) * (1 / η) = (B / η) / 4 := by ring
        rw [he]
        have hp : 0 ≤ B / η := by positivity
        linarith only [hp]
  have hexp : -c * ‖siteToPlane z‖ ^ 2 / ((n : ℝ) + 1) ≤
      -(c / (2 * (T + 1))) * ‖latticeRepresentative N z‖ ^ 2 := by
    rw [hraw]
    apply (div_le_iff₀ hden).mpr
    have hh := mul_le_mul_of_nonneg_left hclock
      (div_nonneg (mul_nonneg hc.le (sq_nonneg ‖latticeRepresentative N z‖))
        (by positivity : (0 : ℝ) ≤ 2 * (T + 1)))
    have he : (c * ‖latticeRepresentative N z‖ ^ 2 / (2 * (T + 1))) * ((T + 1) * N) =
        c * ((N : ℝ) / 2) * ‖latticeRepresentative N z‖ ^ 2 := by
      field_simp

    rw [he] at hh
    convert neg_le_neg hh using 1 <;> ring
  calc
    _ ≤ ((N : ℝ) / 4) * (B / ((n : ℝ) + 1) *
        Real.exp (-c * ‖siteToPlane z‖ ^ 2 / ((n : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left (hb n z) (by positivity)
    _ = (((N : ℝ) / 4) * (B / ((n : ℝ) + 1))) *
        Real.exp (-c * ‖siteToPlane z‖ ^ 2 / ((n : ℝ) + 1)) := by ring
    _ ≤ _ := mul_le_mul hcoef (Real.exp_le_exp.mpr hexp) (Real.exp_nonneg _) (by positivity)

/-- The shifted sample remains within twice the mesh of the original
point when the lattice shift has norm at most one. -/
theorem norm_sub_shifted_sample_le {N : ℕ} (hN : 0 < N) (k : ℕ)
    (p : Plane) (a : Site) (ha : ‖siteToPlane a‖ ≤ 1)
    (hmesh : (Real.sqrt ((N : ℝ) / 2))⁻¹ ≤ 1) :
    ‖p - latticeRepresentative N (pairTwoFutureSampleSite N k p + a)‖ ≤ 2 := by
  have hs : ‖latticeRepresentative N a‖ ≤ 1 := by
    rw [latticeRepresentative, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    exact (mul_le_mul_of_nonneg_left ha (by positivity)).trans (by simpa only [mul_one] using hmesh)
  rw [latticeRepresentative_add]
  calc
    _ = ‖(p - latticeRepresentative N (pairTwoFutureSampleSite N k p)) -
        latticeRepresentative N a‖ := by congr 1; abel
    _ ≤ ‖p - latticeRepresentative N (pairTwoFutureSampleSite N k p)‖ +
        ‖latticeRepresentative N a‖ := norm_sub_le _ _
    _ ≤ 2 := by
      have hp := (norm_sub_pairTwoFutureSampleSite_le hN k p).trans hmesh
      linarith only [hp, hs]

/-- A bounded moving starting point and bounded lattice phase shift give
one fixed macroscopic displacement error for an entrance Gaussian. -/
theorem norm_sub_shifted_sample_displacement_le {N : ℕ} (hN : 0 < N) (k : ℕ)
    (p : Plane) (a x : Site) {R : ℝ} (ha : ‖siteToPlane a‖ ≤ 1)
    (hx : ‖latticeRepresentative N x‖ ≤ R)
    (hmesh : (Real.sqrt ((N : ℝ) / 2))⁻¹ ≤ 1) :
    ‖p - latticeRepresentative N (pairTwoFutureSampleSite N k p + a - x)‖ ≤ R + 2 := by
  rw [latticeRepresentative_sub]
  calc
    _ = ‖(p - latticeRepresentative N (pairTwoFutureSampleSite N k p + a)) +
        latticeRepresentative N x‖ := by congr 1; abel
    _ ≤ ‖p - latticeRepresentative N (pairTwoFutureSampleSite N k p + a)‖ +
        ‖latticeRepresentative N x‖ := norm_add_le _ _
    _ ≤ R + 2 := by
      have hp := norm_sub_shifted_sample_le hN k p a ha hmesh
      linarith only [hp, hx]

/-- Independently phased samples approximate a continuum increment within
twice the mesh, uniformly in both phase clocks. -/
theorem norm_sub_sample_increment_le {N : ℕ} (hN : 0 < N) (k l : ℕ)
    (p q : Plane) (hmesh : (Real.sqrt ((N : ℝ) / 2))⁻¹ ≤ 1) :
    ‖(q - p) - latticeRepresentative N
      (pairTwoFutureSampleSite N l q - pairTwoFutureSampleSite N k p)‖ ≤ 2 := by
  rw [latticeRepresentative_sub]
  calc
    _ = ‖(q - latticeRepresentative N (pairTwoFutureSampleSite N l q)) -
        (p - latticeRepresentative N (pairTwoFutureSampleSite N k p))‖ := by congr 1; abel
    _ ≤ ‖q - latticeRepresentative N (pairTwoFutureSampleSite N l q)‖ +
        ‖p - latticeRepresentative N (pairTwoFutureSampleSite N k p)‖ := norm_sub_le _ _
    _ ≤ 2 := by
      have hp := (norm_sub_pairTwoFutureSampleSite_le hN k p).trans hmesh
      have hq := (norm_sub_pairTwoFutureSampleSite_le hN l q).trans hmesh
      linarith only [hp, hq]

end Critical2DKPZ.SHF.Moments
