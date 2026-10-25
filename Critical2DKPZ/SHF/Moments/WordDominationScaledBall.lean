/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.FutureProfiles.HelperGeometry
public import Critical2DKPZ.MomentBounds.CSZ25AssemblyLemmas
public import Critical2DKPZ.RandomWalk.GaussianBridge
import Mathlib.Tactic

/-! # Finite lattice supports for scaled compact tests -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.FutureProfiles Critical2DKPZ.MomentBounds

/-- Finite sites in the macroscopic radius `R + 2` ball at scale `N`. -/
def collisionWordScaledBallSites (N : ℕ) (R : ℝ) : Finset Site :=
  (boxSites ⌈(R + 2) * Real.sqrt (N : ℝ)⌉₊).filter
    (fun y => ‖siteToPlane y‖ ≤ (R + 2) * Real.sqrt (N : ℝ))

private theorem abs_siteToPlane_apply_le_norm (z : Site) (i : Fin 2) :
    |(siteToPlane z i : ℝ)| ≤ ‖siteToPlane z‖ := by
  have hsquare : |(siteToPlane z i : ℝ)| ^ 2 ≤ ‖siteToPlane z‖ ^ 2 := by
    have hcoord : (siteToPlane z i : ℝ) ^ 2 ≤ ‖siteToPlane z‖ ^ 2 := by
      rw [Critical2DKPZ.norm_siteToPlane_sq]
      fin_cases i
      · exact le_add_of_nonneg_right (sq_nonneg (siteToPlane z 1))
      · exact le_add_of_nonneg_left (sq_nonneg (siteToPlane z 0))
    simpa only [sq_abs] using hcoord
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp hsquare

/-- A point in the scaled radius `R + 2` ball belongs to the finite support
set used for the CCR boundary profiles. -/
theorem mem_collisionWordScaledBallSites_of_scaledNorm {N : ℕ} (hN : 1 ≤ N)
    {R : ℝ} (hR : 0 ≤ R) (z : Site)
    (hz : ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z‖ ≤ R + 2) :
    z ∈ collisionWordScaledBallSites N R := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hscale : 0 < Real.sqrt ((N : ℝ) / 2) := by positivity
  have hscaleSq : (Real.sqrt ((N : ℝ) / 2)) ^ 2 = (N : ℝ) / 2 :=
    Real.sq_sqrt (by positivity)
  have hzscaled : (Real.sqrt ((N : ℝ) / 2))⁻¹ * ‖siteToPlane z‖ ≤ R + 2 := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hscale.le)] using hz
  have hzraw : ‖siteToPlane z‖ ≤ (R + 2) * Real.sqrt (N : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hzscaled hscale.le
    have hcancel : (Real.sqrt ((N : ℝ) / 2))⁻¹ *
        ‖siteToPlane z‖ * Real.sqrt ((N : ℝ) / 2) = ‖siteToPlane z‖ := by
      field_simp [ne_of_gt hscale]
    have hroot : Real.sqrt ((N : ℝ) / 2) ≤ Real.sqrt (N : ℝ) := by
      apply Real.sqrt_le_sqrt
      nlinarith
    calc
      ‖siteToPlane z‖ =
          (Real.sqrt ((N : ℝ) / 2))⁻¹ * ‖siteToPlane z‖ *
            Real.sqrt ((N : ℝ) / 2) := hcancel.symm
      _ ≤ (R + 2) * Real.sqrt ((N : ℝ) / 2) := hmul
      _ ≤ (R + 2) * Real.sqrt (N : ℝ) :=
        mul_le_mul_of_nonneg_left hroot (by linarith)
  have hr : 1 ≤ (R + 2) * Real.sqrt (N : ℝ) := by
    have hsqrt : 1 ≤ Real.sqrt (N : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hNreal
    nlinarith
  have hceil : (R + 2) * Real.sqrt (N : ℝ) ≤
      (⌈(R + 2) * Real.sqrt (N : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have hcoord (i : Fin 2) : |(z i : ℝ)| ≤
      (⌈(R + 2) * Real.sqrt (N : ℝ)⌉₊ : ℝ) := by
    calc
      |(z i : ℝ)| = |(siteToPlane z i : ℝ)| := by simp [siteToPlane]
      _ ≤ ‖siteToPlane z‖ := abs_siteToPlane_apply_le_norm z i
      _ ≤ (R + 2) * Real.sqrt (N : ℝ) := hzraw
      _ ≤ _ := hceil
  have hcoordInt (i : Fin 2) : |z i| ≤ (⌈(R + 2) * Real.sqrt (N : ℝ)⌉₊ : ℤ) := by
    have h := hcoord i
    exact_mod_cast h
  have hbox : z ∈ boxSites ⌈(R + 2) * Real.sqrt (N : ℝ)⌉₊ := by
    simp only [boxSites, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    exact abs_le.mp (hcoordInt i)
  exact Finset.mem_filter.mpr ⟨hbox, hzraw⟩

/-- The scaled support set has quadratic size in the macroscopic radius and
linear size in the lattice horizon. -/
theorem card_collisionWordScaledBallSites_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ}, 1 ≤ N → ∀ {R : ℝ}, 0 ≤ R →
      (((collisionWordScaledBallSites N R).card : ℝ) ≤ C * (R + 2) ^ 2 * N) := by
  obtain ⟨C, hC⟩ := card_ball_sites_le
  have hCnonneg : 0 ≤ C := by
    have h := hC 1 (by norm_num)
    have hcard : 0 ≤ (((boxSites ⌈(1 : ℝ)⌉₊).filter
        fun y => ‖siteToPlane y‖ ≤ (1 : ℝ)).card : ℝ) := Nat.cast_nonneg _
    nlinarith
  refine ⟨C, hCnonneg, ?_⟩
  intro N hN R hR
  let r : ℝ := (R + 2) * Real.sqrt (N : ℝ)
  have hr : 1 ≤ r := by
    dsimp [r]
    have hsqrt : 1 ≤ Real.sqrt (N : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hN : (1 : ℝ) ≤ N)
    nlinarith
  have hbound := hC r hr
  have hcard : (((collisionWordScaledBallSites N R).card : ℝ) ≤ C * r ^ 2) := by
    simpa [collisionWordScaledBallSites, r] using hbound
  have hrpow : r ^ 2 = (R + 2) ^ 2 * (N : ℝ) := by
    dsimp [r]
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  rw [hrpow] at hcard
  calc
    (((collisionWordScaledBallSites N R).card : ℝ)) ≤ C * ((R + 2) ^ 2 * N) := hcard
    _ = C * (R + 2) ^ 2 * N := by ring

end Critical2DKPZ.SHF.Moments

end
