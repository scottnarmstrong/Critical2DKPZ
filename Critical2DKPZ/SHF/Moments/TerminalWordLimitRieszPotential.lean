/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.HeatPotential
public import Critical2DKPZ.SHF.DeltaBose.BlockTransport

/-! # A heat-potential majorant for inverse distance -/

@[expose] public section

open Filter MeasureTheory
open Set
open scoped BigOperators CompactlySupported Topology ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

private theorem heatPotentialIntegrand_scale {c : ℝ} (hc : 0 < c) (u : ℝ)
    (hu : 0 < u) (z : Plane) :
    Critical2DKPZ.DeltaBose.heatPotentialIntegrand (c ^ 2 * u) (c • z) =
      ENNReal.ofReal (c⁻¹ * (c ^ 2)⁻¹) *
        Critical2DKPZ.DeltaBose.heatPotentialIntegrand u z := by
  have hsqrt : Real.sqrt (c ^ 2) = c := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hc]
  have hkernel : heatKernel (c ^ 2 * u) (c • z) = (c ^ 2)⁻¹ * heatKernel u z := by
    simpa [hsqrt] using
      (Critical2DKPZ.DeltaBose.heatKernel_scale (a := c ^ 2) (t := u)
        (sq_pos_of_pos hc) z)
  have hrpow : (c ^ 2 * u) ^ (-(1 / 2 : ℝ)) = c⁻¹ * u ^ (-(1 / 2 : ℝ)) := by
    rw [Real.mul_rpow (sq_nonneg c) hu.le, Real.rpow_neg (sq_nonneg c)]
    rw [← Real.sqrt_eq_rpow, hsqrt]
  have hcoef : 0 ≤ c⁻¹ * (c ^ 2)⁻¹ := by positivity
  have hpow : 0 ≤ u ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hu.le _
  have hker : 0 ≤ heatKernel u z := (Critical2DKPZ.heatKernel_pos hu z).le
  unfold Critical2DKPZ.DeltaBose.heatPotentialIntegrand
  rw [hrpow, hkernel]
  calc
    ENNReal.ofReal (c⁻¹ * u ^ (-(1 / 2 : ℝ))) *
        ENNReal.ofReal ((c ^ 2)⁻¹ * heatKernel u z) =
        ENNReal.ofReal
          ((c⁻¹ * u ^ (-(1 / 2 : ℝ))) * ((c ^ 2)⁻¹ * heatKernel u z)) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (c⁻¹ * (c ^ 2)⁻¹) *
          (ENNReal.ofReal (u ^ (-(1 / 2 : ℝ))) * ENNReal.ofReal (heatKernel u z)) := by
      calc
        _ = ENNReal.ofReal
            ((c⁻¹ * (c ^ 2)⁻¹) * (u ^ (-(1 / 2 : ℝ)) * heatKernel u z)) := by
              congr 1
              ring
        _ = _ := by
          rw [ENNReal.ofReal_mul hcoef, ENNReal.ofReal_mul hpow]

private theorem heatPotential_scale {c : ℝ} (hc : 0 < c) (z : Plane) :
    Critical2DKPZ.DeltaBose.heatPotential (c • z) =
      ENNReal.ofReal c⁻¹ * Critical2DKPZ.DeltaBose.heatPotential z := by
  rw [Critical2DKPZ.DeltaBose.heatPotential, lintegral_Ioi_mul (sq_pos_of_pos hc)]
  have hb : 0 ≤ c⁻¹ * (c ^ 2)⁻¹ := by positivity
  calc
    ENNReal.ofReal (c ^ 2) *
        (∫⁻ u in Ioi 0, heatPotentialIntegrand (c ^ 2 * u) (c • z)) =
        ENNReal.ofReal (c ^ 2) *
          (∫⁻ u in Ioi 0,
            ENNReal.ofReal (c⁻¹ * (c ^ 2)⁻¹) * heatPotentialIntegrand u z) := by
              congr 1
              apply lintegral_congr_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
              exact heatPotentialIntegrand_scale hc u hu z
    _ = ENNReal.ofReal (c ^ 2) *
          (ENNReal.ofReal (c⁻¹ * (c ^ 2)⁻¹) *
            (∫⁻ u in Ioi 0, heatPotentialIntegrand u z)) := by
              rw [lintegral_const_mul' _ _
                (ENNReal.ofReal_ne_top (r := c⁻¹ * (c ^ 2)⁻¹))]
    _ = ENNReal.ofReal c⁻¹ * heatPotential z := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg c)]
      have hreal : c ^ 2 * (c⁻¹ * (c ^ 2)⁻¹) = c⁻¹ := by
        field_simp
      rw [hreal]
      rw [Critical2DKPZ.DeltaBose.heatPotential]

private theorem heatPotential_eq_of_norm_eq {x y : Plane} (h : ‖x‖ = ‖y‖) :
    Critical2DKPZ.DeltaBose.heatPotential x = Critical2DKPZ.DeltaBose.heatPotential y := by
  unfold Critical2DKPZ.DeltaBose.heatPotential
  apply lintegral_congr
  intro s
  unfold Critical2DKPZ.DeltaBose.heatPotentialIntegrand Critical2DKPZ.heatKernel
  rw [h]

theorem exists_ofReal_inv_norm_le_heatPotential :
    ∃ C : ℝ, 0 < C ∧ ∀ z : Plane,
      ENNReal.ofReal (‖z‖⁻¹) ≤ ENNReal.ofReal C * heatPotential z := by
  obtain ⟨e, he⟩ : ∃ e : Plane, e ≠ 0 := exists_ne (0 : Plane)
  have he_norm : 0 < ‖e‖ := norm_pos_iff.mpr he
  let u₀ : Plane := ‖e‖⁻¹ • e
  have hu₀ : ‖u₀‖ = 1 := by
    dsimp [u₀]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact inv_mul_cancel₀ he_norm.ne'
  let κ : ℝ≥0∞ := heatPotential u₀
  have hκpos : 0 < κ := heatPotential_pos u₀
  obtain ⟨C, hCpos, hCκ⟩ : ∃ C : ℝ, 0 < C ∧ 1 ≤ ENNReal.ofReal C * κ := by
    by_cases hκtop : κ = ⊤
    · refine ⟨1, by norm_num, ?_⟩
      simp [hκtop]
    · have hκzero : κ ≠ 0 := ne_of_gt hκpos
      have hκreal : 0 < κ.toReal := ENNReal.toReal_pos hκzero hκtop
      have hκeq : κ = ENNReal.ofReal κ.toReal := (ENNReal.ofReal_toReal hκtop).symm
      refine ⟨κ.toReal⁻¹, inv_pos.mpr hκreal, ?_⟩
      calc
        1 = ENNReal.ofReal 1 := by simp
        _ = ENNReal.ofReal (κ.toReal⁻¹ * κ.toReal) := by
          congr 1
          exact (inv_mul_cancel₀ hκreal.ne').symm
        _ ≤ ENNReal.ofReal (κ.toReal⁻¹) * κ := by
          rw [ENNReal.ofReal_mul (inv_nonneg.mpr hκreal.le), ← hκeq]
  refine ⟨C, hCpos, ?_⟩
  intro z
  by_cases hz : z = 0
  · subst z
    simp
  · have hc : 0 < ‖z‖ := norm_pos_iff.mpr hz
    let u : Plane := ‖z‖⁻¹ • z
    have hu : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
      exact inv_mul_cancel₀ hc.ne'
    have huκ : heatPotential u = κ := by
      apply heatPotential_eq_of_norm_eq
      rw [hu, hu₀]
    have hzdecomp : z = ‖z‖ • u := by
      dsimp [u]
      rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
    have hzpot : heatPotential z = ENNReal.ofReal ‖z‖⁻¹ * κ := by
      calc
        heatPotential z = heatPotential (‖z‖ • u) := congrArg heatPotential hzdecomp
        _ = ENNReal.ofReal ‖z‖⁻¹ * κ := by rw [heatPotential_scale hc, huκ]
    rw [hzpot]
    calc
      ENNReal.ofReal ‖z‖⁻¹ = ENNReal.ofReal ‖z‖⁻¹ * 1 := by simp
      _ ≤ ENNReal.ofReal ‖z‖⁻¹ * (ENNReal.ofReal C * κ) :=
        by gcongr
      _ = ENNReal.ofReal C * (ENNReal.ofReal ‖z‖⁻¹ * κ) := by ac_rfl

end Critical2DKPZ.SHF.Moments
