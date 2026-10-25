/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.StringSum
public import Critical2DKPZ.Collision.SpatialRenewalHatGaussian
public import Critical2DKPZ.Collision.SpatialVarianceFar
public import Critical2DKPZ.Renewal.CriticalWindow
import Critical2DKPZ.OnePoint.CriticalGap
import Critical2DKPZ.SHF.Moments.PairBlockLocalLimit
import Mathlib.Tactic

/-! # Gaussian bounds used by the closed-string comparison -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.Blocks

open Filter
open MeasureTheory

/-- Walk kernels, their convolutions and weighted squared differences admit common Gaussian bounds,
and spatial renewal kernels admit bounds proportional to their total mass. -/
theorem exists_stringGaussian_bounds :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, 0 < c → c ≤ c₀ →
      ∃ Cwalk Crenewal : ℝ, 1 ≤ Cwalk ∧ 1 ≤ Crenewal ∧
        0 < Cwalk ∧ 0 < Crenewal ∧
        (∀ n x, srwKernel n x ≤ Cwalk * Collision.hatGaussian c n x) ∧
        (∀ k l : ℕ, ∀ y : Site,
          ∑' x, Collision.hatGaussian c k x * Collision.hatGaussian c l (y - x) ≤
            Cwalk * Collision.hatGaussian c (k + l) y) ∧
        (∀ k l : ℕ, 0 < k → k < l → ∀ w : Site,
          ∑' y, Collision.hatGaussian c k y *
            (srwKernel (l - k) (w - y) - srwKernel l w) ^ 2 ≤
              Cwalk * k / (l * (l - k)) * Collision.hatGaussian c l w) ∧
        (∀ σ2 : ℝ, 0 ≤ σ2 → ∀ n : ℕ, 1 ≤ n → ∀ x : Site,
          Collision.spatialRenewal σ2 n x ≤
            Crenewal * (∑' z, Collision.spatialRenewal σ2 n z) *
              Collision.hatGaussian c n x) := by
  obtain ⟨cG, hcG, hG⟩ := Collision.hatGaussian_bounds
  obtain ⟨cR, hcR, hR⟩ := Collision.spatialRenewal_le_hatGaussian_uniform
  let c₀ : ℝ := min cG cR
  have hc₀ : 0 < c₀ := by dsimp [c₀]; exact lt_min hcG hcR
  refine ⟨c₀, hc₀, ?_⟩
  intro c hc hcc
  obtain ⟨CG, hGkernel, hGconv, hGvar⟩ :=
    hG c hc (hcc.trans (min_le_left _ _))
  obtain ⟨CR₀, hCR₀, hRbound₀⟩ := hR c hc (hcc.trans (min_le_right _ _))
  let CR : ℝ := max CR₀ 1
  have hCR : 0 < CR := by dsimp [CR]; positivity
  have hmassNonneg (σ2 : ℝ) (hσ : 0 ≤ σ2) (n : ℕ) :
      0 ≤ ∑' z : Site, Collision.spatialRenewal σ2 n z := by
    rw [Critical2DKPZ.SHF.Moments.tsum_spatialRenewal_eq_renewalMass]
    apply Renewal.renewalMass_nonneg
    intro r
    exact mul_nonneg hσ (Critical2DKPZ.srwKernel_nonneg _ _)
  have hRbound : ∀ σ2 : ℝ, 0 ≤ σ2 → ∀ n : ℕ, 1 ≤ n → ∀ x : Site,
      Collision.spatialRenewal σ2 n x ≤
        CR * (∑' z, Collision.spatialRenewal σ2 n z) * Collision.hatGaussian c n x := by
    intro σ2 hσ n hn x
    have hm := hmassNonneg σ2 hσ n
    have hg : 0 ≤ Collision.hatGaussian c n x := Collision.hatGaussian_nonneg n x
    calc
      Collision.spatialRenewal σ2 n x ≤
          CR₀ * (∑' z, Collision.spatialRenewal σ2 n z) * Collision.hatGaussian c n x :=
        hRbound₀ σ2 hσ n hn x
      _ ≤ CR * (∑' z, Collision.spatialRenewal σ2 n z) * Collision.hatGaussian c n x := by
        calc
          _ = CR₀ * ((∑' z, Collision.spatialRenewal σ2 n z) *
              Collision.hatGaussian c n x) := by ring
          _ ≤ CR * ((∑' z, Collision.spatialRenewal σ2 n z) *
              Collision.hatGaussian c n x) :=
            mul_le_mul_of_nonneg_right (le_max_left CR₀ 1) (mul_nonneg hm hg)
          _ = _ := by ring
  let CK : ℝ := max CG 1
  have hCKone : 1 ≤ CK := le_max_right CG 1
  have hCK : 0 < CK := by dsimp [CK]; positivity
  have hCRone : 1 ≤ CR := le_max_right CR₀ 1
  have hkernel : ∀ n x, srwKernel n x ≤ CK * Collision.hatGaussian c n x := by
    intro n x
    exact (hGkernel n x).trans (mul_le_mul_of_nonneg_right
      (le_max_left CG 1) (Collision.hatGaussian_nonneg n x))
  have hconv : ∀ k l : ℕ, ∀ y : Site,
      ∑' x, Collision.hatGaussian c k x * Collision.hatGaussian c l (y - x) ≤
        CK * Collision.hatGaussian c (k + l) y := by
    intro k l y
    exact (hGconv k l y).trans (mul_le_mul_of_nonneg_right
      (le_max_left CG 1) (Collision.hatGaussian_nonneg (k + l) y))
  have hvar : ∀ k l : ℕ, 0 < k → k < l → ∀ w : Site,
      ∑' y, Collision.hatGaussian c k y *
        (srwKernel (l - k) (w - y) - srwKernel l w) ^ 2 ≤
          CK * k / (l * (l - k)) * Collision.hatGaussian c l w := by
    intro k l hk hkl w
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
    have hlR : 0 < (l : ℝ) := by exact_mod_cast (lt_trans hk hkl)
    have hklR : (k : ℝ) < (l : ℝ) := by exact_mod_cast hkl
    have hdiffR : 0 < (l : ℝ) - (k : ℝ) := sub_pos.mpr hklR
    have hcoef : 0 ≤ (k : ℝ) / ((l : ℝ) * ((l : ℝ) - (k : ℝ))) :=
      div_nonneg hkR.le (mul_nonneg hlR.le hdiffR.le)
    have hhat := Collision.hatGaussian_nonneg (c := c) l w
    calc
      _ ≤ CG * (k : ℝ) / ((l : ℝ) * ((l : ℝ) - (k : ℝ))) * Collision.hatGaussian c l w :=
        hGvar k l hk hkl w
      _ ≤ CK * (k : ℝ) / ((l : ℝ) * ((l : ℝ) - (k : ℝ))) * Collision.hatGaussian c l w := by
        calc
          _ = (CG * ((k : ℝ) / ((l : ℝ) * ((l : ℝ) - (k : ℝ))))) *
              Collision.hatGaussian c l w := by ring
          _ ≤ (CK * ((k : ℝ) / ((l : ℝ) * ((l : ℝ) - (k : ℝ))))) *
              Collision.hatGaussian c l w := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_left CG 1) hcoef) hhat
          _ = _ := by ring
  exact ⟨CK, CR, hCKone, hCRone, hCK, hCR, hkernel, hconv, hvar, hRbound⟩

/-- The spatial-renewal envelope also covers its zero-gap atom. -/
theorem spatialRenewal_le_hatGaussian_all {c C : ℝ} (hC : 1 ≤ C)
    (hbound : ∀ σ2 : ℝ, 0 ≤ σ2 → ∀ n : ℕ, 1 ≤ n → ∀ x : Site,
      Collision.spatialRenewal σ2 n x ≤
        C * (∑' z, Collision.spatialRenewal σ2 n z) * Collision.hatGaussian c n x)
    (σ2 : ℝ) (hσ : 0 ≤ σ2) (n : ℕ) (x : Site) :
    Collision.spatialRenewal σ2 n x ≤
      C * (∑' z, Collision.spatialRenewal σ2 n z) * Collision.hatGaussian c n x := by
  by_cases hn : n = 0
  · subst n
    by_cases hx : x = 0
    · simp [Collision.spatialRenewal_zero, Collision.hatGaussian, hx, tsum_ite_eq]
      exact hC
    · simp [Collision.spatialRenewal_zero, Collision.hatGaussian, hx, tsum_ite_eq]
  · exact hbound σ2 hσ n (Nat.one_le_iff_ne_zero.mpr hn) x

/-- For bounded critical-window parameters and sufficiently large scales, the critical coupling has variance equal to the critical renewal parameter. -/
theorem eventually_sigmaSq_criticalBeta_eq (A : ℝ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ ϑ ∈ Set.Icc (-A) A,
      Polymer.sigmaSq (Critical2DKPZ.criticalBeta ϑ N) = Critical2DKPZ.criticalSigmaSq ϑ N := by
  let A₀ : ℝ := max A 0
  have hlog : ∀ᶠ N : ℕ in Filter.atTop, A₀ < Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop A₀
  filter_upwards [eventually_ge_atTop 1, hlog] with N hN hNlog
  intro ϑ hϑ
  have hϑabs : |ϑ| ≤ A := abs_le.mpr hϑ
  have hlogϑ : |ϑ| < Real.log (N : ℝ) := lt_of_le_of_lt
    (hϑabs.trans (le_max_left A 0)) hNlog
  unfold Polymer.sigmaSq
  exact Critical2DKPZ.OnePoint.criticalBeta_spec_of_abs_lt_log hN hlogϑ

/-- The Gaussian envelope is pointwise at most one. -/
theorem hatGaussian_le_one {c : ℝ} (hc : 0 < c) (n : ℕ) (x : Site) :
    Collision.hatGaussian c n x ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    by_cases hx : x = 0 <;> simp [Collision.hatGaussian, hx]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
    exact (Collision.hatGaussian_le_inv hc hn1 x).trans ((inv_le_one₀ (by positivity)).2 hnR)

/-- The total spatial mass of the critical spatial renewal is the scalar renewal mass. -/
theorem tsum_spatialRenewal_eq_criticalRenewalMass (ϑ : ℝ) (N n : ℕ) :
    ∑' z : Site, Collision.spatialRenewal (Critical2DKPZ.criticalSigmaSq ϑ N) n z =
      _root_.Critical2DKPZ.Renewal.criticalRenewalMass ϑ N n := by
  rw [Critical2DKPZ.SHF.Moments.tsum_spatialRenewal_eq_renewalMass]
  rfl

/-- The squared walk kernel has a Gaussian upper bound with an inverse-time factor. -/
theorem srwKernel_sq_le_hatGaussian_inv {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    {n : ℕ} (hn : 1 ≤ n) (hkernel : ∀ n x, srwKernel n x ≤ C * Collision.hatGaussian c n x)
    (x : Site) :
    srwKernel n x ^ 2 ≤ C ^ 2 * (n : ℝ)⁻¹ * Collision.hatGaussian c n x := by
  have hq : 0 ≤ srwKernel n x := Critical2DKPZ.srwKernel_nonneg _ _
  have hg : 0 ≤ Collision.hatGaussian c n x := Collision.hatGaussian_nonneg n x
  have hgi := Collision.hatGaussian_le_inv hc hn x
  have henv := hkernel n x
  calc
    srwKernel n x ^ 2 = srwKernel n x * srwKernel n x := by ring
    _ ≤ (C * Collision.hatGaussian c n x) * srwKernel n x :=
      mul_le_mul_of_nonneg_right henv hq
    _ ≤ (C * Collision.hatGaussian c n x) * (C * Collision.hatGaussian c n x) :=
      mul_le_mul_of_nonneg_left henv (mul_nonneg hC hg)
    _ = C ^ 2 * (Collision.hatGaussian c n x) ^ 2 := by ring
    _ ≤ C ^ 2 * ((n : ℝ)⁻¹ * Collision.hatGaussian c n x) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
      calc
        Collision.hatGaussian c n x ^ 2 =
            Collision.hatGaussian c n x * Collision.hatGaussian c n x := by ring
        _ ≤ (n : ℝ)⁻¹ * Collision.hatGaussian c n x :=
          mul_le_mul_of_nonneg_right hgi hg
    _ = C ^ 2 * (n : ℝ)⁻¹ * Collision.hatGaussian c n x := by ring

end Critical2DKPZ.Blocks

end
