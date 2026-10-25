/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Collision.SpatialRenewalComposition
public import Critical2DKPZ.Collision.SpatialVarianceFar
public import Critical2DKPZ.Lattice.Basic
import Mathlib.Tactic

/-! # Gaussian bounds for spatial renewal compositions -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.Collision

open Critical2DKPZ.WalkTails
open Polymer

/-- A squared-kernel composition has a planar Gaussian envelope with its exact total mass. -/
theorem squareConvolution_le_hatGaussian :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, 0 < c → c ≤ c₀ → ∃ C : ℝ, 0 < C ∧
      ∀ ks : List ℕ, 0 < ks.sum →
        ∀ x : Site, squareConvolution ks x ≤
          C * (ks.map fun k => srwKernel (2 * k) 0).prod * hatGaussian c ks.sum x := by
  obtain ⟨Cb, cb, hCb, hcb, hbin⟩ := squaredBinomialConvolution_le_localGaussian
  refine ⟨2 * cb, by positivity, fun c hc hcc => ?_⟩
  refine ⟨Cb ^ 2, by positivity, ?_⟩
  intro ks hn x
  have hnR : 0 < (ks.sum : ℝ) := by exact_mod_cast hn
  by_cases hpar : Even ((ks.sum : ℤ) + x 0 + x 1)
  · have hpar₂ : Even ((ks.sum : ℤ) + x 0 - x 1) := by
      rcases hpar with ⟨m, hm⟩
      refine ⟨m - x 1, ?_⟩
      nlinarith
    let j₁ : ℤ := ((ks.sum : ℤ) + x 0 + x 1) / 2
    let j₂ : ℤ := ((ks.sum : ℤ) + x 0 - x 1) / 2
    have hj₁ : 2 * j₁ = (ks.sum : ℤ) + x 0 + x 1 := by
      exact Int.two_mul_ediv_two_of_even hpar
    have hj₂ : 2 * j₂ = (ks.sum : ℤ) + x 0 - x 1 := by
      exact Int.two_mul_ediv_two_of_even hpar₂
    have hlocal₁ := hbin ks hn j₁
    have hlocal₂ := hbin ks hn j₂
    have hA0 : 0 ≤ squaredBinomialConvolution ks j₁ :=
      squaredBinomialConvolution_nonneg ks j₁
    have hB0 : 0 ≤ squaredBinomialConvolution ks j₂ :=
      squaredBinomialConvolution_nonneg ks j₂
    have hnorm :
        (2 * (j₁ : ℝ) - ks.sum) ^ 2 + (2 * (j₂ : ℝ) - ks.sum) ^ 2 =
          2 * ‖siteToPlane x‖ ^ 2 := by
      have hj₁R : 2 * (j₁ : ℝ) - ks.sum = (x 0 : ℝ) + x 1 := by
        have hInt : 2 * j₁ - (ks.sum : ℤ) = x 0 + x 1 := by linarith [hj₁]
        have hReal := congrArg (fun z : ℤ => (z : ℝ)) hInt
        simpa only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
          Int.cast_natCast] using hReal
      have hj₂R : 2 * (j₂ : ℝ) - ks.sum = (x 0 : ℝ) - x 1 := by
        have hInt : 2 * j₂ - (ks.sum : ℤ) = x 0 - x 1 := by linarith [hj₂]
        have hReal := congrArg (fun z : ℤ => (z : ℝ)) hInt
        simpa only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
          Int.cast_natCast] using hReal
      rw [hj₁R, hj₂R, Critical2DKPZ.norm_siteToPlane_sq]
      ring
    have hP : 0 ≤ (ks.map fun k => srwKernel (2 * k) 0).prod := by
      apply List.prod_nonneg
      intro q hq
      obtain ⟨k, hk, hq⟩ := List.mem_map.mp hq
      rw [← hq]
      exact _root_.Critical2DKPZ.srwKernel_nonneg (2 * k) 0
    have hprodlocal :
        squaredBinomialConvolution ks j₁ * squaredBinomialConvolution ks j₂ ≤
          (Cb / Real.sqrt ks.sum *
              Real.exp (-cb * (2 * (j₁ : ℝ) - ks.sum) ^ 2 / ks.sum)) *
            (Cb / Real.sqrt ks.sum *
              Real.exp (-cb * (2 * (j₂ : ℝ) - ks.sum) ^ 2 / ks.sum)) := by
      exact mul_le_mul hlocal₁ hlocal₂ hB0 (by positivity)
    have hfactor := squareConvolution_eq ks x j₁ j₂ hj₁ hj₂
    rw [hfactor]
    have hexpArg :
        -cb * (2 * (j₁ : ℝ) - ks.sum) ^ 2 / ks.sum +
            -cb * (2 * (j₂ : ℝ) - ks.sum) ^ 2 / ks.sum =
          -2 * cb * ‖siteToPlane x‖ ^ 2 / ks.sum := by
      calc
        _ = (-cb / ks.sum) *
              ((2 * (j₁ : ℝ) - ks.sum) ^ 2 + (2 * (j₂ : ℝ) - ks.sum) ^ 2) := by ring
        _ = (-cb / ks.sum) * (2 * ‖siteToPlane x‖ ^ 2) := by rw [hnorm]
        _ = _ := by ring
    have hexp :
        Real.exp (-cb * (2 * (j₁ : ℝ) - ks.sum) ^ 2 / ks.sum) *
            Real.exp (-cb * (2 * (j₂ : ℝ) - ks.sum) ^ 2 / ks.sum) =
          Real.exp (-2 * cb * ‖siteToPlane x‖ ^ 2 / ks.sum) := by
      rw [← Real.exp_add, hexpArg]
    have hexp_le :
        Real.exp (-2 * cb * ‖siteToPlane x‖ ^ 2 / ks.sum) ≤
          Real.exp (-c * ‖siteToPlane x‖ ^ 2 / ks.sum) := by
      apply Real.exp_le_exp.mpr
      apply div_le_div_of_nonneg_right _ (le_of_lt hnR)
      have hcc' : c ≤ 2 * cb := hcc
      have hsq : 0 ≤ ‖siteToPlane x‖ ^ 2 := sq_nonneg _
      nlinarith
    have hscale :
        (ks.map fun k => srwKernel (2 * k) 0).prod *
            (squaredBinomialConvolution ks j₁ * squaredBinomialConvolution ks j₂) ≤
          (Cb ^ 2) * (ks.map fun k => srwKernel (2 * k) 0).prod *
            ((ks.sum : ℝ)⁻¹ * Real.exp (-c * ‖siteToPlane x‖ ^ 2 / ks.sum)) := by
      have hsimp :
          (Cb / Real.sqrt ks.sum *
              Real.exp (-cb * (2 * (j₁ : ℝ) - ks.sum) ^ 2 / ks.sum)) *
            (Cb / Real.sqrt ks.sum *
              Real.exp (-cb * (2 * (j₂ : ℝ) - ks.sum) ^ 2 / ks.sum)) =
          Cb ^ 2 * (ks.sum : ℝ)⁻¹ *
            Real.exp (-2 * cb * ‖siteToPlane x‖ ^ 2 / ks.sum) := by
        calc
          _ = Cb ^ 2 * (Real.sqrt (ks.sum : ℝ))⁻¹ ^ 2 *
                (Real.exp (-cb * (2 * (j₁ : ℝ) - ks.sum) ^ 2 / ks.sum) *
                  Real.exp (-cb * (2 * (j₂ : ℝ) - ks.sum) ^ 2 / ks.sum)) := by ring
          _ = _ := by
            have hsqrtSq : Real.sqrt (ks.sum : ℝ) ^ 2 = ks.sum := Real.sq_sqrt hnR.le
            have hinv : (Real.sqrt (ks.sum : ℝ))⁻¹ ^ 2 = (ks.sum : ℝ)⁻¹ := by
              calc
                _ = ((Real.sqrt (ks.sum : ℝ)) ^ 2)⁻¹ := by ring
                _ = _ := by rw [hsqrtSq]
            rw [hexp, hinv]
      have hraw := mul_le_mul_of_nonneg_left hprodlocal hP
      calc
        _ ≤ (ks.map fun k => srwKernel (2 * k) 0).prod *
            ((Cb / Real.sqrt ks.sum *
                Real.exp (-cb * (2 * (j₁ : ℝ) - ks.sum) ^ 2 / ks.sum)) *
              (Cb / Real.sqrt ks.sum *
                Real.exp (-cb * (2 * (j₂ : ℝ) - ks.sum) ^ 2 / ks.sum))) := hraw
        _ = (Cb ^ 2) * (ks.map fun k => srwKernel (2 * k) 0).prod *
            ((ks.sum : ℝ)⁻¹ * Real.exp (-2 * cb * ‖siteToPlane x‖ ^ 2 / ks.sum)) := by
              rw [hsimp]
              ring
        _ ≤ _ := by
          have hinner :
              (ks.sum : ℝ)⁻¹ * Real.exp (-2 * cb * ‖siteToPlane x‖ ^ 2 / ks.sum) ≤
                (ks.sum : ℝ)⁻¹ * Real.exp (-c * ‖siteToPlane x‖ ^ 2 / ks.sum) :=
            mul_le_mul_of_nonneg_left hexp_le (inv_nonneg.mpr hnR.le)
          calc
            _ = (Cb ^ 2) * (ks.map fun k => srwKernel (2 * k) 0).prod *
                ((ks.sum : ℝ)⁻¹ * Real.exp (-2 * cb * ‖siteToPlane x‖ ^ 2 / ks.sum)) := rfl
            _ ≤ _ := mul_le_mul_of_nonneg_left hinner (by positivity)
    calc
      _ = (ks.map fun k => srwKernel (2 * k) 0).prod *
          (squaredBinomialConvolution ks j₁ * squaredBinomialConvolution ks j₂) := by ring
      _ ≤ (Cb ^ 2) * (ks.map fun k => srwKernel (2 * k) 0).prod *
          ((ks.sum : ℝ)⁻¹ * Real.exp (-c * ‖siteToPlane x‖ ^ 2 / ks.sum)) := hscale
      _ = (Cb ^ 2) * (ks.map fun k => srwKernel (2 * k) 0).prod *
          hatGaussian c ks.sum x := by
            rw [hatGaussian, ite_eq_right (Nat.ne_of_gt hn), ite_eq_left hpar]
            ring
  · rw [squareConvolution_eq_zero_of_odd ks x hpar]
    have hP : 0 ≤ (ks.map fun k => srwKernel (2 * k) 0).prod := by
      apply List.prod_nonneg
      intro q hq
      obtain ⟨k, hk, hq⟩ := List.mem_map.mp hq
      rw [← hq]
      exact _root_.Critical2DKPZ.srwKernel_nonneg (2 * k) 0
    have hhat : 0 ≤ hatGaussian c ks.sum x := hatGaussian_nonneg _ _
    positivity

/-- The total renewal mass is the composition sum of the block return masses. -/
theorem tsum_spatialRenewal_eq_compositionMass (σ2 : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∑' x : Site, spatialRenewal σ2 n x =
      ∑ c : Composition n,
        σ2 ^ c.length * (c.blocks.map fun k => srwKernel (2 * k) 0).prod := by
  classical
  let E := Polymer.endpoints (0 : Site) n
  have hsupp (x : Site) (hx : x ∉ E) : spatialRenewal σ2 n x = 0 := by
    rw [spatialRenewal_eq_sum_compositions σ2 hn x]
    apply Finset.sum_eq_zero
    intro c hc
    have hx' : x ∉ Polymer.endpoints 0 c.blocks.sum := by
      rw [c.blocks_sum]
      exact hx
    have hz := squareConvolution_eq_zero_of_not_mem_endpoints hx'
    rw [hz]
    simp
  calc
    ∑' x : Site, spatialRenewal σ2 n x = ∑ x ∈ E, spatialRenewal σ2 n x :=
      tsum_eq_sum (s := E) hsupp
    _ = ∑ c : Composition n,
        σ2 ^ c.length * (c.blocks.map fun k => srwKernel (2 * k) 0).prod := by
      simp_rw [spatialRenewal_eq_sum_compositions σ2 hn]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c hc
      have hcsupp (x : Site) (hx : x ∉ E) : squareConvolution c.blocks x = 0 := by
        have hx' : x ∉ Polymer.endpoints 0 c.blocks.sum := by
          rw [c.blocks_sum]
          exact hx
        exact squareConvolution_eq_zero_of_not_mem_endpoints hx'
      calc
        ∑ x ∈ E, σ2 ^ c.length * squareConvolution c.blocks x =
            ∑' x : Site, σ2 ^ c.length * squareConvolution c.blocks x :=
          (tsum_eq_sum (s := E) (fun x hx => by rw [hcsupp x hx]; simp)).symm
        _ = σ2 ^ c.length * ∑' x : Site, squareConvolution c.blocks x := tsum_mul_left
        _ = σ2 ^ c.length * (c.blocks.map fun k => srwKernel (2 * k) 0).prod := by
          rw [tsum_squareConvolution]

/-- A uniform spatial Gaussian bound for the renewal profile, normalized by its total mass. -/
theorem spatialRenewal_le_hatGaussian_uniform :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, 0 < c → c ≤ c₀ → ∃ C : ℝ, 0 < C ∧
      ∀ σ2 : ℝ, 0 ≤ σ2 → ∀ n : ℕ, 1 ≤ n → ∀ x : Site,
        spatialRenewal σ2 n x ≤ C * (∑' z, spatialRenewal σ2 n z) * hatGaussian c n x := by
  obtain ⟨c₀, hc₀, hsquare⟩ := squareConvolution_le_hatGaussian
  refine ⟨c₀, hc₀, fun c hc hcc => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hsquare c hc hcc
  refine ⟨C, hC, ?_⟩
  intro σ2 hσ n hn x
  have hmass := tsum_spatialRenewal_eq_compositionMass σ2 hn
  rw [spatialRenewal_eq_sum_compositions σ2 hn x]
  calc
    (∑ c' : Composition n, σ2 ^ c'.length * squareConvolution c'.blocks x) ≤
        ∑ c' : Composition n,
          σ2 ^ c'.length *
            (C * (c'.blocks.map fun k => srwKernel (2 * k) 0).prod * hatGaussian c n x) := by
      apply Finset.sum_le_sum
      intro c' hc'
      have hweight : 0 ≤ σ2 ^ c'.length := pow_nonneg hσ _
      have hsum_pos : 0 < c'.blocks.sum := by
        rw [c'.blocks_sum]
        exact Nat.zero_lt_of_lt hn
      have hpiece := hbound c'.blocks hsum_pos x
      rw [c'.blocks_sum] at hpiece
      exact mul_le_mul_of_nonneg_left hpiece hweight
    _ = C * (∑ c' : Composition n,
          σ2 ^ c'.length * (c'.blocks.map fun k => srwKernel (2 * k) 0).prod) *
          hatGaussian c n x := by
      calc
        _ = ∑ c' : Composition n,
            (C * (σ2 ^ c'.length * (c'.blocks.map fun k => srwKernel (2 * k) 0).prod)) *
              hatGaussian c n x := by
          apply Finset.sum_congr rfl
          intro c' hc'
          ring
        _ = (∑ c' : Composition n,
              C * (σ2 ^ c'.length * (c'.blocks.map fun k => srwKernel (2 * k) 0).prod)) *
              hatGaussian c n x := (Finset.sum_mul ..).symm
        _ = _ := by rw [← Finset.mul_sum]
    _ = C * (∑' z : Site, spatialRenewal σ2 n z) * hatGaussian c n x := by
      rw [hmass]

/-- The critical-window spatial renewal bound follows from the uniform renewal estimate. -/
theorem spatialRenewal_le_hatGaussian (A D₁ : ℝ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, 0 < c → c ≤ c₀ → ∃ C : ℝ, ∀ᶠ N : ℕ in Filter.atTop,
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ D₁ * N → ∀ x : Site,
        spatialRenewal (Polymer.sigmaSq (Critical2DKPZ.criticalBeta ϑ N)) n x ≤
          C * (∑' z, spatialRenewal (Polymer.sigmaSq (Critical2DKPZ.criticalBeta ϑ N)) n z) *
          hatGaussian c n x := by
  obtain ⟨c₀, hc₀, huniform⟩ := spatialRenewal_le_hatGaussian_uniform
  refine ⟨c₀, hc₀, fun c hc hcc => ?_⟩
  obtain ⟨C, hC, hbound⟩ := huniform c hc hcc
  refine ⟨C, ?_⟩
  apply Filter.Eventually.of_forall
  intro N ϑ hϑ n hn hnN x
  exact hbound (Polymer.sigmaSq (Critical2DKPZ.criticalBeta ϑ N))
    (by
      unfold Polymer.sigmaSq
      exact sub_nonneg.mpr (Real.one_le_exp (sq_nonneg _))) n hn x

end Critical2DKPZ.Collision

end
