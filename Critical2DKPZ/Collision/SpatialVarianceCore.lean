/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Collision.SpatialGaussian
import Critical2DKPZ.Polymer.WalkKernel
import Critical2DKPZ.Lattice.Basic
import Critical2DKPZ.WalkTails.SameParityGradient
import Mathlib.Analysis.Convex.Jensen

/-! # Long-time variance estimates for the spatial walk envelope -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.Collision

open scoped BigOperators

private theorem expWeighted_le_inv {d x : ℝ} (hd : 0 < d) (hx : 0 ≤ x) :
    x * Real.exp (-d * x) ≤ d⁻¹ := by
  let u := d * x
  have hu : 0 ≤ u := mul_nonneg hd.le hx
  have huExp : u ≤ Real.exp u := by
    have h := Real.add_one_le_exp u
    linarith
  have hprod : u * Real.exp (-u) ≤ 1 := by
    calc
      u * Real.exp (-u) ≤ Real.exp u * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right huExp (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hcoeff : d⁻¹ * u = x := by
    dsimp [u]
    field_simp [ne_of_gt hd]
  have hexp : -d * x = -u := by dsimp [u]; ring
  calc
    _ = d⁻¹ * (u * Real.exp (-u)) := by rw [hexp, ← hcoeff]; ring
    _ ≤ d⁻¹ * 1 := mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr hd.le)
    _ = d⁻¹ := by ring

private theorem sq_le_two_sq_add {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (hxy : x ≤ y + z) : x ^ 2 ≤ 2 * y ^ 2 + 2 * z ^ 2 := by
  have hprod : 0 ≤ (y + z - x) * (y + z + x) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [hprod, sq_nonneg (y - z)]

private theorem weighted_norm_sq_le {c : ℝ} (hc : 0 ≤ c) (p q : Plane) :
    c * ‖p‖ ^ 2 ≤ c * (2 * ‖p - q‖ ^ 2 + 2 * ‖q‖ ^ 2) := by
  have htri : ‖p‖ ≤ ‖p - q‖ + ‖q‖ := by
    calc
      ‖p‖ = ‖(p - q) + q‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hnorm := sq_le_two_sq_add (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) htri
  exact mul_le_mul_of_nonneg_left hnorm hc

private theorem exp_product_rearrange {A B x y : ℝ} :
    (A * B) * (2 * x + 2 * y) = A * (2 * (x * B) + 2 * y * B) := by
  ring

private theorem summable_two_weighted {f g : Site → ℝ} (hf : Summable f)
    (hg : Summable g) (c d : ℝ) :
    Summable (fun x => c * (2 * f x + d * g x)) := by
  exact ((hf.mul_left 2).add (hg.mul_left d)).mul_left c

private theorem rawGaussian_twoRate_sum_bound {a b γ d μ δ₀ : ℝ} {k n : ℕ}
    (ha : 0 < a) (hδ₀ : 0 < δ₀) (hk : 1 ≤ k) (hn : 1 ≤ n)
    (hrate : a / ((k : ℝ) + n) ≤ γ)
    (hgap : δ₀ / ((k : ℝ) + n) ≤ γ - a / ((k : ℝ) + n))
    (hμnonneg : 0 ≤ μ)
    (hμBound : μ ≤ (b / a) * (k / ((k : ℝ) + n)))
    (w : Site) (v : Plane)
    (hnormV : ‖v‖ ^ 2 = μ ^ 2 * ‖siteToPlane w‖ ^ 2)
    (hpoint : ∀ x : Site,
      Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k -
          b * ‖siteToPlane (w - x)‖ ^ 2 / n) =
        Real.exp (-γ * ‖siteToPlane w‖ ^ 2) *
          Real.exp (-d * ‖siteToPlane x - v‖ ^ 2))
    (hshift0 : Summable (fun x : Site => Real.exp (-d * ‖siteToPlane x - v‖ ^ 2)))
    (hshift2 : Summable (fun x : Site => ‖siteToPlane x - v‖ ^ 2 *
      Real.exp (-d * ‖siteToPlane x - v‖ ^ 2)))
    (hS0 : (∑' x : Site, Real.exp (-d * ‖siteToPlane x - v‖ ^ 2)) ≤
      8 * (1 + Real.pi / a) * k)
    (hS2 : (∑' x : Site, ‖siteToPlane x - v‖ ^ 2 *
      Real.exp (-d * ‖siteToPlane x - v‖ ^ 2)) ≤
      16 / a * (1 + 2 * Real.pi / a) * k ^ 2) :
    ∃ C : ℝ, 0 < C ∧
      (∑' x : Site,
        Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k -
          b * ‖siteToPlane (w - x)‖ ^ 2 / n) * ‖siteToPlane x‖ ^ 2 ≤
        C * (k : ℝ) ^ 2 * Real.exp (-a * ‖siteToPlane w‖ ^ 2 / (k + n))) ∧
      C = 2 * (16 / a * (1 + 2 * Real.pi / a)) +
        2 * (8 * (1 + Real.pi / a)) * (b / a) ^ 2 / δ₀ := by
  have hlR : 0 < (k : ℝ) + n := by positivity
  have hgapPositive : 0 < δ₀ / ((k : ℝ) + n) := div_pos hδ₀ hlR
  have hgapExp (W : ℝ) (hW : 0 ≤ W) :
      W * Real.exp (-γ * W) ≤
        ((k : ℝ) + n) / δ₀ * Real.exp (-a * W / ((k : ℝ) + n)) := by
    have hfac : Real.exp (-γ * W) =
        Real.exp (-a * W / ((k : ℝ) + n)) *
          Real.exp (-(γ - a / ((k : ℝ) + n)) * W) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hdec : Real.exp (-(γ - a / ((k : ℝ) + n)) * W) ≤
        Real.exp (-(δ₀ / ((k : ℝ) + n)) * W) := by
      apply Real.exp_le_exp.mpr
      have hgapW := mul_le_mul_of_nonneg_right hgap hW
      calc
        -(γ - a / ((k : ℝ) + n)) * W = -((γ - a / ((k : ℝ) + n)) * W) := by ring
        _ ≤ -((δ₀ / ((k : ℝ) + n)) * W) := neg_le_neg hgapW
        _ = -(δ₀ / ((k : ℝ) + n)) * W := by ring
    have hpoly := expWeighted_le_inv hgapPositive hW
    have hinv : (δ₀ / ((k : ℝ) + n))⁻¹ = ((k : ℝ) + n) / δ₀ := by
      field_simp [ne_of_gt hδ₀, ne_of_gt hlR]
    have hpoly' : W * Real.exp (-(δ₀ / ((k : ℝ) + n)) * W) ≤
        ((k : ℝ) + n) / δ₀ := by
      rw [← hinv]
      exact hpoly
    rw [hfac]
    calc
      _ = Real.exp (-a * W / ((k : ℝ) + n)) *
          (W * Real.exp (-(γ - a / ((k : ℝ) + n)) * W)) := by ring
      _ ≤ Real.exp (-a * W / ((k : ℝ) + n)) *
          (W * Real.exp (-(δ₀ / ((k : ℝ) + n)) * W)) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left hdec hW
        · exact Real.exp_nonneg _
      _ ≤ Real.exp (-a * W / ((k : ℝ) + n)) * (((k : ℝ) + n) / δ₀) :=
        mul_le_mul_of_nonneg_left hpoly' (Real.exp_nonneg _)
      _ = _ := by ring
  have hW : 0 ≤ ‖siteToPlane w‖ ^ 2 := sq_nonneg _
  have hrawPoint (x : Site) :
      Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k -
          b * ‖siteToPlane (w - x)‖ ^ 2 / n) * ‖siteToPlane x‖ ^ 2 ≤
        Real.exp (-γ * ‖siteToPlane w‖ ^ 2) *
          (2 * (‖siteToPlane x - v‖ ^ 2 * Real.exp (-d * ‖siteToPlane x - v‖ ^ 2)) +
            2 * ‖v‖ ^ 2 * Real.exp (-d * ‖siteToPlane x - v‖ ^ 2)) := by
    rw [hpoint x]
    have hmul :
        (Real.exp (-γ * ‖siteToPlane w‖ ^ 2) *
          Real.exp (-d * ‖siteToPlane x - v‖ ^ 2)) * ‖siteToPlane x‖ ^ 2 ≤
        (Real.exp (-γ * ‖siteToPlane w‖ ^ 2) *
          Real.exp (-d * ‖siteToPlane x - v‖ ^ 2)) *
          (2 * ‖siteToPlane x - v‖ ^ 2 + 2 * ‖v‖ ^ 2) := by
      exact weighted_norm_sq_le (by positivity) (siteToPlane x) v
    calc
      _ = (Real.exp (-γ * ‖siteToPlane w‖ ^ 2) *
          Real.exp (-d * ‖siteToPlane x - v‖ ^ 2)) * ‖siteToPlane x‖ ^ 2 := rfl
      _ ≤ (Real.exp (-γ * ‖siteToPlane w‖ ^ 2) *
          Real.exp (-d * ‖siteToPlane x - v‖ ^ 2)) *
          (2 * ‖siteToPlane x - v‖ ^ 2 + 2 * ‖v‖ ^ 2) := hmul
      _ = _ := exp_product_rearrange
  let f2 : Site → ℝ := fun x => ‖siteToPlane x - v‖ ^ 2 *
    Real.exp (-d * ‖siteToPlane x - v‖ ^ 2)
  let f0 : Site → ℝ := fun x => Real.exp (-d * ‖siteToPlane x - v‖ ^ 2)
  let gmajor : Site → ℝ := fun x => Real.exp (-γ * ‖siteToPlane w‖ ^ 2) *
    (2 * f2 x + 2 * ‖v‖ ^ 2 * f0 x)
  have hmajor : Summable gmajor :=
    summable_two_weighted hshift2 hshift0
      (Real.exp (-γ * ‖siteToPlane w‖ ^ 2)) (2 * ‖v‖ ^ 2)
  have hrawSummable : Summable (fun x : Site =>
      Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k -
        b * ‖siteToPlane (w - x)‖ ^ 2 / n) * ‖siteToPlane x‖ ^ 2) := by
    apply hmajor.of_nonneg_of_le
    · intro x
      positivity
    · intro x
      exact hrawPoint x
  have hrawSum :
      ∑' x : Site, Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k -
        b * ‖siteToPlane (w - x)‖ ^ 2 / n) * ‖siteToPlane x‖ ^ 2 ≤
      Real.exp (-γ * ‖siteToPlane w‖ ^ 2) *
        (2 * (∑' x : Site, f2 x) + 2 * ‖v‖ ^ 2 * (∑' x : Site, f0 x)) := by
    have hmajorEq : (∑' x : Site, gmajor x) =
        Real.exp (-γ * ‖siteToPlane w‖ ^ 2) *
          (2 * (∑' x : Site, f2 x) + 2 * ‖v‖ ^ 2 * (∑' x : Site, f0 x)) := by
      dsimp [gmajor]
      rw [tsum_mul_left, Summable.tsum_add (hshift2.mul_left 2)
        (hshift0.mul_left (2 * ‖v‖ ^ 2)), tsum_mul_left, tsum_mul_left]
    have hle := hrawSummable.tsum_le_tsum (fun x => by
      simpa [gmajor, f2, f0] using hrawPoint x) hmajor
    simpa only [hmajorEq] using hle
  let M0 : ℝ := 8 * (1 + Real.pi / a)
  let M2 : ℝ := 16 / a * (1 + 2 * Real.pi / a)
  let C : ℝ := 2 * M2 + 2 * M0 * (b / a) ^ 2 / δ₀
  have hC : 0 < C := by dsimp [C, M2, M0]; positivity
  refine ⟨C, hC, ?_, ?_⟩
  · calc
    _ ≤ Real.exp (-γ * ‖siteToPlane w‖ ^ 2) *
        (2 * (M2 * k ^ 2) + 2 * ‖v‖ ^ 2 * (M0 * k)) := by
      have hcoef : 0 ≤ Real.exp (-γ * ‖siteToPlane w‖ ^ 2) := Real.exp_nonneg _
      apply hrawSum.trans
      apply mul_le_mul_of_nonneg_left _ hcoef
      exact add_le_add (mul_le_mul_of_nonneg_left hS2 (by norm_num))
        (mul_le_mul_of_nonneg_left hS0 (by positivity))
    _ ≤ 2 * M2 * k ^ 2 * Real.exp (-a * ‖siteToPlane w‖ ^ 2 / (k + n)) +
        2 * M0 * (b / a) ^ 2 / δ₀ * k ^ 2 *
          Real.exp (-a * ‖siteToPlane w‖ ^ 2 / (k + n)) := by
      have hE : Real.exp (-γ * ‖siteToPlane w‖ ^ 2) ≤
          Real.exp (-a * ‖siteToPlane w‖ ^ 2 / (k + n)) := by
        apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_right hrate hW
        calc
          -γ * ‖siteToPlane w‖ ^ 2 = -(γ * ‖siteToPlane w‖ ^ 2) := by ring
          _ ≤ -(a / ((k : ℝ) + n) * ‖siteToPlane w‖ ^ 2) := neg_le_neg h
          _ = -a * ‖siteToPlane w‖ ^ 2 / (k + n) := by ring
      have hweighted := hgapExp (‖siteToPlane w‖ ^ 2) hW
      rw [hnormV]
      have hμsq : μ ^ 2 ≤ (b / a) ^ 2 * (k / ((k : ℝ) + n)) ^ 2 := by
        have hRnonneg : 0 ≤ (b / a) * (k / ((k : ℝ) + n)) :=
          le_trans hμnonneg hμBound
        have hsq := (sq_le_sq₀ hμnonneg hRnonneg).2 hμBound
        rw [mul_pow] at hsq
        exact hsq
      have hk3 : (k : ℝ) ^ 3 / ((k : ℝ) + n) ≤ (k : ℝ) ^ 2 := by
        rw [div_le_iff₀ hlR]
        nlinarith [sq_nonneg (k : ℝ)]
      have hfirst := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ 2 * M2 * k ^ 2)
      have hmuScale : μ ^ 2 * k * (((k : ℝ) + n) / δ₀) ≤
          (b / a) ^ 2 / δ₀ * (k : ℝ) ^ 2 := by
        have hscale := mul_le_mul_of_nonneg_right hμsq
          (mul_nonneg (by positivity : 0 ≤ (k : ℝ))
            (div_nonneg (by positivity : 0 ≤ (k : ℝ) + n) hδ₀.le))
        calc
          _ = μ ^ 2 * ((k : ℝ) * (((k : ℝ) + n) / δ₀)) := by ring
          _ ≤ ((b / a) ^ 2 * (k / ((k : ℝ) + n)) ^ 2) *
              ((k : ℝ) * (((k : ℝ) + n) / δ₀)) := hscale
          _ = ((b / a) ^ 2 / δ₀) *
              ((k : ℝ) ^ 3 / ((k : ℝ) + n)) := by
            field_simp [ne_of_gt hδ₀, ne_of_gt hlR]
          _ ≤ ((b / a) ^ 2 / δ₀) * (k : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left hk3 (by positivity : 0 ≤ (b / a) ^ 2 / δ₀)
      have hcoeffBound : 2 * M0 * μ ^ 2 * k * (((k : ℝ) + n) / δ₀) ≤
          2 * M0 * (b / a) ^ 2 / δ₀ * (k : ℝ) ^ 2 := by
        calc
          _ = 2 * M0 * (μ ^ 2 * k * (((k : ℝ) + n) / δ₀)) := by ring
          _ ≤ 2 * M0 * ((b / a) ^ 2 / δ₀ * (k : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hmuScale (by positivity)
          _ = _ := by ring
      have hsecond :
          2 * M0 * μ ^ 2 * k * (‖siteToPlane w‖ ^ 2 *
            Real.exp (-γ * ‖siteToPlane w‖ ^ 2)) ≤
          2 * M0 * (b / a) ^ 2 / δ₀ * (k : ℝ) ^ 2 *
            Real.exp (-a * ‖siteToPlane w‖ ^ 2 / (k + n)) := by
        calc
          _ = (2 * M0 * μ ^ 2 * k) *
              (‖siteToPlane w‖ ^ 2 * Real.exp (-γ * ‖siteToPlane w‖ ^ 2)) := by ring
          _ ≤ (2 * M0 * μ ^ 2 * k) *
              (((k : ℝ) + n) / δ₀ *
                Real.exp (-a * ‖siteToPlane w‖ ^ 2 / (k + n))) :=
            mul_le_mul_of_nonneg_left hweighted (by positivity)
          _ = (2 * M0 * μ ^ 2 * k * (((k : ℝ) + n) / δ₀)) *
              Real.exp (-a * ‖siteToPlane w‖ ^ 2 / (k + n)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hcoeffBound (Real.exp_nonneg _)
      have hsumForm : Real.exp (-γ * ‖siteToPlane w‖ ^ 2) *
          (2 * (M2 * k ^ 2) + 2 * (μ ^ 2 * ‖siteToPlane w‖ ^ 2) * (M0 * k)) =
          2 * M2 * k ^ 2 * Real.exp (-γ * ‖siteToPlane w‖ ^ 2) +
            2 * M0 * μ ^ 2 * k * (‖siteToPlane w‖ ^ 2 *
              Real.exp (-γ * ‖siteToPlane w‖ ^ 2)) := by ring
      rw [hsumForm]
      exact add_le_add hfirst hsecond
    _ = C * (k : ℝ) ^ 2 *
        Real.exp (-a * ‖siteToPlane w‖ ^ 2 / (k + n)) := by
      dsimp [C, M2, M0]
      ring
  · dsimp [C, M2, M0]

/-- Two-rate Gaussian products have a localized second-moment bound when the
second time interval dominates the first. -/
private theorem rawGaussian_twoRate_secondMoment_control {a b : ℝ}
    (ha : 0 < a) (hab : a < b) {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n)
    (hkn : 2 * k ≤ n) (w : Site) :
    ∃ C : ℝ, 0 < C ∧
      (∑' x : Site,
        Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k -
          b * ‖siteToPlane (w - x)‖ ^ 2 / n) * ‖siteToPlane x‖ ^ 2 ≤
        C * (k : ℝ) ^ 2 * Real.exp (-a * ‖siteToPlane w‖ ^ 2 / (k + n))) ∧
      C = 2 * (16 / a * (1 + 2 * Real.pi / a)) +
        2 * (8 * (1 + Real.pi / a)) * (b / a) ^ 2 /
          (2 * a * (b - a) / (3 * b)) := by
  let K : ℝ := (k : ℝ) / a
  let L : ℝ := (n : ℝ) / b
  let H : ℝ := K * L / (K + L)
  let d : ℝ := (K + L) / (K * L)
  let γ : ℝ := 1 / (K + L)
  let μ : ℝ := K / (K + L)
  let den : ℝ := b * k + a * n
  let δ₀ : ℝ := 2 * a * (b - a) / (3 * b)
  let v : Plane := μ • siteToPlane w
  have hb : 0 < b := lt_trans ha hab
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hk)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hn)
  have hlR : 0 < (k : ℝ) + n := by positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hKL : 0 < K + L := by positivity
  have hprod : 0 < K * L := mul_pos hK hL
  have hH : 0 < H := by dsimp [H]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hden : 0 < den := by dsimp [den]; positivity
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hHle : H ≤ K := by
    dsimp [H]
    rw [div_le_iff₀ hKL]
    nlinarith [sq_nonneg K]
  have hrate : a / ((k : ℝ) + n) ≤ γ := by
    change a / ((k : ℝ) + n) ≤ 1 / (K + L)
    rw [div_le_div_iff₀ hlR hKL]
    dsimp [K, L]
    field_simp [ne_of_gt ha, ne_of_gt hb]
    nlinarith [mul_le_mul_of_nonneg_right (le_of_lt hab) hnR.le]
  have hγeq : γ = a * b / den := by
    dsimp [γ, K, L, den]
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hden]
  have hμeq : μ = b * k / den := by
    dsimp [μ, K, L, den]
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hden]
  have hμnonneg : 0 ≤ μ := by dsimp [μ]; positivity
  have hdenBound : 2 * den ≤ 3 * b * n := by
    have hknR : 2 * (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    have h1 := mul_le_mul_of_nonneg_left hknR hb.le
    have h2 := mul_le_mul_of_nonneg_right (le_of_lt hab) hnR.le
    dsimp [den]
    linarith only [h1, h2]
  have hgapEq : γ - a / ((k : ℝ) + n) =
      a * (b - a) * n / (den * ((k : ℝ) + n)) := by
    rw [hγeq]
    field_simp [ne_of_gt hden, ne_of_gt hlR]
    ring
  have hgap : δ₀ / ((k : ℝ) + n) ≤
      γ - a / ((k : ℝ) + n) := by
    rw [hgapEq, div_le_div_iff₀ hlR (mul_pos hden hlR)]
    have hcoeff : 0 ≤ a * (b - a) / (3 * b) := by positivity
    have hkey : δ₀ * den ≤ a * (b - a) * n := by
      calc
        δ₀ * den = (a * (b - a) / (3 * b)) * (2 * den) := by
          dsimp [δ₀]
          ring
        _ ≤ (a * (b - a) / (3 * b)) * (3 * b * n) :=
          mul_le_mul_of_nonneg_left hdenBound hcoeff
        _ = _ := by field_simp [ne_of_gt hb]
    have hkey' := mul_le_mul_of_nonneg_right hkey hlR.le
    dsimp [δ₀]
    nlinarith [hkey']
  have hpoint (x : Site) :
      Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k -
          b * ‖siteToPlane (w - x)‖ ^ 2 / n) =
        Real.exp (-γ * ‖siteToPlane w‖ ^ 2) *
          Real.exp (-d * ‖siteToPlane x - v‖ ^ 2) := by
    rw [siteToPlane_sub, ← Real.exp_add]
    congr 1
    have hsq := gaussian_square_completion hK hL
      (siteToPlane x) (siteToPlane w)
    have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkR
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hfirst : -a * ‖siteToPlane x‖ ^ 2 / k =
        -‖siteToPlane x‖ ^ 2 / K := by
      dsimp [K]
      field_simp [hk0, ne_of_gt ha]
    have hsecond : -b * ‖siteToPlane w - siteToPlane x‖ ^ 2 / n =
        -‖siteToPlane w - siteToPlane x‖ ^ 2 / L := by
      dsimp [L]
      field_simp [hn0, ne_of_gt hb]
    calc
      _ = -‖siteToPlane x‖ ^ 2 / K -
            ‖siteToPlane w - siteToPlane x‖ ^ 2 / L := by
        linear_combination hfirst + hsecond
      _ = -γ * ‖siteToPlane w‖ ^ 2 + -d * ‖siteToPlane x - v‖ ^ 2 := by
        have hsqNeg := congrArg Neg.neg hsq
        calc
          -‖siteToPlane x‖ ^ 2 / K -
              ‖siteToPlane w - siteToPlane x‖ ^ 2 / L =
              -(‖siteToPlane x‖ ^ 2 / K +
                ‖siteToPlane w - siteToPlane x‖ ^ 2 / L) := by ring
          _ = -(‖siteToPlane w‖ ^ 2 / (K + L) +
                (K + L) / (K * L) *
                  ‖siteToPlane x - (K / (K + L)) • siteToPlane w‖ ^ 2) := hsqNeg
          _ = -γ * ‖siteToPlane w‖ ^ 2 + -d * ‖siteToPlane x - v‖ ^ 2 := by
            dsimp [γ, d, v]
            ring
  have hshift0 := shiftedSiteGaussian_control hd v
  have hshift2 := shiftedSiteGaussian_secondMoment_control hd v
  have hdeq : Real.pi / d = Real.pi * H := by
    dsimp [d, H]
    field_simp [ne_of_gt hprod, ne_of_gt hKL]
  have hroot : Real.sqrt (Real.pi / d) ≤ Real.sqrt (Real.pi / a) * Real.sqrt k := by
    rw [hdeq, Real.sqrt_mul Real.pi_nonneg]
    have hright : Real.sqrt (Real.pi / a) * Real.sqrt k =
        Real.sqrt Real.pi * Real.sqrt K := by
      rw [← Real.sqrt_mul (by positivity : 0 ≤ Real.pi / a)]
      rw [show (Real.pi / a) * k = Real.pi * K by
        dsimp [K]
        field_simp [ne_of_gt ha]]
      rw [Real.sqrt_mul Real.pi_nonneg]
    rw [hright]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hHle) (Real.sqrt_nonneg _)
  have hroot2 : Real.sqrt (2 * Real.pi / d) ≤
      Real.sqrt (2 * Real.pi / a) * Real.sqrt k := by
    have hdeq2 : 2 * Real.pi / d = (2 * Real.pi) * H := by
      dsimp [d, H]
      field_simp [ne_of_gt hprod, ne_of_gt hKL]
    rw [hdeq2, Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
    have hright : Real.sqrt (2 * Real.pi / a) * Real.sqrt k =
        Real.sqrt (2 * Real.pi) * Real.sqrt K := by
      rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi / a)]
      rw [show (2 * Real.pi / a) * k = (2 * Real.pi) * K by
        dsimp [K]
        field_simp [ne_of_gt ha]]
      rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
    rw [hright]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hHle) (Real.sqrt_nonneg _)
  have hrootSq : (1 + Real.sqrt (Real.pi / d)) ^ 2 ≤
      2 * (1 + Real.pi / a) * k := by
    have hroot' : 1 + Real.sqrt (Real.pi / d) ≤
        (1 + Real.sqrt (Real.pi / a)) * Real.sqrt k := by
      have hkroot : 1 ≤ Real.sqrt k := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hk)
      calc
        1 + Real.sqrt (Real.pi / d) ≤ Real.sqrt k + Real.sqrt (Real.pi / a) * Real.sqrt k :=
          add_le_add hkroot hroot
        _ = (1 + Real.sqrt (Real.pi / a)) * Real.sqrt k := by ring
    have hsq := (sq_le_sq₀ (by positivity) (by positivity)).2 hroot'
    rw [mul_pow, Real.sq_sqrt (by exact_mod_cast (Nat.zero_le k))] at hsq
    have hbase : (1 + Real.sqrt (Real.pi / a)) ^ 2 ≤ 2 * (1 + Real.pi / a) := by
      have hx := Real.sq_sqrt (show 0 ≤ Real.pi / a by positivity)
      nlinarith only [sq_nonneg (Real.sqrt (Real.pi / a) - 1), hx]
    calc
      _ ≤ (1 + Real.sqrt (Real.pi / a)) ^ 2 * k := hsq
      _ ≤ _ := mul_le_mul_of_nonneg_right hbase (by positivity)
  have hroot2Sq : (1 + Real.sqrt (2 * Real.pi / d)) ^ 2 ≤
      2 * (1 + 2 * Real.pi / a) * k := by
    have hroot' : 1 + Real.sqrt (2 * Real.pi / d) ≤
        (1 + Real.sqrt (2 * Real.pi / a)) * Real.sqrt k := by
      have hkroot : 1 ≤ Real.sqrt k := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hk)
      calc
        1 + Real.sqrt (2 * Real.pi / d) ≤ Real.sqrt k + Real.sqrt (2 * Real.pi / a) * Real.sqrt k :=
          add_le_add hkroot hroot2
        _ = (1 + Real.sqrt (2 * Real.pi / a)) * Real.sqrt k := by ring
    have hsq := (sq_le_sq₀ (by positivity) (by positivity)).2 hroot'
    rw [mul_pow, Real.sq_sqrt (by exact_mod_cast (Nat.zero_le k))] at hsq
    have hbase : (1 + Real.sqrt (2 * Real.pi / a)) ^ 2 ≤
        2 * (1 + 2 * Real.pi / a) := by
      have hx := Real.sq_sqrt (show 0 ≤ 2 * Real.pi / a by positivity)
      nlinarith only [sq_nonneg (Real.sqrt (2 * Real.pi / a) - 1), hx]
    calc
      _ ≤ (1 + Real.sqrt (2 * Real.pi / a)) ^ 2 * k := hsq
      _ ≤ _ := mul_le_mul_of_nonneg_right hbase (by positivity)
  have hS0 : (∑' x : Site, Real.exp (-d * ‖siteToPlane x - v‖ ^ 2)) ≤
      8 * (1 + Real.pi / a) * k := by
    calc
      _ ≤ 4 * (1 + Real.sqrt (Real.pi / d)) ^ 2 := hshift0.2
      _ ≤ 4 * (2 * (1 + Real.pi / a) * k) :=
        mul_le_mul_of_nonneg_left hrootSq (by norm_num)
      _ = _ := by ring
  have hS2 :
      (∑' x : Site, ‖siteToPlane x - v‖ ^ 2 *
        Real.exp (-d * ‖siteToPlane x - v‖ ^ 2)) ≤
      16 / a * (1 + 2 * Real.pi / a) * k ^ 2 := by
    calc
      _ ≤ 8 / d * (1 + Real.sqrt (2 * Real.pi / d)) ^ 2 := hshift2.2
      _ = 8 * d⁻¹ * (1 + Real.sqrt (2 * Real.pi / d)) ^ 2 := by
        rw [div_eq_mul_inv]
      _ = 8 * H * (1 + Real.sqrt (2 * Real.pi / d)) ^ 2 := by
        have hdinv : d⁻¹ = H := by dsimp [d, H]; field_simp [ne_of_gt hprod, ne_of_gt hKL]
        rw [hdinv]
      _ ≤ 8 * H * (2 * (1 + 2 * Real.pi / a) * k) :=
        mul_le_mul_of_nonneg_left hroot2Sq (by positivity)
      _ ≤ _ := by
        have hHbound : H ≤ k / a := by dsimp [K] at hHle ⊢; exact hHle
        have hkpos : 0 ≤ (k : ℝ) := by positivity
        have hfactor : 0 ≤ 16 * (1 + 2 * Real.pi / a) * k := by positivity
        calc
          _ = (16 * (1 + 2 * Real.pi / a) * k) * H := by ring
          _ ≤ (16 * (1 + 2 * Real.pi / a) * k) * (k / a) :=
            mul_le_mul_of_nonneg_left hHbound hfactor
          _ = _ := by ring
  have hmuBound : μ ≤ (b / a) * (k / ((k : ℝ) + n)) := by
    have hdenLower : a * ((k : ℝ) + n) ≤ den := by
      change a * ((k : ℝ) + n) ≤ b * k + a * n
      have hbk := mul_le_mul_of_nonneg_right (le_of_lt hab) hkR.le
      rw [mul_add]
      exact add_le_add hbk le_rfl
    rw [hμeq]
    have hratio : b * k / den ≤ b * k / (a * ((k : ℝ) + n)) := by
      rw [div_le_div_iff₀ hden (mul_pos ha hlR)]
      exact mul_le_mul_of_nonneg_left hdenLower (by positivity)
    calc
      _ ≤ (b * k) / (a * ((k : ℝ) + n)) := hratio
      _ = _ := by field_simp [ne_of_gt ha, ne_of_gt hlR]
  have hnormV : ‖v‖ ^ 2 = μ ^ 2 * ‖siteToPlane w‖ ^ 2 := by
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμnonneg]
    ring
  obtain ⟨C, hC, hBound, hCeq⟩ := rawGaussian_twoRate_sum_bound
    ha hδ₀ hk hn hrate hgap hμnonneg hmuBound w v hnormV hpoint
    hshift0.1 hshift2.1 hS0 hS2
  exact ⟨C, hC, hBound, by simpa [δ₀] using hCeq⟩

/-- The squared difference from the averaged walk kernel is bounded by the average squared difference. -/
theorem kernelVariance_jensen {k n : ℕ} (w y : Site) :
    (srwKernel n (w - y) - srwKernel (k + n) w) ^ 2 ≤
      ∑' z : Site, srwKernel k z *
        (srwKernel n (w - y) - srwKernel n (w - z)) ^ 2 := by
  classical
  let E := Polymer.endpoints 0 k
  have hmass : ∑ z ∈ E, srwKernel k z = 1 := by
    simpa [E, sub_zero] using Polymer.sum_srwKernel_endpoints k 0
  have hsemigroup : srwKernel (k + n) w =
      ∑ z ∈ E, srwKernel k z * srwKernel n (w - z) := by
    have h := Polymer.srwKernel_convolution k n 0 w
    have hsum : (∑' z : Site, srwKernel k z * srwKernel n (w - z)) =
        ∑ z ∈ E, srwKernel k z * srwKernel n (w - z) := by
      apply tsum_eq_sum
      intro z hz
      have hq := Polymer.srwKernel_eq_zero_of_not_mem k 0 z hz
      have hq0 : srwKernel k z = 0 := by simpa using hq
      simp [hq0]
    calc
      srwKernel (k + n) w =
          ∑' z : Site, srwKernel k z * srwKernel n (w - z) := by
        simpa only [sub_zero] using h
      _ = _ := hsum
  have hmean :
      ∑ z ∈ E, srwKernel k z * (srwKernel n (w - y) - srwKernel n (w - z)) =
        srwKernel n (w - y) - srwKernel (k + n) w := by
    calc
      _ = ∑ z ∈ E, (srwKernel k z * srwKernel n (w - y) -
            srwKernel k z * srwKernel n (w - z)) := by
          apply Finset.sum_congr rfl
          intro z hz
          ring
      _ = (∑ z ∈ E, srwKernel k z * srwKernel n (w - y)) -
            (∑ z ∈ E, srwKernel k z * srwKernel n (w - z)) :=
          by rw [Finset.sum_sub_distrib]
      _ = (∑ z ∈ E, srwKernel k z) * srwKernel n (w - y) -
            srwKernel (k + n) w := by
          rw [Finset.sum_mul, hsemigroup]
      _ = _ := by rw [hmass]; ring
  have hconvex : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) :=
    Even.convexOn_pow (by norm_num : Even 2)
  have hJensen :
      (∑ z ∈ E, srwKernel k z •
        (srwKernel n (w - y) - srwKernel n (w - z))) ^ 2 ≤
        ∑ z ∈ E, srwKernel k z •
          (srwKernel n (w - y) - srwKernel n (w - z)) ^ 2 := by
    apply hconvex.map_sum_le
    · intro z hz
      exact Critical2DKPZ.srwKernel_nonneg k z
    · exact hmass
    · intro z hz
      exact Set.mem_univ _
  have hfinite :
      (∑ z ∈ E, srwKernel k z •
        (srwKernel n (w - y) - srwKernel n (w - z))) =
        srwKernel n (w - y) - srwKernel (k + n) w := by
    simpa only [smul_eq_mul] using hmean
  have hJ := hJensen
  rw [hfinite] at hJ
  have hsum :
      (∑ z ∈ E, srwKernel k z •
        (srwKernel n (w - y) - srwKernel n (w - z)) ^ 2) =
        ∑' z : Site, srwKernel k z *
          (srwKernel n (w - y) - srwKernel n (w - z)) ^ 2 := by
    simp only [smul_eq_mul]
    symm
    apply tsum_eq_sum
    intro z hz
    have hq := Polymer.srwKernel_eq_zero_of_not_mem k 0 z hz
    have hq0 : srwKernel k z = 0 := by simpa using hq
    simp [hq0]
  rw [hsum] at hJ
  exact hJ

private theorem one_add_sqrt_scaled_sq_le {r : ℝ} {k : ℕ} (hr : 0 ≤ r)
    (hk : 1 ≤ k) :
    (1 + r * Real.sqrt k) ^ 2 ≤ 2 * (1 + r ^ 2) * k := by
  have hkroot : 1 ≤ Real.sqrt k := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hk)
  have hroot : 1 + r * Real.sqrt k ≤ (1 + r) * Real.sqrt k := by
    nlinarith [mul_nonneg hr (sub_nonneg.mpr hkroot)]
  have hsquare := (sq_le_sq₀ (by positivity) (by positivity)).2 hroot
  have hbase : (1 + r) ^ 2 ≤ 2 * (1 + r ^ 2) := by
    nlinarith [sq_nonneg (r - 1)]
  rw [mul_pow, Real.sq_sqrt (by exact_mod_cast (Nat.zero_le k))] at hsquare
  calc
    _ ≤ (1 + r) ^ 2 * k := hsquare
    _ ≤ 2 * (1 + r ^ 2) * k := by
      exact mul_le_mul_of_nonneg_right hbase (by positivity)

/-- Scaled unshifted Gaussian mass and second moment bounds. -/
private theorem scaledSiteGaussian_mass_moment {a : ℝ} (ha : 0 < a)
    {k : ℕ} (hk : 1 ≤ k) :
    Summable (fun x : Site => Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k)) ∧
      (∑' x : Site, Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k) ≤
        8 * (1 + Real.pi / a) * k) ∧
      Summable (fun x : Site => ‖siteToPlane x‖ ^ 2 *
        Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k)) ∧
      (∑' x : Site, ‖siteToPlane x‖ ^ 2 *
        Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k) ≤
        16 / a * (1 + 2 * Real.pi / a) * k ^ 2) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hk)
  have hshift0 := shiftedSiteGaussian_control (div_pos ha hkR) (0 : Plane)
  have hshift2 := shiftedSiteGaussian_secondMoment_control (div_pos ha hkR) (0 : Plane)
  have hmassTerms : (fun x : Site =>
      Real.exp (-(a / (k : ℝ)) * ‖siteToPlane x - (0 : Plane)‖ ^ 2)) =
      (fun x : Site => Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k)) := by
    funext x
    rw [sub_zero]
    congr 1
    field_simp [ne_of_gt hkR]
  have hmomentTerms : (fun x : Site => ‖siteToPlane x - (0 : Plane)‖ ^ 2 *
      Real.exp (-(a / (k : ℝ)) * ‖siteToPlane x - (0 : Plane)‖ ^ 2)) =
      (fun x : Site => ‖siteToPlane x‖ ^ 2 *
        Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k)) := by
    funext x
    rw [sub_zero]
    congr 1
    field_simp [ne_of_gt hkR]
  have hmassSummable : Summable (fun x : Site =>
      Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k)) := by
    rw [← hmassTerms]
    exact hshift0.1
  have hmomentSummable : Summable (fun x : Site => ‖siteToPlane x‖ ^ 2 *
      Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k)) := by
    rw [← hmomentTerms]
    exact hshift2.1
  have hrootMass : Real.sqrt (Real.pi / (a / k)) =
      Real.sqrt (Real.pi / a) * Real.sqrt k := by
    rw [show Real.pi / (a / k) = (Real.pi / a) * k by
      field_simp [ne_of_gt ha, ne_of_gt hkR], Real.sqrt_mul (div_nonneg Real.pi_pos.le ha.le)]
  have hrootMoment : Real.sqrt (2 * Real.pi / (a / k)) =
      Real.sqrt (2 * Real.pi / a) * Real.sqrt k := by
    rw [show 2 * Real.pi / (a / k) = (2 * Real.pi / a) * k by
      field_simp [ne_of_gt ha, ne_of_gt hkR], Real.sqrt_mul (by positivity)]
  refine ⟨hmassSummable, ?_, hmomentSummable, ?_⟩
  · calc
      _ ≤ 4 * (1 + Real.sqrt (Real.pi / (a / k))) ^ 2 := by
        rw [← hmassTerms]
        exact hshift0.2
      _ = 4 * (1 + Real.sqrt (Real.pi / a) * Real.sqrt k) ^ 2 := by rw [hrootMass]
      _ ≤ 8 * (1 + Real.pi / a) * k := by
        have hscaled0 := one_add_sqrt_scaled_sq_le
          (r := Real.sqrt (Real.pi / a)) (Real.sqrt_nonneg _) hk
        have hscaled : (1 + Real.sqrt (Real.pi / a) * Real.sqrt k) ^ 2 ≤
            2 * (1 + Real.pi / a) * k := by
          simpa only [Real.sq_sqrt (div_nonneg Real.pi_pos.le ha.le)] using hscaled0
        calc
          _ = 4 * (1 + Real.sqrt (Real.pi / a) * Real.sqrt k) ^ 2 := rfl
          _ ≤ 4 * (2 * (1 + Real.pi / a) * k) :=
            mul_le_mul_of_nonneg_left hscaled (by norm_num)
          _ = _ := by ring
  · calc
      _ ≤ 8 / (a / k) * (1 + Real.sqrt (2 * Real.pi / (a / k))) ^ 2 := by
        rw [← hmomentTerms]
        exact hshift2.2
      _ = 8 / (a / k) *
          (1 + Real.sqrt (2 * Real.pi / a) * Real.sqrt k) ^ 2 := by rw [hrootMoment]
      _ ≤ 16 / a * (1 + 2 * Real.pi / a) * k ^ 2 := by
        have hscaled0 := one_add_sqrt_scaled_sq_le
          (r := Real.sqrt (2 * Real.pi / a)) (Real.sqrt_nonneg _) hk
        have hscaled : (1 + Real.sqrt (2 * Real.pi / a) * Real.sqrt k) ^ 2 ≤
            2 * (1 + 2 * Real.pi / a) * k := by
          simpa only [Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi / a)] using hscaled0
        have hscale : 0 ≤ 8 / (a / k) := by positivity
        calc
          _ ≤ 8 / (a / k) * (2 * (1 + 2 * Real.pi / a) * k) :=
            mul_le_mul_of_nonneg_left hscaled hscale
          _ = _ := by field_simp [ne_of_gt ha, ne_of_gt hkR]; ring

private theorem hatGaussian_le_rawGaussian {c : ℝ}
    {k : ℕ} (hk : 1 ≤ k) (x : Site) :
    hatGaussian c k x ≤ (k : ℝ)⁻¹ *
      Real.exp (-c * ‖siteToPlane x‖ ^ 2 / k) := by
  have hk0 : k ≠ 0 := by omega
  by_cases hp : Even ((k : ℤ) + x 0 + x 1)
  · simp [hatGaussian, hk0, hp]
  · simp [hatGaussian, hk0, hp]
    positivity

/-- The lattice Gaussian second moment is summable and bounded by a constant times elapsed time. -/
theorem hatGaussian_secondMoment_le {c : ℝ} (hc : 0 < c)
    {k : ℕ} (hk : 1 ≤ k) :
    Summable (fun x : Site => hatGaussian c k x * ‖siteToPlane x‖ ^ 2) ∧
    (∑' x : Site, hatGaussian c k x * ‖siteToPlane x‖ ^ 2 ≤
      16 / c * (1 + 2 * Real.pi / c) * k) := by
  have hraw := scaledSiteGaussian_mass_moment hc hk
  have hpoint (x : Site) : 0 ≤ hatGaussian c k x * ‖siteToPlane x‖ ^ 2 ∧
      hatGaussian c k x * ‖siteToPlane x‖ ^ 2 ≤
        (k : ℝ)⁻¹ * (‖siteToPlane x‖ ^ 2 *
          Real.exp (-c * ‖siteToPlane x‖ ^ 2 / k)) := by
    constructor
    · exact mul_nonneg (hatGaussian_nonneg k x) (sq_nonneg _)
    · calc
        _ ≤ ((k : ℝ)⁻¹ * Real.exp (-c * ‖siteToPlane x‖ ^ 2 / k)) *
            ‖siteToPlane x‖ ^ 2 :=
              mul_le_mul_of_nonneg_right (hatGaussian_le_rawGaussian hk x) (sq_nonneg _)
        _ = _ := by ring
  have hmajorSummable : Summable (fun x : Site => (k : ℝ)⁻¹ *
      (‖siteToPlane x‖ ^ 2 * Real.exp (-c * ‖siteToPlane x‖ ^ 2 / k))) :=
    hraw.2.2.1.mul_left _
  have hsum := hmajorSummable.of_nonneg_of_le
    (fun x => hpoint x |>.1) (fun x => hpoint x |>.2)
  refine ⟨hsum, ?_⟩
  calc
    _ ≤ ∑' x : Site, (k : ℝ)⁻¹ *
        (‖siteToPlane x‖ ^ 2 * Real.exp (-c * ‖siteToPlane x‖ ^ 2 / k)) :=
      hsum.tsum_le_tsum (fun x => (hpoint x).2) hmajorSummable
    _ = (k : ℝ)⁻¹ *
        (∑' x : Site, ‖siteToPlane x‖ ^ 2 *
          Real.exp (-c * ‖siteToPlane x‖ ^ 2 / k)) := tsum_mul_left
    _ ≤ (k : ℝ)⁻¹ * (16 / c * (1 + 2 * Real.pi / c) * k ^ 2) := by
      exact mul_le_mul_of_nonneg_left hraw.2.2.2 (inv_nonneg.mpr (by positivity))
    _ = 16 / c * (1 + 2 * Real.pi / c) * k := by
      have hkR : (k : ℝ) ≠ 0 := by positivity
      field_simp [hkR]

private theorem rawGaussian_twoRate_secondMoment_summable {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) {k n : ℕ} (hk : 1 ≤ k)
    (w : Site) :
    Summable (fun x : Site =>
      Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k -
        b * ‖siteToPlane (w - x)‖ ^ 2 / n) * ‖siteToPlane x‖ ^ 2) := by
  have hbase := scaledSiteGaussian_mass_moment ha hk
  have hpoint (x : Site) :
      0 ≤ Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k -
        b * ‖siteToPlane (w - x)‖ ^ 2 / n) * ‖siteToPlane x‖ ^ 2 ∧
      Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k -
        b * ‖siteToPlane (w - x)‖ ^ 2 / n) * ‖siteToPlane x‖ ^ 2 ≤
      Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k) * ‖siteToPlane x‖ ^ 2 := by
    have hsecond : Real.exp (-b * ‖siteToPlane (w - x)‖ ^ 2 / n) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hnum' : 0 ≤ b * ‖siteToPlane (w - x)‖ ^ 2 :=
        mul_nonneg hb.le (sq_nonneg _)
      have hnum : -b * ‖siteToPlane (w - x)‖ ^ 2 ≤ 0 := by
        calc
          -b * ‖siteToPlane (w - x)‖ ^ 2 =
              -(b * ‖siteToPlane (w - x)‖ ^ 2) := by ring
          _ ≤ 0 := neg_nonpos.mpr hnum'
      exact div_nonpos_of_nonpos_of_nonneg hnum (by positivity)
    have hfactor : Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k -
        b * ‖siteToPlane (w - x)‖ ^ 2 / n) =
        Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k) *
          Real.exp (-b * ‖siteToPlane (w - x)‖ ^ 2 / n) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hfactor]
    constructor
    · positivity
    · calc
        _ = (Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k) *
            Real.exp (-b * ‖siteToPlane (w - x)‖ ^ 2 / n)) *
              ‖siteToPlane x‖ ^ 2 := by ring
        _ ≤ Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k) *
            ‖siteToPlane x‖ ^ 2 := by
              apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
              calc
                _ ≤ Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k) * 1 :=
                  mul_le_mul_of_nonneg_left hsecond (Real.exp_nonneg _)
                _ = _ := by ring
  have hsum : Summable (fun x : Site =>
      Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k) * ‖siteToPlane x‖ ^ 2) := by
    apply hbase.2.2.1.congr
    intro x
    ring
  have hsum := hsum.of_nonneg_of_le
    (fun x => (hpoint x).1) (fun x => (hpoint x).2)
  exact hsum

/-- The walk kernel inherits the Gaussian mass and second-moment estimates. -/
theorem srwKernel_gaussian_mass_moment {c Ck : ℝ} (hc : 0 < c)
    (hCk : 0 ≤ Ck)
    (hkernel : ∀ n x, srwKernel n x ≤ Ck * hatGaussian c n x)
    {k : ℕ} (hk : 1 ≤ k) :
    Summable (fun z : Site => srwKernel k z) ∧
      (∑' z : Site, srwKernel k z ≤ Ck * 8 * (1 + Real.pi / c)) ∧
      Summable (fun z : Site => srwKernel k z * ‖siteToPlane z‖ ^ 2) ∧
      (∑' z : Site, srwKernel k z * ‖siteToPlane z‖ ^ 2 ≤
        Ck * 16 / c * (1 + 2 * Real.pi / c) * k) := by
  have hraw := scaledSiteGaussian_mass_moment hc hk
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hk)
  have hqPoint (z : Site) : 0 ≤ srwKernel k z ∧
      srwKernel k z ≤ Ck * (k : ℝ)⁻¹ *
        Real.exp (-c * ‖siteToPlane z‖ ^ 2 / k) := by
    constructor
    · exact Critical2DKPZ.srwKernel_nonneg _ _
    · calc
        _ ≤ Ck * hatGaussian c k z := hkernel k z
        _ ≤ Ck * ((k : ℝ)⁻¹ *
            Real.exp (-c * ‖siteToPlane z‖ ^ 2 / k)) :=
              mul_le_mul_of_nonneg_left (hatGaussian_le_rawGaussian hk z) hCk
        _ = _ := by ring
  have hqSum : Summable (fun z : Site => srwKernel k z) := by
    apply (hraw.1.mul_left (Ck * (k : ℝ)⁻¹)).of_nonneg_of_le
    · exact fun z => (hqPoint z).1
    · exact fun z => (hqPoint z).2
  have hq2Point (z : Site) : 0 ≤ srwKernel k z * ‖siteToPlane z‖ ^ 2 ∧
      srwKernel k z * ‖siteToPlane z‖ ^ 2 ≤
        Ck * (k : ℝ)⁻¹ * (‖siteToPlane z‖ ^ 2 *
          Real.exp (-c * ‖siteToPlane z‖ ^ 2 / k)) := by
    constructor
    · exact mul_nonneg (hqPoint z).1 (sq_nonneg _)
    · calc
        _ ≤ (Ck * (k : ℝ)⁻¹ *
            Real.exp (-c * ‖siteToPlane z‖ ^ 2 / k)) * ‖siteToPlane z‖ ^ 2 :=
              mul_le_mul_of_nonneg_right (hqPoint z).2 (sq_nonneg _)
        _ = _ := by ring
  have hq2Sum : Summable (fun z : Site => srwKernel k z * ‖siteToPlane z‖ ^ 2) := by
    apply (hraw.2.2.1.mul_left (Ck * (k : ℝ)⁻¹)).of_nonneg_of_le
    · exact fun z => (hq2Point z).1
    · intro z
      simpa only [mul_assoc] using (hq2Point z).2
  refine ⟨hqSum, ?_, hq2Sum, ?_⟩
  · calc
      _ ≤ ∑' z : Site, (Ck * (k : ℝ)⁻¹) *
          Real.exp (-c * ‖siteToPlane z‖ ^ 2 / k) :=
            hqSum.tsum_le_tsum (fun z => by simpa only [mul_assoc] using (hqPoint z).2)
              (hraw.1.mul_left (Ck * (k : ℝ)⁻¹))
      _ = (Ck * (k : ℝ)⁻¹) *
          (∑' z : Site, Real.exp (-c * ‖siteToPlane z‖ ^ 2 / k)) := tsum_mul_left
      _ ≤ (Ck * (k : ℝ)⁻¹) *
          (8 * (1 + Real.pi / c) * k) := by
            apply mul_le_mul_of_nonneg_left hraw.2.1 (by positivity)
      _ = Ck * 8 * (1 + Real.pi / c) := by
            have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
            field_simp [hkne]
  · calc
      _ ≤ ∑' z : Site, (Ck * (k : ℝ)⁻¹) *
          (‖siteToPlane z‖ ^ 2 *
            Real.exp (-c * ‖siteToPlane z‖ ^ 2 / k)) :=
              hq2Sum.tsum_le_tsum (fun z => by
                simpa only [mul_assoc] using (hq2Point z).2)
                (hraw.2.2.1.mul_left (Ck * (k : ℝ)⁻¹))
      _ = (Ck * (k : ℝ)⁻¹) *
          (∑' z : Site, ‖siteToPlane z‖ ^ 2 *
            Real.exp (-c * ‖siteToPlane z‖ ^ 2 / k)) := tsum_mul_left
      _ ≤ (Ck * (k : ℝ)⁻¹) *
          (16 / c * (1 + 2 * Real.pi / c) * k ^ 2) := by
            apply mul_le_mul_of_nonneg_left hraw.2.2.2 (by positivity)
      _ = Ck * 16 / c * (1 + 2 * Real.pi / c) * k := by
            have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
            field_simp [hkne]

/-- Two Gaussian rates give summable convolution mass and second moment bounds with Gaussian spatial decay. -/
theorem hatGaussian_twoRate_mass_moment {c cg : ℝ} (hc : 0 < c)
    (hcc : c < cg) {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n)
    (hkn : 2 * k ≤ n) (w : Site) :
    Summable (fun y : Site => hatGaussian c k y *
      Real.exp (-cg * ‖siteToPlane (w - y)‖ ^ 2 / n)) ∧
      (∑' y : Site, hatGaussian c k y *
        Real.exp (-cg * ‖siteToPlane (w - y)‖ ^ 2 / n) ≤
        8 * (1 + Real.pi / c) * Real.exp
          (-c * ‖siteToPlane w‖ ^ 2 / (k + n))) ∧
      Summable (fun y : Site => hatGaussian c k y * ‖siteToPlane y‖ ^ 2 *
        Real.exp (-cg * ‖siteToPlane (w - y)‖ ^ 2 / n)) ∧
      (∑' y : Site, hatGaussian c k y * ‖siteToPlane y‖ ^ 2 *
        Real.exp (-cg * ‖siteToPlane (w - y)‖ ^ 2 / n) ≤
        (2 * (16 / c * (1 + 2 * Real.pi / c)) +
          2 * (8 * (1 + Real.pi / c)) * (cg / c) ^ 2 /
            (2 * c * (cg - c) / (3 * cg))) * k *
          Real.exp (-c * ‖siteToPlane w‖ ^ 2 / (k + n))) := by
  have hrawMass := rawGaussian_twoRate_control hc (le_of_lt hcc) hk hn w
  have hrawMoment := rawGaussian_twoRate_secondMoment_control hc hcc hk hn hkn w
  obtain ⟨M2, hM2, hrawMomentBound, hM2eq⟩ := hrawMoment
  have hrawMomentSum := rawGaussian_twoRate_secondMoment_summable
    hc (lt_trans hc hcc) (k := k) (n := n) hk w
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hk)
  have hkernelPoint (y : Site) : 0 ≤ hatGaussian c k y ∧
      hatGaussian c k y ≤ (k : ℝ)⁻¹ *
        Real.exp (-c * ‖siteToPlane y‖ ^ 2 / k) := by
    exact ⟨hatGaussian_nonneg k y, hatGaussian_le_rawGaussian hk y⟩
  have hmassPoint (y : Site) :
      0 ≤ hatGaussian c k y * Real.exp (-cg *
          ‖siteToPlane (w - y)‖ ^ 2 / n) ∧
      hatGaussian c k y * Real.exp (-cg *
          ‖siteToPlane (w - y)‖ ^ 2 / n) ≤
        (k : ℝ)⁻¹ * Real.exp (-c * ‖siteToPlane y‖ ^ 2 / k -
          cg * ‖siteToPlane (w - y)‖ ^ 2 / n) := by
    constructor
    · exact mul_nonneg (hkernelPoint y).1 (Real.exp_nonneg _)
    · calc
        _ ≤ ((k : ℝ)⁻¹ * Real.exp (-c * ‖siteToPlane y‖ ^ 2 / k)) *
            Real.exp (-cg * ‖siteToPlane (w - y)‖ ^ 2 / n) :=
              mul_le_mul_of_nonneg_right (hkernelPoint y).2 (Real.exp_nonneg _)
        _ = (k : ℝ)⁻¹ *
            (Real.exp (-c * ‖siteToPlane y‖ ^ 2 / k) *
              Real.exp (-cg * ‖siteToPlane (w - y)‖ ^ 2 / n)) := by ring
        _ = (k : ℝ)⁻¹ * Real.exp
            (-c * ‖siteToPlane y‖ ^ 2 / k +
              (-cg * ‖siteToPlane (w - y)‖ ^ 2 / n)) := by rw [← Real.exp_add]
        _ = _ := by congr 2; ring
  have hmassSum : Summable (fun y : Site => hatGaussian c k y *
      Real.exp (-cg * ‖siteToPlane (w - y)‖ ^ 2 / n)) := by
    apply (hrawMass.1.mul_left ((k : ℝ)⁻¹)).of_nonneg_of_le
    · exact fun y => (hmassPoint y).1
    · exact fun y => (hmassPoint y).2
  have hmomentPoint (y : Site) :
      0 ≤ hatGaussian c k y * ‖siteToPlane y‖ ^ 2 *
          Real.exp (-cg * ‖siteToPlane (w - y)‖ ^ 2 / n) ∧
      hatGaussian c k y * ‖siteToPlane y‖ ^ 2 *
          Real.exp (-cg * ‖siteToPlane (w - y)‖ ^ 2 / n) ≤
        (k : ℝ)⁻¹ * Real.exp (-c * ‖siteToPlane y‖ ^ 2 / k -
          cg * ‖siteToPlane (w - y)‖ ^ 2 / n) * ‖siteToPlane y‖ ^ 2 := by
    constructor
    · exact mul_nonneg
        (mul_nonneg (hkernelPoint y).1 (sq_nonneg _)) (Real.exp_nonneg _)
    · calc
        _ ≤ ((k : ℝ)⁻¹ * Real.exp (-c * ‖siteToPlane y‖ ^ 2 / k)) *
            Real.exp (-cg * ‖siteToPlane (w - y)‖ ^ 2 / n) *
              ‖siteToPlane y‖ ^ 2 := by
                calc
                  _ = (hatGaussian c k y * ‖siteToPlane y‖ ^ 2) *
                      Real.exp (-cg * ‖siteToPlane (w - y)‖ ^ 2 / n) := by ring
                  _ ≤ ((k : ℝ)⁻¹ *
                      Real.exp (-c * ‖siteToPlane y‖ ^ 2 / k) *
                      ‖siteToPlane y‖ ^ 2) *
                      Real.exp (-cg * ‖siteToPlane (w - y)‖ ^ 2 / n) :=
                        mul_le_mul_of_nonneg_right
                          (mul_le_mul_of_nonneg_right (hkernelPoint y).2 (sq_nonneg _))
                          (Real.exp_nonneg _)
                  _ = _ := by ring
        _ = _ := by
          calc
            _ = (k : ℝ)⁻¹ *
                (Real.exp (-c * ‖siteToPlane y‖ ^ 2 / k) *
                  Real.exp (-cg * ‖siteToPlane (w - y)‖ ^ 2 / n)) *
                    ‖siteToPlane y‖ ^ 2 := by ring
            _ = (k : ℝ)⁻¹ * Real.exp
                (-c * ‖siteToPlane y‖ ^ 2 / k +
                  (-cg * ‖siteToPlane (w - y)‖ ^ 2 / n)) *
                    ‖siteToPlane y‖ ^ 2 := by rw [← Real.exp_add]
            _ = _ := by congr 3; ring
  have hmomentSum : Summable (fun y : Site => hatGaussian c k y *
      ‖siteToPlane y‖ ^ 2 *
        Real.exp (-cg * ‖siteToPlane (w - y)‖ ^ 2 / n)) := by
    apply (hrawMomentSum.mul_left ((k : ℝ)⁻¹)).of_nonneg_of_le
    · exact fun y => (hmomentPoint y).1
    · intro y
      calc
        _ ≤ ((k : ℝ)⁻¹ * Real.exp (-c * ‖siteToPlane y‖ ^ 2 / k -
            cg * ‖siteToPlane (w - y)‖ ^ 2 / n)) * ‖siteToPlane y‖ ^ 2 :=
              (hmomentPoint y).2
        _ = (k : ℝ)⁻¹ *
            (Real.exp (-c * ‖siteToPlane y‖ ^ 2 / k -
              cg * ‖siteToPlane (w - y)‖ ^ 2 / n) * ‖siteToPlane y‖ ^ 2) := by ring
  refine ⟨hmassSum, ?_, hmomentSum, ?_⟩
  · calc
      _ ≤ ∑' y : Site, (k : ℝ)⁻¹ *
          Real.exp (-c * ‖siteToPlane y‖ ^ 2 / k -
            cg * ‖siteToPlane (w - y)‖ ^ 2 / n) :=
              hmassSum.tsum_le_tsum (fun y => (hmassPoint y).2)
                (hrawMass.1.mul_left ((k : ℝ)⁻¹))
      _ = (k : ℝ)⁻¹ *
          (∑' y : Site, Real.exp (-c * ‖siteToPlane y‖ ^ 2 / k -
            cg * ‖siteToPlane (w - y)‖ ^ 2 / n)) := tsum_mul_left
      _ ≤ (k : ℝ)⁻¹ * (8 * (1 + Real.pi / c) * k *
          Real.exp (-c * ‖siteToPlane w‖ ^ 2 / (k + n))) := by
            exact mul_le_mul_of_nonneg_left hrawMass.2 (inv_nonneg.mpr hkR.le)
      _ = _ := by field_simp [ne_of_gt hkR]
  · calc
      _ ≤ ∑' y : Site, (k : ℝ)⁻¹ *
          (Real.exp (-c * ‖siteToPlane y‖ ^ 2 / k -
            cg * ‖siteToPlane (w - y)‖ ^ 2 / n) * ‖siteToPlane y‖ ^ 2) :=
              hmomentSum.tsum_le_tsum (fun y => by
                calc
                  _ ≤ ((k : ℝ)⁻¹ *
                      Real.exp (-c * ‖siteToPlane y‖ ^ 2 / k -
                        cg * ‖siteToPlane (w - y)‖ ^ 2 / n)) *
                        ‖siteToPlane y‖ ^ 2 := (hmomentPoint y).2
                  _ = _ := by ring)
                (hrawMomentSum.mul_left ((k : ℝ)⁻¹))
      _ = (k : ℝ)⁻¹ *
          (∑' y : Site, Real.exp (-c * ‖siteToPlane y‖ ^ 2 / k -
            cg * ‖siteToPlane (w - y)‖ ^ 2 / n) * ‖siteToPlane y‖ ^ 2) := tsum_mul_left
      _ ≤ (k : ℝ)⁻¹ * (M2 * k ^ 2 *
          Real.exp (-c * ‖siteToPlane w‖ ^ 2 / (k + n))) := by
            exact mul_le_mul_of_nonneg_left hrawMomentBound
              (inv_nonneg.mpr hkR.le)
      _ = _ := by
            rw [hM2eq]
            field_simp [ne_of_gt hkR]

/-- A Gaussian walk bound gives summable weighted mass and second moment bounds with Gaussian spatial decay. -/
theorem srwKernel_twoRate_mass_moment {c cg Ck : ℝ} (hc : 0 < c)
    (hcc : c < cg) (hCk : 0 ≤ Ck)
    (hkernel : ∀ n x, srwKernel n x ≤ Ck * hatGaussian c n x)
    {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) (hkn : 2 * k ≤ n)
    (w : Site) :
    Summable (fun z : Site => srwKernel k z *
      Real.exp (-cg * ‖siteToPlane (w - z)‖ ^ 2 / n)) ∧
      (∑' z : Site, srwKernel k z *
        Real.exp (-cg * ‖siteToPlane (w - z)‖ ^ 2 / n) ≤
        Ck * 8 * (1 + Real.pi / c) * Real.exp
          (-c * ‖siteToPlane w‖ ^ 2 / (k + n))) ∧
      Summable (fun z : Site => srwKernel k z * ‖siteToPlane z‖ ^ 2 *
        Real.exp (-cg * ‖siteToPlane (w - z)‖ ^ 2 / n)) ∧
      (∑' z : Site, srwKernel k z * ‖siteToPlane z‖ ^ 2 *
        Real.exp (-cg * ‖siteToPlane (w - z)‖ ^ 2 / n) ≤
        Ck * (2 * (16 / c * (1 + 2 * Real.pi / c)) +
          2 * (8 * (1 + Real.pi / c)) * (cg / c) ^ 2 /
            (2 * c * (cg - c) / (3 * cg))) * k *
          Real.exp (-c * ‖siteToPlane w‖ ^ 2 / (k + n))) := by
  obtain ⟨hhat0, hhat0Bound, hhat2, hhat2Bound⟩ :=
    hatGaussian_twoRate_mass_moment hc hcc hk hn hkn w
  have hqPoint (z : Site) : 0 ≤ srwKernel k z ∧
      srwKernel k z ≤ Ck * hatGaussian c k z := by
    exact ⟨Critical2DKPZ.srwKernel_nonneg _ _, hkernel k z⟩
  have hq0Point (z : Site) :
      0 ≤ srwKernel k z * Real.exp (-cg * ‖siteToPlane (w - z)‖ ^ 2 / n) ∧
      srwKernel k z * Real.exp (-cg * ‖siteToPlane (w - z)‖ ^ 2 / n) ≤
        Ck * (hatGaussian c k z *
          Real.exp (-cg * ‖siteToPlane (w - z)‖ ^ 2 / n)) := by
    constructor
    · exact mul_nonneg (hqPoint z).1 (Real.exp_nonneg _)
    · calc
        _ ≤ (Ck * hatGaussian c k z) *
            Real.exp (-cg * ‖siteToPlane (w - z)‖ ^ 2 / n) :=
              mul_le_mul_of_nonneg_right (hqPoint z).2 (Real.exp_nonneg _)
        _ = _ := by ring
  have hq0 : Summable (fun z : Site => srwKernel k z *
      Real.exp (-cg * ‖siteToPlane (w - z)‖ ^ 2 / n)) := by
    apply (hhat0.mul_left Ck).of_nonneg_of_le
    · exact fun z => (hq0Point z).1
    · exact fun z => (hq0Point z).2
  have hq2Point (z : Site) :
      0 ≤ srwKernel k z * ‖siteToPlane z‖ ^ 2 *
        Real.exp (-cg * ‖siteToPlane (w - z)‖ ^ 2 / n) ∧
      srwKernel k z * ‖siteToPlane z‖ ^ 2 *
        Real.exp (-cg * ‖siteToPlane (w - z)‖ ^ 2 / n) ≤
        Ck * (hatGaussian c k z * ‖siteToPlane z‖ ^ 2 *
          Real.exp (-cg * ‖siteToPlane (w - z)‖ ^ 2 / n)) := by
    constructor
    · exact mul_nonneg
        (mul_nonneg (hqPoint z).1 (sq_nonneg _)) (Real.exp_nonneg _)
    · calc
        _ ≤ (Ck * hatGaussian c k z) * ‖siteToPlane z‖ ^ 2 *
            Real.exp (-cg * ‖siteToPlane (w - z)‖ ^ 2 / n) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (hqPoint z).2 (sq_nonneg _))
                (Real.exp_nonneg _)
        _ = _ := by ring
  have hq2 : Summable (fun z : Site => srwKernel k z *
      ‖siteToPlane z‖ ^ 2 *
        Real.exp (-cg * ‖siteToPlane (w - z)‖ ^ 2 / n)) := by
    apply (hhat2.mul_left Ck).of_nonneg_of_le
    · exact fun z => (hq2Point z).1
    · exact fun z => (hq2Point z).2
  refine ⟨hq0, ?_, hq2, ?_⟩
  · calc
      _ ≤ ∑' z : Site, Ck *
          (hatGaussian c k z *
            Real.exp (-cg * ‖siteToPlane (w - z)‖ ^ 2 / n)) :=
              hq0.tsum_le_tsum (fun z => (hq0Point z).2)
                (hhat0.mul_left Ck)
      _ = Ck * (∑' z : Site, hatGaussian c k z *
          Real.exp (-cg * ‖siteToPlane (w - z)‖ ^ 2 / n)) := tsum_mul_left
      _ ≤ Ck * (8 * (1 + Real.pi / c) * Real.exp
          (-c * ‖siteToPlane w‖ ^ 2 / (k + n))) :=
            mul_le_mul_of_nonneg_left hhat0Bound hCk
      _ = _ := by ring
  · calc
      _ ≤ ∑' z : Site, Ck *
          (hatGaussian c k z * ‖siteToPlane z‖ ^ 2 *
            Real.exp (-cg * ‖siteToPlane (w - z)‖ ^ 2 / n)) :=
              hq2.tsum_le_tsum (fun z => (hq2Point z).2)
                (hhat2.mul_left Ck)
      _ = Ck * (∑' z : Site, hatGaussian c k z * ‖siteToPlane z‖ ^ 2 *
          Real.exp (-cg * ‖siteToPlane (w - z)‖ ^ 2 / n)) := tsum_mul_left
      _ ≤ Ck * ((2 * (16 / c * (1 + 2 * Real.pi / c)) +
          2 * (8 * (1 + Real.pi / c)) * (cg / c) ^ 2 /
            (2 * c * (cg - c) / (3 * cg))) * k *
          Real.exp (-c * ‖siteToPlane w‖ ^ 2 / (k + n))) :=
            mul_le_mul_of_nonneg_left hhat2Bound hCk
      _ = _ := by ring

private theorem even_sameParity_gradient {k : ℕ} {w y z : Site}
    (hy : Even ((k : ℤ) + y 0 + y 1))
    (hz : Even ((k : ℤ) + z 0 + z 1)) :
    Even ((w - y) 0 + (w - y) 1 + (w - z) 0 + (w - z) 1) := by
  apply Int.even_iff.mpr
  have hy' := Int.even_iff.mp hy
  have hz' := Int.even_iff.mp hz
  simp only [Pi.sub_apply]
  omega

/-- A nonzero parity restricted Gaussian kernel has compatible time and site parity. -/
theorem even_of_hatGaussian_ne_zero {c : ℝ} {k : ℕ} {y : Site}
    (hk : 1 ≤ k) (h : hatGaussian c k y ≠ 0) :
    Even ((k : ℤ) + y 0 + y 1) := by
  by_cases hp : Even ((k : ℤ) + y 0 + y 1)
  · exact hp
  · have hk0 : k ≠ 0 := by omega
    have hzero : hatGaussian c k y = 0 := by simp [hatGaussian, hk0, hp]
    exact (h hzero).elim

private theorem even_of_srwKernel_ne_zero {k : ℕ} {z : Site}
    (h : srwKernel k z ≠ 0) : Even ((k : ℤ) + z 0 + z 1) := by
  by_contra hpar
  exact h (srwKernel_eq_zero_of_not_hatGaussianParity hpar)

private theorem siteDifference_norm_sq_le {w y z : Site} :
    ‖siteToPlane ((w - y) - (w - z))‖ ^ 2 ≤
      2 * ‖siteToPlane y‖ ^ 2 + 2 * ‖siteToPlane z‖ ^ 2 := by
  have hsub : (w - y) - (w - z) = z - y := by
    ext i
    simp only [Pi.sub_apply]
    omega
  rw [hsub, siteToPlane_sub]
  apply sq_le_two_sq_add (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  simpa [add_comm] using norm_sub_le (siteToPlane z) (siteToPlane y)

/-- A pointwise walk gradient estimate bounds its walk average through weighted mass and second moments. -/
theorem kernelGradient_average_bound {cg Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgrad : ∀ n : ℕ, 1 ≤ n → ∀ z z' : Site,
      Even (z 0 + z 1 + z' 0 + z' 1) →
      (srwKernel n z - srwKernel n z') ^ 2 ≤
        Cg * ‖siteToPlane (z - z')‖ ^ 2 / (n : ℝ) ^ 3 *
          (Real.exp (-cg * ‖siteToPlane z‖ ^ 2 / n) +
            Real.exp (-cg * ‖siteToPlane z'‖ ^ 2 / n)))
    {k n : ℕ} (hn : 1 ≤ n) (w y : Site) (ey : ℝ)
    (hEyEq : ey = Real.exp (-cg * ‖siteToPlane (w - y)‖ ^ 2 / n))
    (hy : Even ((k : ℤ) + y 0 + y 1))
    (hq0 : Summable (fun z : Site => srwKernel k z))
    (hq0w : Summable (fun z : Site => srwKernel k z *
      Real.exp (-cg * ‖siteToPlane (w - z)‖ ^ 2 / n)))
    (hq2 : Summable (fun z : Site => srwKernel k z * ‖siteToPlane z‖ ^ 2))
    (hq2w : Summable (fun z : Site => srwKernel k z * ‖siteToPlane z‖ ^ 2 *
      Real.exp (-cg * ‖siteToPlane (w - z)‖ ^ 2 / n))) :
    ∑' z : Site, srwKernel k z *
      (srwKernel n (w - y) - srwKernel n (w - z)) ^ 2 ≤
    Cg / (n : ℝ) ^ 3 *
      (2 * ‖siteToPlane y‖ ^ 2 *
          (ey * (∑' z : Site, srwKernel k z) +
            ∑' z : Site, srwKernel k z *
              Real.exp (-cg * ‖siteToPlane (w - z)‖ ^ 2 / n)) +
        2 * (ey * (∑' z : Site, srwKernel k z * ‖siteToPlane z‖ ^ 2) +
            ∑' z : Site, srwKernel k z * ‖siteToPlane z‖ ^ 2 *
              Real.exp (-cg * ‖siteToPlane (w - z)‖ ^ 2 / n))) := by
  let q0 : Site → ℝ := fun z => srwKernel k z
  let q0w : Site → ℝ := fun z => srwKernel k z *
    Real.exp (-cg * ‖siteToPlane (w - z)‖ ^ 2 / n)
  let q2 : Site → ℝ := fun z => srwKernel k z * ‖siteToPlane z‖ ^ 2
  let q2w : Site → ℝ := fun z => srwKernel k z * ‖siteToPlane z‖ ^ 2 *
    Real.exp (-cg * ‖siteToPlane (w - z)‖ ^ 2 / n)
  let a : ℝ := 2 * ‖siteToPlane y‖ ^ 2 * ey
  let b : ℝ := 2 * ‖siteToPlane y‖ ^ 2
  let d : ℝ := 2 * ey
  let e : ℝ := 2
  let A : ℝ := Cg / (n : ℝ) ^ 3
  let major : Site → ℝ := fun z => A *
    ((a * q0 z + b * q0w z) + (d * q2 z + e * q2w z))
  have heynonneg : 0 ≤ ey := by rw [hEyEq]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hmajorSummable : Summable major := by
    have hpieces : Summable (fun z : Site =>
        (a * q0 z + b * q0w z) + (d * q2 z + e * q2w z)) :=
      ((hq0.mul_left a).add (hq0w.mul_left b)).add
        ((hq2.mul_left d).add (hq2w.mul_left e))
    simpa [major, q0, q0w, q2, q2w, add_assoc] using hpieces.mul_left A
  have hmajorEq : (∑' z : Site, major z) = A *
      (a * (∑' z : Site, q0 z) + b * (∑' z : Site, q0w z) +
        d * (∑' z : Site, q2 z) + e * (∑' z : Site, q2w z)) := by
    calc
      _ = A * (∑' z : Site,
          ((a * q0 z + b * q0w z) + (d * q2 z + e * q2w z))) := by
            dsimp [major]
            rw [tsum_mul_left]
      _ = A * ((∑' z : Site, (a * q0 z + b * q0w z)) +
          (∑' z : Site, (d * q2 z + e * q2w z))) := by
            rw [Summable.tsum_add ((hq0.mul_left a).add (hq0w.mul_left b))
              ((hq2.mul_left d).add (hq2w.mul_left e))]
      _ = _ := by
            rw [Summable.tsum_add (hq0.mul_left a) (hq0w.mul_left b),
              Summable.tsum_add (hq2.mul_left d) (hq2w.mul_left e),
              tsum_mul_left, tsum_mul_left, tsum_mul_left, tsum_mul_left]
            simp [q0, q0w, q2, q2w, add_assoc]
  have hpoint (z : Site) : 0 ≤ srwKernel k z *
        (srwKernel n (w - y) - srwKernel n (w - z)) ^ 2 ∧
      srwKernel k z * (srwKernel n (w - y) - srwKernel n (w - z)) ^ 2 ≤ major z := by
    have hq : 0 ≤ srwKernel k z := Critical2DKPZ.srwKernel_nonneg _ _
    let ez : ℝ := Real.exp (-cg * ‖siteToPlane (w - z)‖ ^ 2 / n)
    have hEzEq : ez = Real.exp (-cg * ‖siteToPlane (w - z)‖ ^ 2 / n) := rfl
    have hEzNonneg : 0 ≤ ez := by rw [hEzEq]; positivity
    have hySq : 0 ≤ ‖siteToPlane y‖ ^ 2 := sq_nonneg _
    have hzSq : 0 ≤ ‖siteToPlane z‖ ^ 2 := sq_nonneg _
    have hnorm := siteDifference_norm_sq_le (w := w) (y := y) (z := z)
    by_cases hqzero : srwKernel k z = 0
    · constructor
      · simp [hqzero]
      · simp [major, a, b, d, e, q0, q0w, q2, q2w, A, hqzero]
    · have hzpar := even_of_srwKernel_ne_zero hqzero
      have hpar := even_sameParity_gradient (w := w) (y := y) (z := z) hy hzpar
      have hgrad' := hgrad n hn (w - y) (w - z) hpar
      rw [← hEyEq, ← hEzEq] at hgrad'
      have hgradBound :
          (srwKernel n (w - y) - srwKernel n (w - z)) ^ 2 ≤
            Cg / (n : ℝ) ^ 3 * (2 * ‖siteToPlane y‖ ^ 2 +
              2 * ‖siteToPlane z‖ ^ 2) * (ey + ez) := by
        calc
          _ ≤ Cg * ‖siteToPlane ((w - y) - (w - z))‖ ^ 2 /
                (n : ℝ) ^ 3 * (ey + ez) := by
              simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hgrad'
          _ ≤ Cg / (n : ℝ) ^ 3 *
                (2 * ‖siteToPlane y‖ ^ 2 + 2 * ‖siteToPlane z‖ ^ 2) * (ey + ez) := by
              have hcoef : 0 ≤ Cg / (n : ℝ) ^ 3 := by positivity
              apply mul_le_mul_of_nonneg_right _ (add_nonneg heynonneg hEzNonneg)
              calc
                _ = (Cg / (n : ℝ) ^ 3) *
                    ‖siteToPlane ((w - y) - (w - z))‖ ^ 2 := by ring
                _ ≤ (Cg / (n : ℝ) ^ 3) *
                    (2 * ‖siteToPlane y‖ ^ 2 + 2 * ‖siteToPlane z‖ ^ 2) :=
                      mul_le_mul_of_nonneg_left hnorm hcoef
                _ = _ := by ring
      constructor
      · exact mul_nonneg hq (sq_nonneg _)
      · calc
          _ ≤ srwKernel k z *
              (Cg / (n : ℝ) ^ 3 *
                (2 * ‖siteToPlane y‖ ^ 2 + 2 * ‖siteToPlane z‖ ^ 2) * (ey + ez)) :=
                mul_le_mul_of_nonneg_left hgradBound hq
          _ = major z := by dsimp [major, a, b, d, e, q0, q0w, q2, q2w, A, ez]; ring
  have hsum := hmajorSummable.of_nonneg_of_le
    (fun z => (hpoint z).1) (fun z => (hpoint z).2)
  calc
    _ ≤ ∑' z : Site, major z :=
      hsum.tsum_le_tsum (fun z => (hpoint z).2) hmajorSummable
    _ = _ := by
      rw [hmajorEq]
      dsimp [a, b, d, e, q0, q0w, q2, q2w, A]
      ring


end Critical2DKPZ.Collision

end
