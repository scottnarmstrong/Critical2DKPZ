/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Collision.SpatialGaussian
public import Critical2DKPZ.Collision.SpatialVarianceCore
import Critical2DKPZ.Polymer.WalkKernel
import Critical2DKPZ.Lattice.Basic
import Critical2DKPZ.WalkTails.SameParityGradient

/-! # Far-time same-parity walk variance estimate -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.Collision

open WalkTails
open scoped BigOperators

/-- Gaussian averaging bounds the squared walk kernel difference by a time ratio with Gaussian spatial decay. -/
theorem hatGaussian_sq_diff_far_raw {c cg Ck Cg : ℝ}
    (hc : 0 < c) (hcc : c < cg) (hCk : 0 ≤ Ck) (hCg : 0 ≤ Cg)
    (hkernel : ∀ n x, srwKernel n x ≤ Ck * hatGaussian c n x)
    (hgrad : ∀ n : ℕ, 1 ≤ n → ∀ z z' : Site,
      Even (z 0 + z 1 + z' 0 + z' 1) →
      (srwKernel n z - srwKernel n z') ^ 2 ≤
        Cg * ‖siteToPlane (z - z')‖ ^ 2 / (n : ℝ) ^ 3 *
          (Real.exp (-cg * ‖siteToPlane z‖ ^ 2 / n) +
            Real.exp (-cg * ‖siteToPlane z'‖ ^ 2 / n)))
    {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) (hkn : 2 * k ≤ n)
    (w : Site) :
    ∑' y : Site, hatGaussian c k y *
        (srwKernel n (w - y) - srwKernel (k + n) w) ^ 2 ≤
      Cg * Ck * (4 * (8 * (1 + Real.pi / c)) *
          ((2 * (16 / c * (1 + 2 * Real.pi / c)) +
              2 * (8 * (1 + Real.pi / c)) * (cg / c) ^ 2 /
                (2 * c * (cg - c) / (3 * cg))) +
            16 / c * (1 + 2 * Real.pi / c)) +
        2 * (2 * (16 / c * (1 + 2 * Real.pi / c)) +
            2 * (8 * (1 + Real.pi / c)) * (cg / c) ^ 2 /
              (2 * c * (cg - c) / (3 * cg))) *
          (1 + Real.sqrt (Real.pi / c)) ^ 2) *
        k / (n : ℝ) ^ 3 * Real.exp
          (-c * ‖siteToPlane w‖ ^ 2 / (k + n)) := by
  let A0 : ℝ := 8 * (1 + Real.pi / c)
  let A2 : ℝ := 16 / c * (1 + 2 * Real.pi / c)
  let B2 : ℝ := 2 * A2 + 2 * A0 *
    (cg / c) ^ 2 / (2 * c * (cg - c) / (3 * cg))
  let M0 : ℝ := (1 + Real.sqrt (Real.pi / c)) ^ 2
  let E : ℝ := Real.exp (-c * ‖siteToPlane w‖ ^ 2 / (k + n))
  let ey : Site → ℝ := fun y =>
    Real.exp (-cg * ‖siteToPlane (w - y)‖ ^ 2 / n)
  let q0 : ℝ := ∑' z : Site, srwKernel k z
  let q2 : ℝ := ∑' z : Site, srwKernel k z * ‖siteToPlane z‖ ^ 2
  let q0w : ℝ := ∑' z : Site, srwKernel k z * ey z
  let q2w : ℝ := ∑' z : Site,
    srwKernel k z * ‖siteToPlane z‖ ^ 2 * ey z
  let y0 : ℝ := ∑' y : Site, hatGaussian c k y
  let y2 : ℝ := ∑' y : Site, hatGaussian c k y * ‖siteToPlane y‖ ^ 2
  let y0w : ℝ := ∑' y : Site, hatGaussian c k y * ey y
  let y2w : ℝ := ∑' y : Site,
    hatGaussian c k y * ‖siteToPlane y‖ ^ 2 * ey y
  let f1 : Site → ℝ := fun y => hatGaussian c k y *
    ‖siteToPlane y‖ ^ 2 * ey y
  let f2 : Site → ℝ := fun y => hatGaussian c k y * ‖siteToPlane y‖ ^ 2
  let f3 : Site → ℝ := fun y => hatGaussian c k y * ey y
  let f4 : Site → ℝ := fun y => hatGaussian c k y
  let major : Site → ℝ := fun y => Cg / (n : ℝ) ^ 3 *
    (2 * q0 * f1 y + 2 * q0w * f2 y + 2 * q2 * f3 y + 2 * q2w * f4 y)
  have hA0 : 0 ≤ A0 := by dsimp [A0]; positivity
  have hA2 : 0 ≤ A2 := by dsimp [A2]; positivity
  have hcg : 0 < cg := lt_trans hc hcc
  have hcgGap : 0 < cg - c := sub_pos.mpr hcc
  have hB2 : 0 ≤ B2 := by
    dsimp [B2, A0, A2]
    positivity
  have hM0 : 0 ≤ M0 := by dsimp [M0]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hq := srwKernel_gaussian_mass_moment hc hCk hkernel hk
  have hqLocal := srwKernel_twoRate_mass_moment hc hcc hCk hkernel hk hn hkn w
  have hYLocal := hatGaussian_twoRate_mass_moment hc hcc hk hn hkn w
  have hy0 : Summable f4 := by
    simpa [f4] using hatGaussian_summable hc hk
  have hy2 := hatGaussian_secondMoment_le hc hk
  have hf1 : Summable f1 := by simpa [f1, ey] using hYLocal.2.2.1
  have hf2 : Summable f2 := by simpa [f2] using hy2.1
  have hf3 : Summable f3 := by simpa [f3, ey] using hYLocal.1
  have hf4 : Summable f4 := hy0
  have hq0 : Summable (fun z : Site => srwKernel k z) := hq.1
  have hq2 : Summable (fun z : Site => srwKernel k z * ‖siteToPlane z‖ ^ 2) := hq.2.2.1
  have hq0w : Summable (fun z : Site => srwKernel k z * ey z) := by
    simpa [ey] using hqLocal.1
  have hq2w : Summable (fun z : Site =>
      srwKernel k z * ‖siteToPlane z‖ ^ 2 * ey z) := by
    simpa [ey] using hqLocal.2.2.1
  have hmajor : Summable major := by
    have hp1 := hf1.mul_left (2 * q0)
    have hp2 := hf2.mul_left (2 * q0w)
    have hp3 := hf3.mul_left (2 * q2)
    have hp4 := hf4.mul_left (2 * q2w)
    have hpieces : Summable (fun y : Site =>
        2 * q0 * f1 y + 2 * q0w * f2 y + 2 * q2 * f3 y + 2 * q2w * f4 y) := by
      simpa [add_assoc] using ((hp1.add hp2).add hp3).add hp4
    simpa [major] using hpieces.mul_left (Cg / (n : ℝ) ^ 3)
  have hpoint (y : Site) :
      0 ≤ hatGaussian c k y *
          (srwKernel n (w - y) - srwKernel (k + n) w) ^ 2 ∧
      hatGaussian c k y *
          (srwKernel n (w - y) - srwKernel (k + n) w) ^ 2 ≤ major y := by
    have hg : 0 ≤ hatGaussian c k y := hatGaussian_nonneg k y
    constructor
    · exact mul_nonneg hg (sq_nonneg _)
    · by_cases hzero : hatGaussian c k y = 0
      · simp [major, f1, f2, f3, f4, hzero]
      · have hypar := even_of_hatGaussian_ne_zero hk hzero
        have hinner := kernelGradient_average_bound hCg hgrad hn w y (ey y) rfl
          hypar hq0 hq0w hq2 hq2w
        have haverage :
            ∑' z : Site, srwKernel k z *
                (srwKernel n (w - y) - srwKernel n (w - z)) ^ 2 ≤
              Cg / (n : ℝ) ^ 3 *
                (2 * ‖siteToPlane y‖ ^ 2 * (ey y * q0 + q0w) +
                  2 * (ey y * q2 + q2w)) := by
          simpa [q0, q2, q0w, q2w, ey] using hinner
        have hJensen :
            (srwKernel n (w - y) - srwKernel (k + n) w) ^ 2 ≤
              ∑' z : Site, srwKernel k z *
                (srwKernel n (w - y) - srwKernel n (w - z)) ^ 2 := by
          exact kernelVariance_jensen w y
        have hcombined := le_trans hJensen haverage
        calc
          _ ≤ hatGaussian c k y *
              (Cg / (n : ℝ) ^ 3 *
                (2 * ‖siteToPlane y‖ ^ 2 * (ey y * q0 + q0w) +
                  2 * (ey y * q2 + q2w))) :=
                mul_le_mul_of_nonneg_left hcombined hg
          _ = major y := by
                dsimp [major, f1, f2, f3, f4]
                dsimp [q0, q2, q0w, q2w, ey]
                ring
  have hsum := hmajor.of_nonneg_of_le (fun y => (hpoint y).1)
    (fun y => (hpoint y).2)
  have hmajorEq :
      (∑' y : Site, major y) = Cg / (n : ℝ) ^ 3 *
        (2 * q0 * y2w + 2 * q0w * y2 + 2 * q2 * y0w + 2 * q2w * y0) := by
    dsimp [major]
    rw [tsum_mul_left]
    have hp1 := hf1.mul_left (2 * q0)
    have hp2 := hf2.mul_left (2 * q0w)
    have hp3 := hf3.mul_left (2 * q2)
    have hp4 := hf4.mul_left (2 * q2w)
    rw [Summable.tsum_add ((hp1.add hp2).add hp3) hp4]
    rw [Summable.tsum_add (hp1.add hp2) hp3]
    rw [Summable.tsum_add hp1 hp2]
    simp only [tsum_mul_left]
    rfl
  have hsumBound :
      2 * q0 * y2w + 2 * q0w * y2 + 2 * q2 * y0w + 2 * q2w * y0 ≤
        Ck * (k : ℝ) * E *
          (2 * A0 * B2 + 4 * A0 * A2 + 2 * B2 * M0) := by
    have hq0Bound : q0 ≤ Ck * A0 := by
      dsimp [q0]
      calc
        _ ≤ Ck * 8 * (1 + Real.pi / c) := hq.2.1
        _ = Ck * A0 := by dsimp [A0]; ring
    have hq2Bound : q2 ≤ Ck * A2 * k := by
      dsimp [q2]
      calc
        _ ≤ Ck * 16 / c * (1 + 2 * Real.pi / c) * k := hq.2.2.2
        _ = Ck * A2 * k := by dsimp [A2]; ring
    have hq0wBound : q0w ≤ Ck * A0 * E := by
      dsimp [q0w, ey]
      calc
        _ ≤ Ck * 8 * (1 + Real.pi / c) * E := by
          simpa only [E] using hqLocal.2.1
        _ = Ck * A0 * E := by dsimp [A0]; ring
    have hq2wBound : q2w ≤ Ck * B2 * k * E := by
      dsimp [q2w, ey]
      calc
        _ ≤ Ck * (2 * (16 / c * (1 + 2 * Real.pi / c)) +
            2 * (8 * (1 + Real.pi / c)) * (cg / c) ^ 2 /
              (2 * c * (cg - c) / (3 * cg))) * k * E := by
          simpa only [E] using hqLocal.2.2.2
        _ = Ck * B2 * k * E := by simp [B2, A0, A2]
    have hy0Bound : y0 ≤ M0 := by
      dsimp [y0, M0]
      exact hatGaussian_totalMass_le hc hk
    have hy2Bound : y2 ≤ A2 * k := by
      dsimp [y2]
      simpa [A2] using hy2.2
    have hy0wBound : y0w ≤ A0 * E := by
      simpa [y0w, ey, A0, E] using hYLocal.2.1
    have hy2wBound : y2w ≤ B2 * k * E := by
      dsimp [y2w, ey]
      calc
        _ ≤ (2 * (16 / c * (1 + 2 * Real.pi / c)) +
            2 * (8 * (1 + Real.pi / c)) * (cg / c) ^ 2 /
              (2 * c * (cg - c) / (3 * cg))) * k * E := by
          simpa [A0, A2, E] using hYLocal.2.2.2
        _ = B2 * k * E := by simp [B2, A0, A2]
    have hq0bnonneg : 0 ≤ Ck * A0 := mul_nonneg hCk hA0
    have hq2bnonneg : 0 ≤ Ck * A2 * k := by positivity
    have hq0wbnonneg : 0 ≤ Ck * A0 * E := by positivity
    have hq2wbnonneg : 0 ≤ Ck * B2 * k * E := by positivity
    have hq0wnonneg : 0 ≤ q0w := by
      dsimp [q0w]
      exact tsum_nonneg (fun z => mul_nonneg
        (Critical2DKPZ.srwKernel_nonneg k z) (Real.exp_nonneg _))
    have hy0bnonneg : 0 ≤ y0 := by
      dsimp [y0]
      exact tsum_nonneg (fun y => hatGaussian_nonneg (c := c) k y)
    have hy2wnonneg : 0 ≤ y2w := by
      dsimp [y2w]
      exact tsum_nonneg (fun y => mul_nonneg
        (mul_nonneg (hatGaussian_nonneg (c := c) k y) (sq_nonneg _))
        (Real.exp_nonneg _))
    have hy2nonneg : 0 ≤ y2 := by
      dsimp [y2]
      exact tsum_nonneg (fun y => mul_nonneg (hatGaussian_nonneg (c := c) k y) (sq_nonneg _))
    have hy0wnonneg : 0 ≤ y0w := by
      dsimp [y0w]
      exact tsum_nonneg (fun y => mul_nonneg
        (hatGaussian_nonneg (c := c) k y) (Real.exp_nonneg _))
    have h1 : q0 * y2w ≤ (Ck * A0) * (B2 * k * E) := by
      calc
        _ ≤ (Ck * A0) * y2w :=
          mul_le_mul_of_nonneg_right hq0Bound hy2wnonneg
        _ ≤ (Ck * A0) * (B2 * k * E) :=
          mul_le_mul_of_nonneg_left hy2wBound hq0bnonneg
    have h2 : q0w * y2 ≤ (Ck * A0 * E) * (A2 * k) := by
      calc
        _ ≤ q0w * (A2 * k) :=
          mul_le_mul_of_nonneg_left hy2Bound hq0wnonneg
        _ ≤ (Ck * A0 * E) * (A2 * k) :=
          mul_le_mul_of_nonneg_right hq0wBound (by positivity)
    have h3 : q2 * y0w ≤ (Ck * A2 * k) * (A0 * E) := by
      calc
        _ ≤ (Ck * A2 * k) * y0w :=
          mul_le_mul_of_nonneg_right hq2Bound hy0wnonneg
        _ ≤ (Ck * A2 * k) * (A0 * E) :=
          mul_le_mul_of_nonneg_left hy0wBound hq2bnonneg
    have h4 : q2w * y0 ≤ (Ck * B2 * k * E) * M0 := by
      calc
        _ ≤ (Ck * B2 * k * E) * y0 :=
          mul_le_mul_of_nonneg_right hq2wBound hy0bnonneg
        _ ≤ (Ck * B2 * k * E) * M0 :=
          mul_le_mul_of_nonneg_left hy0Bound hq2wbnonneg
    calc
      2 * q0 * y2w + 2 * q0w * y2 + 2 * q2 * y0w + 2 * q2w * y0 =
          2 * (q0 * y2w) + 2 * (q0w * y2) +
            2 * (q2 * y0w) + 2 * (q2w * y0) := by ring
      _ ≤ 2 * ((Ck * A0) * (B2 * k * E)) +
          2 * ((Ck * A0 * E) * (A2 * k)) +
          2 * ((Ck * A2 * k) * (A0 * E)) +
          2 * ((Ck * B2 * k * E) * M0) := by
        exact add_le_add (add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left h1 (by norm_num))
          (mul_le_mul_of_nonneg_left h2 (by norm_num)))
          (mul_le_mul_of_nonneg_left h3 (by norm_num)))
          (mul_le_mul_of_nonneg_left h4 (by norm_num))
      _ = Ck * (k : ℝ) * E *
          (2 * A0 * B2 + 4 * A0 * A2 + 2 * B2 * M0) := by ring
  have hsumBound' :
      2 * q0 * y2w + 2 * q0w * y2 + 2 * q2 * y0w + 2 * q2w * y0 ≤
        Ck * (k : ℝ) * E * (4 * A0 * (B2 + A2) + 2 * B2 * M0) := by
    have hconst : 2 * A0 * B2 + 4 * A0 * A2 + 2 * B2 * M0 ≤
        4 * A0 * (B2 + A2) + 2 * B2 * M0 := by
      have hnonneg : 0 ≤ 2 * A0 * B2 := by positivity
      calc
        _ = (2 * A0 * B2 + 4 * A0 * A2 + 2 * B2 * M0) + 0 := by ring
        _ ≤ (2 * A0 * B2 + 4 * A0 * A2 + 2 * B2 * M0) + 2 * A0 * B2 :=
          add_le_add (le_refl _) hnonneg
        _ = _ := by ring
    calc
      _ ≤ Ck * (k : ℝ) * E *
          (2 * A0 * B2 + 4 * A0 * A2 + 2 * B2 * M0) := hsumBound
      _ ≤ _ := mul_le_mul_of_nonneg_left hconst (by positivity)
  have hsumfinal :
      (∑' y : Site, major y) ≤
        Cg * Ck * (4 * A0 * (B2 + A2) + 2 * B2 * M0) *
          k / (n : ℝ) ^ 3 * E := by
    rw [hmajorEq]
    have hcoef : 0 ≤ Cg / (n : ℝ) ^ 3 := by positivity
    calc
      _ ≤ Cg / (n : ℝ) ^ 3 *
          (Ck * (k : ℝ) * E * (4 * A0 * (B2 + A2) + 2 * B2 * M0)) :=
            mul_le_mul_of_nonneg_left hsumBound' hcoef
      _ = _ := by ring
  calc
    _ ≤ ∑' y : Site, major y :=
      hsum.tsum_le_tsum (fun y => (hpoint y).2) hmajor
    _ ≤ _ := hsumfinal

/-- The walk-kernel bound, Gaussian convolution bound, and same-parity variance bound hold with a common constant. The Gaussian envelopes are summable by `hatGaussian_summable` at positive times. -/
theorem hatGaussian_bounds :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, 0 < c → c ≤ c₀ → ∃ C : ℝ,
      (∀ n x, srwKernel n x ≤ C * hatGaussian c n x) ∧
      (∀ k l : ℕ, ∀ y : Site, ∑' x, hatGaussian c k x * hatGaussian c l (y - x) ≤
        C * hatGaussian c (k + l) y) ∧
      (∀ k l : ℕ, 0 < k → k < l → ∀ w : Site,
        ∑' y, hatGaussian c k y *
          (srwKernel (l - k) (w - y) - srwKernel l w) ^ 2 ≤
          C * k / (l * (l - k)) * hatGaussian c l w) := by
  obtain ⟨cK, hcK, hK⟩ := hatGaussian_kernel_convolution_bounds
  obtain ⟨CG, cG, hcG, hG⟩ := srwKernel_sameParity_sq_diff_le
  let c₀ : ℝ := min cK (cG / 2)
  have hc₀ : 0 < c₀ := by
    dsimp [c₀]
    exact lt_min hcK (by positivity)
  refine ⟨c₀, hc₀, fun c hc hcc₀ => ?_⟩
  obtain ⟨Ck, hCk, hkernel, hconv⟩ := hK c hc (le_trans hcc₀ (min_le_left _ _))
  have hCg : 0 ≤ max CG 0 := le_max_right _ _
  have hcgRate : c < cG := by
    have hcsmall : c ≤ cG / 2 := le_trans hcc₀ (min_le_right _ _)
    linarith
  have hgrad : ∀ n : ℕ, 1 ≤ n → ∀ z z' : Site,
      Even (z 0 + z 1 + z' 0 + z' 1) →
      (srwKernel n z - srwKernel n z') ^ 2 ≤
        (max CG 0) * ‖siteToPlane (z - z')‖ ^ 2 / (n : ℝ) ^ 3 *
          (Real.exp (-cG * ‖siteToPlane z‖ ^ 2 / n) +
            Real.exp (-cG * ‖siteToPlane z'‖ ^ 2 / n)) := by
    intro n hn z z' hpar
    have hbase := hG n hn z z' hpar
    calc
      _ ≤ CG * ‖siteToPlane (z - z')‖ ^ 2 / (n : ℝ) ^ 3 *
          (Real.exp (-cG * ‖siteToPlane z‖ ^ 2 / n) +
            Real.exp (-cG * ‖siteToPlane z'‖ ^ 2 / n)) := hbase
      _ ≤ (max CG 0) * ‖siteToPlane (z - z')‖ ^ 2 / (n : ℝ) ^ 3 *
          (Real.exp (-cG * ‖siteToPlane z‖ ^ 2 / n) +
            Real.exp (-cG * ‖siteToPlane z'‖ ^ 2 / n)) := by
        have hcoef : CG * ‖siteToPlane (z - z')‖ ^ 2 / (n : ℝ) ^ 3 ≤
            (max CG 0) * ‖siteToPlane (z - z')‖ ^ 2 / (n : ℝ) ^ 3 := by
          calc
            _ = (CG * ‖siteToPlane (z - z')‖ ^ 2) / (n : ℝ) ^ 3 := by ring
            _ ≤ ((max CG 0) * ‖siteToPlane (z - z')‖ ^ 2) / (n : ℝ) ^ 3 :=
              div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right (le_max_left CG 0) (sq_nonneg _))
                (by positivity)
            _ = _ := by ring
        exact mul_le_mul_of_nonneg_right hcoef (by positivity)
  let A0 : ℝ := 8 * (1 + Real.pi / c)
  let A2 : ℝ := 16 / c * (1 + 2 * Real.pi / c)
  let B2 : ℝ := 2 * A2 + 2 * A0 *
    (cG / c) ^ 2 / (2 * c * (cG - c) / (3 * cG))
  let M0 : ℝ := (1 + Real.sqrt (Real.pi / c)) ^ 2
  let Craw : ℝ := max CG 0 * Ck * (4 * A0 * (B2 + A2) + 2 * B2 * M0)
  let Cnear : ℝ :=
    6 * Ck ^ 2 * (4 * (Real.sqrt 2 + Real.sqrt (Real.pi / c)) ^ 2) +
      4 * Ck ^ 2 * (1 + Real.sqrt (Real.pi / c)) ^ 2
  let Cfar : ℝ := (9 / 4 : ℝ) * Craw
  let C : ℝ := max Ck (max Cnear Cfar)
  have hC : 0 < C := by dsimp [C]; positivity
  have hCkC : Ck ≤ C := le_max_left _ _
  have hCnearC : Cnear ≤ C :=
    le_trans (le_max_left Cnear Cfar) (le_max_right Ck (max Cnear Cfar))
  have hCfarC : Cfar ≤ C :=
    le_trans (le_max_right Cnear Cfar) (le_max_right Ck (max Cnear Cfar))
  refine ⟨C, ?_, ?_, ?_⟩
  · intro n x
    exact (hkernel n x).trans
      (mul_le_mul_of_nonneg_right hCkC (hatGaussian_nonneg n x))
  · intro k l y
    exact (hconv k l y).trans
      (mul_le_mul_of_nonneg_right hCkC (hatGaussian_nonneg (k + l) y))
  · intro k l hk hkl w
    let n : ℕ := l - k
    have hn : 1 ≤ n := by dsimp [n]; omega
    have hlpos : 0 < l := by omega
    have hlR : 0 < (l : ℝ) := by exact_mod_cast hlpos
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hknl : k + n = l := by dsimp [n]; omega
    have hnCast : (n : ℝ) = (l : ℝ) - k := by
      change ((l - k : ℕ) : ℝ) = (l : ℝ) - (k : ℝ)
      exact Nat.cast_sub (Nat.le_of_lt hkl)
    have hsubCast : ((l - k : ℕ) : ℝ) = (l : ℝ) - (k : ℝ) :=
      Nat.cast_sub (Nat.le_of_lt hkl)
    have hbaseFactor : 0 ≤ (k : ℝ) / ((l : ℝ) * (n : ℝ)) *
        hatGaussian c l w :=
      mul_nonneg (div_nonneg (by positivity) (mul_nonneg hlR.le hnR.le))
        (hatGaussian_nonneg (c := c) l w)
    by_cases hnear : l ≤ 3 * k
    · have hnearBound := hatGaussian_sq_diff_near hc hCk hkernel
        (by omega) hkl hnear w
      calc
        _ ≤ Cnear * (k : ℝ) / ((l : ℝ) * (n : ℝ)) * hatGaussian c l w := by
          simpa [Cnear, n, Nat.cast_sub (Nat.le_of_lt hkl), mul_assoc] using hnearBound
        _ ≤ C * (k : ℝ) / ((l : ℝ) * (n : ℝ)) * hatGaussian c l w := by
          have hmul := mul_le_mul_of_nonneg_right hCnearC hbaseFactor
          calc
            _ = Cnear * ((k : ℝ) / ((l : ℝ) * (n : ℝ)) * hatGaussian c l w) := by ring
            _ ≤ _ := hmul
            _ = _ := by ring
        _ = C * (k : ℝ) / ((l : ℝ) * ((l - k : ℕ) : ℝ)) *
            hatGaussian c l w := by simp [n]
        _ = C * (k : ℝ) / ((l : ℝ) * ((l : ℝ) - k)) *
            hatGaussian c l w := by rw [hsubCast]
    · have hfar : 3 * k < l := by omega
      have hkn : 2 * k ≤ n := by dsimp [n]; omega
      by_cases hpar : Even ((l : ℤ) + w 0 + w 1)
      · have hraw := hatGaussian_sq_diff_far_raw hc hcgRate hCk.le hCg
          hkernel hgrad (by omega) hn hkn w
        have hparityHat : hatGaussian c l w =
            (l : ℝ)⁻¹ * Real.exp (-c * ‖siteToPlane w‖ ^ 2 / l) := by
          simp [hatGaussian, Nat.ne_of_gt hlpos, hpar]
        have hratioSquare : (l : ℝ) ^ 2 ≤ (9 / 4 : ℝ) * (n : ℝ) ^ 2 := by
          have htwol : 2 * (l : ℝ) ≤ 3 * (n : ℝ) := by
            have hthree : 3 * (k : ℝ) < (l : ℝ) := by exact_mod_cast hfar
            rw [hnCast]
            linarith
          have hlNonneg : 0 ≤ (l : ℝ) := by positivity
          have hnNonneg : 0 ≤ (n : ℝ) := by positivity
          have hlin : (l : ℝ) ≤ (3 / 2 : ℝ) * n := by linarith
          have hsquare := (sq_le_sq₀ hlNonneg (by positivity)).2 hlin
          nlinarith [hsquare]
        have hratio : (1 : ℝ) / (n : ℝ) ^ 3 ≤
            (9 / 4 : ℝ) / ((l : ℝ) ^ 2 * n) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          calc
            _ = (l : ℝ) ^ 2 * n := by ring
            _ ≤ (9 / 4 : ℝ) * (n : ℝ) ^ 2 * n :=
              mul_le_mul_of_nonneg_right hratioSquare hnR.le
            _ = (9 / 4 : ℝ) * (n : ℝ) ^ 3 := by ring
        have hE : 0 ≤ Real.exp (-c * ‖siteToPlane w‖ ^ 2 / (k + n)) :=
          Real.exp_nonneg _
        have hscale : Craw * (k : ℝ) / (n : ℝ) ^ 3 *
            Real.exp (-c * ‖siteToPlane w‖ ^ 2 / (k + n)) ≤
          Cfar * (k : ℝ) / ((l : ℝ) * (n : ℝ)) * hatGaussian c l w := by
          have hknlR : (k : ℝ) + (n : ℝ) = (l : ℝ) := by exact_mod_cast hknl
          rw [hparityHat]
          have hCraw : 0 ≤ Craw := by
            dsimp [Craw, A0, A2, B2, M0]
            positivity
          have hfactor : 0 ≤ Craw * (k : ℝ) *
              Real.exp (-c * ‖siteToPlane w‖ ^ 2 / (k + n)) :=
            mul_nonneg (mul_nonneg hCraw (by positivity)) hE
          calc
            _ = (Craw * (k : ℝ) *
                Real.exp (-c * ‖siteToPlane w‖ ^ 2 / (k + n))) *
                  (1 / (n : ℝ) ^ 3) := by ring
            _ ≤ (Craw * (k : ℝ) *
                Real.exp (-c * ‖siteToPlane w‖ ^ 2 / (k + n))) *
                  ((9 / 4 : ℝ) / ((l : ℝ) ^ 2 * n)) :=
                    mul_le_mul_of_nonneg_left hratio hfactor
            _ = Cfar * (k : ℝ) / ((l : ℝ) * (n : ℝ)) *
                ((l : ℝ)⁻¹ * Real.exp
                  (-c * ‖siteToPlane w‖ ^ 2 / (l : ℝ))) := by
                    dsimp [Cfar]
                    field_simp [ne_of_gt hlR, ne_of_gt hnR]
                    rw [hknlR]
        calc
          _ ≤ Craw * (k : ℝ) / (n : ℝ) ^ 3 *
              Real.exp (-c * ‖siteToPlane w‖ ^ 2 / (k + n)) := by
                have hknlNat : k + (l - k) = l := Nat.add_sub_of_le (Nat.le_of_lt hkl)
                simpa [Craw, A0, A2, B2, M0, n, hknlNat] using hraw
          _ ≤ Cfar * (k : ℝ) / ((l : ℝ) * (n : ℝ)) * hatGaussian c l w := hscale
          _ ≤ C * (k : ℝ) / ((l : ℝ) * (n : ℝ)) * hatGaussian c l w := by
            have hmul := mul_le_mul_of_nonneg_right hCfarC hbaseFactor
            calc
              _ = Cfar * ((k : ℝ) / ((l : ℝ) * (n : ℝ)) *
                  hatGaussian c l w) := by ring
              _ ≤ _ := hmul
              _ = _ := by ring
          _ = C * (k : ℝ) / ((l : ℝ) * ((l - k : ℕ) : ℝ)) *
              hatGaussian c l w := by simp [n]
          _ = C * (k : ℝ) / ((l : ℝ) * ((l : ℝ) - k)) *
              hatGaussian c l w := by rw [hsubCast]
      · have hsumZero : ∑' y : Site, hatGaussian c k y *
            (srwKernel n (w - y) - srwKernel l w) ^ 2 = 0 := by
          have hterm (y : Site) : hatGaussian c k y *
              (srwKernel n (w - y) - srwKernel l w) ^ 2 = 0 := by
            by_cases hy0 : hatGaussian c k y = 0
            · simp [hy0]
            · have hypar := even_of_hatGaussian_ne_zero (by omega) hy0
              have hnpar : ¬ Even ((n : ℤ) + (w - y) 0 + (w - y) 1) := by
                intro hny
                apply hpar
                apply Int.even_iff.mpr
                have hkpar := Int.even_iff.mp hypar
                have hnpar' := Int.even_iff.mp hny
                have hknlZ : (l : ℤ) = (k : ℤ) + (n : ℤ) := by exact_mod_cast hknl.symm
                simp only [Pi.sub_apply] at hnpar'
                omega
              have hqn : srwKernel n (w - y) = 0 :=
                srwKernel_eq_zero_of_not_hatGaussianParity hnpar
              have hql : srwKernel l w = 0 :=
                srwKernel_eq_zero_of_not_hatGaussianParity hpar
              simp [hqn, hql]
          calc
            _ = ∑' y : Site, (0 : ℝ) := tsum_congr (fun y => hterm y)
            _ = 0 := tsum_zero
        rw [hsumZero]
        have hsubPos : 0 < ((l - k : ℕ) : ℝ) := by
          exact_mod_cast (Nat.sub_pos_of_lt hkl)
        have hden : 0 < (l : ℝ) * ((l : ℝ) - (k : ℝ)) := by
          rw [← hsubCast]
          exact mul_pos hlR hsubPos
        have hcoef : 0 ≤ C * (k : ℝ) := mul_nonneg (le_of_lt hC) (by positivity)
        exact mul_nonneg (div_nonneg hcoef hden.le)
          (hatGaussian_nonneg (c := c) l w)


end Critical2DKPZ.Collision

end
