/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.StringSumGaussian
import Critical2DKPZ.SHF.Moments.PairBlockLocalLimit
import Critical2DKPZ.Polymer.SummableCovariance
import Mathlib.Tactic

/-! # Gaussian propagation across a discrepancy and a renewal block -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.Blocks

open MeasureTheory
open scoped BigOperators


theorem srwKernel_difference_sq_le_one (n m : ℕ) (x y : Site) :
    (srwKernel n x - srwKernel m y) ^ 2 ≤ 1 := by
  have hx0 := Critical2DKPZ.srwKernel_nonneg n x
  have hy0 := Critical2DKPZ.srwKernel_nonneg m y
  have hx1 := Polymer.srwKernel_le_one n x
  have hy1 := Polymer.srwKernel_le_one m y
  have hlow : -1 ≤ srwKernel n x - srwKernel m y := by
    linarith only [hx0, hy1]
  have hhigh : srwKernel n x - srwKernel m y ≤ 1 := by
    linarith only [hx1, hy0]
  rw [sq_le_one_iff_abs_le_one]
  exact abs_le.mpr ⟨hlow, hhigh⟩

/-- Spatial renewal profiles are nonnegative for nonnegative coupling. -/
theorem spatialRenewal_nonneg {σ2 : ℝ} (hσ : 0 ≤ σ2) :
    ∀ n x, 0 ≤ Collision.spatialRenewal σ2 n x := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          intro x
          simp only [Collision.spatialRenewal_zero]
          split_ifs <;> norm_num
      | succ n =>
          intro x
          rw [Collision.spatialRenewal_succ]
          apply Finset.sum_nonneg
          intro m hm
          apply tsum_nonneg
          intro z
          exact mul_nonneg (mul_nonneg (ih m.val (by omega) z) hσ) (sq_nonneg _)

/-- The spatial renewal kernel vanishes outside the walk endpoint set. -/
theorem spatialRenewal_eq_zero_of_not_mem_endpoints {σ2 : ℝ} {n : ℕ} {x : Site}
    (hx : x ∉ Polymer.endpoints 0 n) : Collision.spatialRenewal σ2 n x = 0 :=
  SHF.Moments.spatialRenewal_eq_zero_of_not_mem_endpoints σ2 n x hx


/-- A reflected translate of a spatial renewal profile also has finite support. -/
theorem summable_spatialRenewal_sub_left (σ2 : ℝ) (n : ℕ) (z : Site) :
    Summable (fun x => Collision.spatialRenewal σ2 n (z - x)) := by
  apply summable_of_ne_finset_zero
    (s := (Polymer.endpoints 0 n).image (fun y => z - y))
  intro x hx
  have hx' : z - x ∉ Polymer.endpoints 0 n := by
    intro hmem
    apply hx
    apply Finset.mem_image.mpr
    exact ⟨z - x, hmem, by abel⟩
  exact spatialRenewal_eq_zero_of_not_mem_endpoints hx'

/-- The Gaussian-weighted squared kernel difference is bounded by a Gaussian envelope times the variance factor. -/
theorem tsum_weighted_difference_sq_le {c C K : ℝ} (hc : 0 < c)
    (hK : 0 ≤ K) {k a : ℕ} (hk : 1 ≤ k) (hka : k < a)
    (q : ℕ → Site → ℝ)
    (hqdiff : ∀ n m x y, (q n x - q m y) ^ 2 ≤ 1)
    (hvariance : ∀ k a : ℕ, 0 < k → k < a → ∀ x : Site,
      ∑' y, Collision.hatGaussian c k y *
        (q (a - k) (x - y) - q a x) ^ 2 ≤
          C * k / (a * (a - k)) * Collision.hatGaussian c a x)
    (f : Site → ℝ) (hf0 : ∀ y, 0 ≤ f y)
    (hf : ∀ y, f y ≤ K * Collision.hatGaussian c k y)
    (hfs : Summable f) (x : Site) :
    ∑' y, f y * (q (a - k) (x - y) - q a x) ^ 2 ≤
      K * C * k / (a * (a - k)) * Collision.hatGaussian c a x := by
  let D : Site → ℝ := fun y =>
    (q (a - k) (x - y) - q a x) ^ 2
  have hD0 (y : Site) : 0 ≤ D y := sq_nonneg _
  have hD1 (y : Site) : D y ≤ 1 := hqdiff (a - k) a (x - y) x
  have hsumfD : Summable (fun y => f y * D y) := by
    apply hfs.of_nonneg_of_le
    · intro y
      exact mul_nonneg (hf0 y) (hD0 y)
    · intro y
      calc
        f y * D y ≤ f y * 1 := mul_le_mul_of_nonneg_left (hD1 y) (hf0 y)
        _ = f y := mul_one _
  have hsumHatD : Summable (fun y => Collision.hatGaussian c k y * D y) := by
    apply (Collision.hatGaussian_summable hc hk).of_nonneg_of_le
    · intro y
      exact mul_nonneg (Collision.hatGaussian_nonneg (c := c) k y) (hD0 y)
    · intro y
      calc
        Collision.hatGaussian c k y * D y ≤ Collision.hatGaussian c k y * 1 :=
          mul_le_mul_of_nonneg_left (hD1 y) (Collision.hatGaussian_nonneg (c := c) k y)
        _ = Collision.hatGaussian c k y := mul_one _
  have hpoint (y : Site) : f y * D y ≤ (K * Collision.hatGaussian c k y) * D y :=
    mul_le_mul_of_nonneg_right (hf y) (hD0 y)
  have hsumMajor' : Summable (fun y => K *
      (Collision.hatGaussian c k y * D y)) := by
    exact hsumHatD.mul_left K
  have hpoint' (y : Site) : f y * D y ≤
      K * (Collision.hatGaussian c k y * D y) := by
    calc
      _ ≤ (K * Collision.hatGaussian c k y) * D y := hpoint y
      _ = K * (Collision.hatGaussian c k y * D y) := by ring
  have hvar := hvariance k a (by omega) hka x
  have hvar' : ∑' y, Collision.hatGaussian c k y * D y ≤
      C * k / (a * (a - k)) * Collision.hatGaussian c a x := by
    simpa only [D] using hvar
  calc
    _ ≤ ∑' y, K * (Collision.hatGaussian c k y * D y) :=
      hsumfD.tsum_le_tsum hpoint' hsumMajor'
    _ = K * ∑' y, Collision.hatGaussian c k y * D y := by
      exact hsumHatD.tsum_mul_left K
    _ ≤ K * (C * k / (a * (a - k)) * Collision.hatGaussian c a x) :=
      mul_le_mul_of_nonneg_left hvar' hK
    _ = K * C * k / (a * (a - k)) * Collision.hatGaussian c a x := by ring

/-- Convolution with a spatial renewal kernel propagates a Gaussian upper bound, retaining the scalar renewal mass. -/
theorem tsum_profile_spatialRenewal_le {c Cwalk Crenewal σ2 K : ℝ}
    (hc : 0 < c) (hCrenewal : 1 ≤ Crenewal)
    (hconvolution : ∀ k d : ℕ, ∀ z : Site,
      ∑' x, Collision.hatGaussian c k x * Collision.hatGaussian c d (z - x) ≤
        Cwalk * Collision.hatGaussian c (k + d) z)
    (hrenewal : ∀ σ : ℝ, 0 ≤ σ → ∀ n : ℕ, 1 ≤ n → ∀ x : Site,
      Collision.spatialRenewal σ n x ≤
        Crenewal * (∑' w, Collision.spatialRenewal σ n w) * Collision.hatGaussian c n x)
    (hU : ∀ n x, 0 ≤ Collision.spatialRenewal σ2 n x)
    (hσ : 0 ≤ σ2) (hK : 0 ≤ K) {k : ℕ} (hk : 1 ≤ k)
    (f : Site → ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (hf : ∀ x, f x ≤ K * Collision.hatGaussian c k x)
    (d : ℕ) (z : Site) :
    ∑' x, f x * (σ2 * Collision.spatialRenewal σ2 d (z - x)) ≤
      K * Crenewal * Cwalk *
        (σ2 * (∑' w, Collision.spatialRenewal σ2 d w)) *
          Collision.hatGaussian c (k + d) z := by
  have hmassEq := Critical2DKPZ.SHF.Moments.tsum_spatialRenewal_eq_renewalMass σ2 d
  have hweights : ∀ r, 0 ≤ σ2 * Critical2DKPZ.Renewal.returnWeight r := by
    intro r
    exact mul_nonneg hσ (Critical2DKPZ.srwKernel_nonneg _ _)
  have hmass0 : 0 ≤ ∑' w, Collision.spatialRenewal σ2 d w := by
    rw [hmassEq]
    exact Critical2DKPZ.Renewal.renewalMass_nonneg hweights d
  have hcoeff : 0 ≤ K * Crenewal * (σ2 * (∑' w, Collision.spatialRenewal σ2 d w)) := by
    positivity
  have hmassBound (x : Site) :
      σ2 * Collision.spatialRenewal σ2 d (z - x) ≤
        Crenewal * (σ2 * (∑' w, Collision.spatialRenewal σ2 d w)) *
          Collision.hatGaussian c d (z - x) := by
    by_cases hd : d = 0
    · subst d
      have hzero := spatialRenewal_le_hatGaussian_all hCrenewal hrenewal σ2 hσ 0 (z - x)
      calc
        _ ≤ σ2 * (Crenewal * (∑' w, Collision.spatialRenewal σ2 0 w) *
            Collision.hatGaussian c 0 (z - x)) := mul_le_mul_of_nonneg_left hzero hσ
        _ = _ := by ring
    · have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
      have hzero := hrenewal σ2 hσ d hd1 (z - x)
      calc
        _ ≤ σ2 * (Crenewal * (∑' w, Collision.spatialRenewal σ2 d w) *
            Collision.hatGaussian c d (z - x)) := mul_le_mul_of_nonneg_left hzero hσ
        _ = _ := by ring
  have hproductSummable :
      Summable (fun x => Collision.hatGaussian c k x * Collision.hatGaussian c d (z - x)) := by
    apply (Collision.hatGaussian_summable hc hk).of_nonneg_of_le
    · intro x
      exact mul_nonneg (Collision.hatGaussian_nonneg (c := c) k x)
        (Collision.hatGaussian_nonneg (c := c) d (z - x))
    · intro x
      calc
        Collision.hatGaussian c k x * Collision.hatGaussian c d (z - x) ≤
            Collision.hatGaussian c k x * 1 :=
          mul_le_mul_of_nonneg_left (hatGaussian_le_one hc d (z - x))
            (Collision.hatGaussian_nonneg (c := c) k x)
        _ = Collision.hatGaussian c k x := mul_one _
  have hpoint0 (x : Site) :
      0 ≤ f x * (σ2 * Collision.spatialRenewal σ2 d (z - x)) :=
    mul_nonneg (hf0 x) (mul_nonneg hσ (hU d (z - x)))
  have hpoint1 (x : Site) :
      f x * (σ2 * Collision.spatialRenewal σ2 d (z - x)) ≤
        (K * Crenewal * (σ2 * (∑' w, Collision.spatialRenewal σ2 d w))) *
          (Collision.hatGaussian c k x * Collision.hatGaussian c d (z - x)) := by
    calc
      _ ≤ (K * Collision.hatGaussian c k x) *
          (σ2 * Collision.spatialRenewal σ2 d (z - x)) :=
            mul_le_mul_of_nonneg_right (hf x)
              (mul_nonneg hσ (hU d (z - x)))
      _ ≤ (K * Collision.hatGaussian c k x) *
          (Crenewal * (σ2 * (∑' w, Collision.spatialRenewal σ2 d w)) *
            Collision.hatGaussian c d (z - x)) :=
              mul_le_mul_of_nonneg_left (hmassBound x)
                (mul_nonneg hK (Collision.hatGaussian_nonneg (c := c) k x))
      _ = _ := by ring
  let M : ℝ := K * Crenewal *
    (σ2 * (∑' w, Collision.spatialRenewal σ2 d w))
  have hsumMajor : Summable (fun x => M *
      (Collision.hatGaussian c k x * Collision.hatGaussian c d (z - x))) := by
    exact hproductSummable.mul_left M
  have hsumLeft : Summable (fun x =>
      f x * (σ2 * Collision.spatialRenewal σ2 d (z - x))) :=
    hsumMajor.of_nonneg_of_le hpoint0 (by simpa [M] using hpoint1)
  calc
    _ ≤ ∑' x, (K * Crenewal * (σ2 *
          (∑' w, Collision.spatialRenewal σ2 d w))) *
          (Collision.hatGaussian c k x * Collision.hatGaussian c d (z - x)) :=
            hsumLeft.tsum_le_tsum (by simpa [M] using hpoint1) hsumMajor
    _ = (K * Crenewal * (σ2 *
          (∑' w, Collision.spatialRenewal σ2 d w))) *
          ∑' x, Collision.hatGaussian c k x * Collision.hatGaussian c d (z - x) := by
            rw [hproductSummable.tsum_mul_left]
    _ ≤ (K * Crenewal * (σ2 *
          (∑' w, Collision.spatialRenewal σ2 d w))) *
          (Cwalk * Collision.hatGaussian c (k + d) z) :=
            mul_le_mul_of_nonneg_left (hconvolution k d z) hcoeff
    _ = _ := by ring

/-- The first occupied block starts with the squared walk profile and then makes one renewal
excursion. -/
theorem tsum_srwKernel_sq_spatialRenewal_le {c Cwalk Crenewal σ2 : ℝ}
    (hc : 0 < c) (hCwalk : 1 ≤ Cwalk) (hCrenewal : 1 ≤ Crenewal)
    (hkernel : ∀ n x, srwKernel n x ≤ Cwalk * Collision.hatGaussian c n x)
    (hconvolution : ∀ k d : ℕ, ∀ z : Site,
      ∑' x, Collision.hatGaussian c k x * Collision.hatGaussian c d (z - x) ≤
        Cwalk * Collision.hatGaussian c (k + d) z)
    (hrenewal : ∀ σ : ℝ, 0 ≤ σ → ∀ n : ℕ, 1 ≤ n → ∀ x : Site,
      Collision.spatialRenewal σ n x ≤
        Crenewal * (∑' w, Collision.spatialRenewal σ n w) * Collision.hatGaussian c n x)
    (hσ : 0 ≤ σ2) {a : ℕ} (ha : 1 ≤ a) (d : ℕ) (z : Site) :
    ∑' x : Site, srwKernel a x ^ 2 *
        (σ2 * Collision.spatialRenewal σ2 d (z - x)) ≤
      (Cwalk ^ 2 * (a : ℝ)⁻¹) * Crenewal * Cwalk *
        (σ2 * (∑' w, Collision.spatialRenewal σ2 d w)) *
          Collision.hatGaussian c (a + d) z := by
  have hCwalk0 : 0 ≤ Cwalk := le_trans (by norm_num) hCwalk
  have hK : 0 ≤ Cwalk ^ 2 * (a : ℝ)⁻¹ := by positivity
  have hbound (x : Site) : srwKernel a x ^ 2 ≤
      (Cwalk ^ 2 * (a : ℝ)⁻¹) * Collision.hatGaussian c a x := by
    simpa only [mul_assoc] using
      srwKernel_sq_le_hatGaussian_inv hc hCwalk0 ha hkernel x
  exact tsum_profile_spatialRenewal_le hc hCrenewal hconvolution hrenewal
    (spatialRenewal_nonneg hσ) hσ hK (k := a) ha
    (fun x => srwKernel a x ^ 2) (fun _ => sq_nonneg _)
    hbound d z

/-- A transition propagates a Gaussian upper bound with the transition and renewal mass factors. -/
theorem tsum_transition_spatialRenewal_le {c Cwalk Crenewal σ2 K : ℝ}
    (hc : 0 < c) (hCwalk : 1 ≤ Cwalk) (hCrenewal : 1 ≤ Crenewal)
    (hconvolution : ∀ k d : ℕ, ∀ z : Site,
      ∑' x, Collision.hatGaussian c k x * Collision.hatGaussian c d (z - x) ≤
        Cwalk * Collision.hatGaussian c (k + d) z)
    (hrenewal : ∀ σ : ℝ, 0 ≤ σ → ∀ n : ℕ, 1 ≤ n → ∀ x : Site,
      Collision.spatialRenewal σ n x ≤
        Crenewal * (∑' w, Collision.spatialRenewal σ n w) * Collision.hatGaussian c n x)
    (hU : ∀ n x, 0 ≤ Collision.spatialRenewal σ2 n x)
    (hσ : 0 ≤ σ2) (hK : 0 ≤ K) {k a : ℕ} (hk : 1 ≤ k) (hka : k < a)
    (q : ℕ → Site → ℝ)
    (hqdiff : ∀ n m x y, (q n x - q m y) ^ 2 ≤ 1)
    (hvariance : ∀ k a : ℕ, 0 < k → k < a → ∀ x : Site,
      ∑' y, Collision.hatGaussian c k y *
        (q (a - k) (x - y) - q a x) ^ 2 ≤
          Cwalk * k / (a * (a - k)) * Collision.hatGaussian c a x)
    (f : Site → ℝ) (hf0 : ∀ y, 0 ≤ f y)
    (hf : ∀ y, f y ≤ K * Collision.hatGaussian c k y)
    (hfs : Summable f) (d : ℕ) (z : Site) :
    ∑' y, f y * ∑' x,
        (q (a - k) (x - y) - q a x) ^ 2 *
          (σ2 * Collision.spatialRenewal σ2 d (z - x)) ≤
      (K * Cwalk * k / (a * (a - k))) * Crenewal * Cwalk *
        (σ2 * (∑' w, Collision.spatialRenewal σ2 d w)) *
          Collision.hatGaussian c (a + d) z := by
  {
    let D : Site → Site → ℝ := fun y x =>
      (q (a - k) (x - y) - q a x) ^ 2
    let R : Site → ℝ := fun x => σ2 * Collision.spatialRenewal σ2 d (z - x)
    let P : Site × Site → ℝ := fun p => f p.1 * D p.1 p.2 * R p.2
    have hD0 (y x : Site) : 0 ≤ D y x := sq_nonneg _
    have hD1 (y x : Site) : D y x ≤ 1 := hqdiff (a - k) a (x - y) x
    have hR0 (x : Site) : 0 ≤ R x := mul_nonneg hσ (hU d (z - x))
    have hRs : Summable R := by
      simpa only [R] using
        (summable_spatialRenewal_sub_left σ2 d z).mul_left σ2
    have hMajor : Summable (fun p : Site × Site => f p.1 * R p.2) := by
      apply (summable_prod_of_nonneg (f := fun p : Site × Site => f p.1 * R p.2)
        (fun p => mul_nonneg (hf0 p.1) (hR0 p.2))).2
      constructor
      · intro y
        simpa only [R] using hRs.mul_left (f y)
      · have hrow (y : Site) :
            (∑' x, f y * R x) = f y * (∑' x, R x) := hRs.tsum_mul_left (f y)
        have houter : Summable (fun y => f y * (∑' x, R x)) := hfs.mul_right _
        exact houter.congr fun y => (hrow y).symm
    have hP0 (p : Site × Site) : 0 ≤ P p := by
      exact mul_nonneg (mul_nonneg (hf0 p.1) (hD0 p.1 p.2)) (hR0 p.2)
    have hPs : Summable P := by
      apply hMajor.of_nonneg_of_le hP0
      intro p
      dsimp [P]
      calc
        f p.1 * D p.1 p.2 * R p.2 ≤ f p.1 * 1 * R p.2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hD1 p.1 p.2) (hf0 p.1)) (hR0 p.2)
        _ = f p.1 * R p.2 := by ring
    have hPsSwap : Summable (fun p : Site × Site => P p.swap) := hPs.prod_symm
    have hFDs (x : Site) : Summable (fun y => f y * D y x) := by
      apply hfs.of_nonneg_of_le
      · intro y
        exact mul_nonneg (hf0 y) (hD0 y x)
      · intro y
        calc
          f y * D y x ≤ f y * 1 := mul_le_mul_of_nonneg_left (hD1 y x) (hf0 y)
          _ = f y := mul_one _
    let H : Site → ℝ := fun x => ∑' y, f y * D y x
    have hH0 (x : Site) : 0 ≤ H x := tsum_nonneg fun y =>
      mul_nonneg (hf0 y) (hD0 y x)
    have hTransition (x : Site) :
        H x ≤ K * Cwalk * k / (a * (a - k)) * Collision.hatGaussian c a x := by
      simpa only [H, D] using
        tsum_weighted_difference_sq_le hc hK hk hka q hqdiff
          hvariance f hf0 hf hfs x
    have haR : 0 < (a : ℝ) := by exact_mod_cast (lt_trans hk hka)
    have hkaR : (k : ℝ) < (a : ℝ) := by exact_mod_cast hka
    have hK' : 0 ≤ K * Cwalk * k / (a * (a - k)) := by positivity
    have hTsumSwap : (∑' p : Site × Site, P p) =
        ∑' p : Site × Site, P p.swap := by
      exact (Equiv.prodComm Site Site).tsum_eq P |>.symm
    have hTsumY : (∑' p : Site × Site, P p) =
        ∑' y, ∑' x, P (y, x) := hPs.tsum_prod
    have hTsumX : (∑' p : Site × Site, P p.swap) =
        ∑' x, ∑' y, P (y, x) := hPsSwap.tsum_prod
    have hReorder :
        (∑' y, f y * ∑' x, D y x * R x) = ∑' x, H x * R x := by
      calc
        _ = ∑' y, ∑' x, P (y, x) := by
          apply tsum_congr
          intro y
          dsimp [P]
          rw [← tsum_mul_left]
          apply tsum_congr
          intro x
          ring
        _ = ∑' p : Site × Site, P p := hTsumY.symm
        _ = ∑' p : Site × Site, P p.swap := hTsumSwap
        _ = ∑' x, ∑' y, P (y, x) := hTsumX
        _ = ∑' x, H x * R x := tsum_congr fun x =>
          (hFDs x).tsum_mul_right (R x)
    exact hReorder.symm ▸ (by
      simpa only [R, mul_assoc, mul_comm, mul_left_comm] using
        (tsum_profile_spatialRenewal_le hc hCrenewal hconvolution hrenewal
          (spatialRenewal_nonneg hσ) hσ hK' (k := a) (by omega)
          H hH0 (fun x => by simpa only [mul_assoc] using hTransition x) d z))
  }

end Critical2DKPZ.Blocks

end
