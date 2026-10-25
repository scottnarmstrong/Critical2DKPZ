/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Collision.SpatialRenewal
import Critical2DKPZ.MomentBounds.LatticeShells
import Critical2DKPZ.WalkTails.SameParityGradient
import Critical2DKPZ.Lattice.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-! # Gaussian summation estimates for the planar lattice -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.Collision

open MeasureTheory

/-- The scalar Gaussian weight is the exponential of minus the rate times the squared argument. -/
def gaussian1D (a x : ℝ) : ℝ := Real.exp (-a * x ^ 2)

private theorem gaussian1D_antitone {a : ℝ} (ha : 0 < a) :
    AntitoneOn (gaussian1D a) (Set.Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  dsimp [gaussian1D]
  apply Real.exp_le_exp.mpr
  have hx2 : x ^ 2 ≤ y ^ 2 := by
    have hmul := mul_nonneg (sub_nonneg.mpr hxy) (add_nonneg hx hy)
    nlinarith
  nlinarith [mul_le_mul_of_nonpos_left hx2 (neg_nonpos.mpr ha.le)]

/-- The one-dimensional Gaussian is summable over the integers. -/
theorem gaussian1D_int_summable {a : ℝ} (ha : 0 < a) :
    Summable (fun z : ℤ => gaussian1D a (z : ℝ)) := by
  have hI : IntegrableOn (gaussian1D a) (Set.Ioi (0 : ℝ)) := by
    exact (integrable_exp_neg_mul_sq ha).integrableOn
  have hnonneg : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ gaussian1D a t := by
    intro t ht
    exact (Real.exp_pos _).le
  have hNat : Summable (fun n : ℕ => gaussian1D a (n : ℝ)) :=
    (gaussian1D_antitone ha).summable_of_integrableOn_Ioi_zero hI hnonneg
  apply (summable_int_iff_summable_nat_and_neg).2
  refine ⟨?_, ?_⟩
  · simpa [gaussian1D] using hNat
  · simpa [gaussian1D, Int.cast_neg] using hNat

/-- The sum over the integers of the one-dimensional Gaussian is at most `1 + √(π / a)`. The series
is summable by `gaussian1D_int_summable`. -/
theorem intGaussian_tsum_le {a : ℝ} (ha : 0 < a) :
    ∑' z : ℤ, gaussian1D a (z : ℝ) ≤ 1 + Real.sqrt (Real.pi / a) := by
  have anti := gaussian1D_antitone ha
  have hI : IntegrableOn (gaussian1D a) (Set.Ioi (0 : ℝ)) := by
    exact (integrable_exp_neg_mul_sq ha).integrableOn
  have hnonneg : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ gaussian1D a t := by
    intro t ht
    exact (Real.exp_pos _).le
  have hInt := gaussian1D_int_summable ha
  have heven : Function.Even (fun z : ℤ => gaussian1D a (z : ℝ)) := by
    intro z
    simp [gaussian1D]
  have hPNat : (∑' n : ℕ+, gaussian1D a ((n : ℤ) : ℝ)) =
      ∑' n : ℕ, gaussian1D a ((n + 1 : ℕ) : ℝ) := by
    calc
      _ = ∑' n : ℕ+, gaussian1D a ((n : ℕ) : ℝ) := by
        apply tsum_congr
        intro n
        simp
      _ = _ := tsum_pnat_eq_tsum_succ (f := fun n : ℕ => gaussian1D a (n : ℝ))
  have htail :
      (∑' n : ℕ, gaussian1D a ((n + 1 : ℕ) : ℝ)) ≤
        ∫ x in Set.Ioi (0 : ℝ), gaussian1D a x := by
    simpa only [gaussian1D] using
      anti.tsum_add_one_le_integral hI hnonneg
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven hInt, hPNat]
  have hzero : gaussian1D a 0 = 1 := by simp [gaussian1D]
  simp only [Int.cast_zero, hzero, Nat.cast_ofNat, nsmul_eq_mul]
  have hIeq : ∫ x in Set.Ioi (0 : ℝ), gaussian1D a x =
      Real.sqrt (Real.pi / a) / 2 := by
    simpa only [gaussian1D] using integral_gaussian_Ioi a
  calc
    _ ≤ 1 + (2 : ℝ) * (∫ x in Set.Ioi (0 : ℝ), gaussian1D a x) := by
      have hmul := mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 2)
      change 1 + (2 : ℝ) * (∑' n : ℕ, gaussian1D a ((n + 1 : ℕ) : ℝ)) ≤
        1 + (2 : ℝ) * (∫ x in Set.Ioi (0 : ℝ), gaussian1D a x)
      simpa [add_comm] using add_le_add_right hmul 1
    _ = 1 + Real.sqrt (Real.pi / a) := by
      rw [hIeq]
      ring

/-- A shifted one-dimensional Gaussian is summable with a uniform sum bound. -/
theorem intGaussian_shifted_summable_and_tsum_le {a u : ℝ} (ha : 0 < a) :
    Summable (fun z : ℤ => Real.exp (-a * ((z : ℝ) - u) ^ 2)) ∧
      ∑' z : ℤ, Real.exp (-a * ((z : ℝ) - u) ^ 2) ≤
        2 * (1 + Real.sqrt (Real.pi / a)) := by
  let m : ℤ := ⌊u⌋
  let δ : ℝ := u - (m : ℝ)
  have hδeq : δ = Int.fract u := by
    dsimp [δ, m]
  have hδ0 : 0 ≤ δ := by rw [hδeq]; exact Int.fract_nonneg u
  have hδ1 : δ ≤ 1 := by rw [hδeq]; exact (Int.fract_lt_one u).le
  have hmδ : (m : ℝ) + δ = u := by
    dsimp [δ, m]
    exact Int.floor_add_fract u
  let f : ℤ → ℝ := fun z => gaussian1D a (z : ℝ)
  let g : ℤ → ℝ := fun z => Real.exp (-a * ((z : ℝ) - δ) ^ 2)
  let e : ℤ ≃ ℤ :=
    { toFun := fun z => m + z
      invFun := fun z => z - m
      left_inv := by intro z; change (m + z) - m = z; omega
      right_inv := by intro z; change m + (z - m) = z; omega }
  have hcomp : (fun z : ℤ => Real.exp (-a * ((e z : ℤ) - u) ^ 2)) = g := by
    funext z
    change Real.exp (-a * (((m + z : ℤ) : ℝ) - u) ^ 2) =
      Real.exp (-a * ((z : ℝ) - δ) ^ 2)
    congr 1
    have harg : (m : ℝ) + (z : ℝ) - u = (z : ℝ) - δ := by linarith [hmδ]
    rw [Int.cast_add, harg]
  have hReindex : (∑' z : ℤ, Real.exp (-a * ((z : ℝ) - u) ^ 2)) = ∑' z, g z := by
    calc
      _ = ∑' z : ℤ, Real.exp (-a * (((e z : ℤ) : ℝ) - u) ^ 2) :=
        (e.tsum_eq (fun z : ℤ => Real.exp (-a * ((z : ℝ) - u) ^ 2))).symm
      _ = _ := tsum_congr (fun z => congrFun hcomp z)
  have hf : Summable f := by
    simpa [f] using gaussian1D_int_summable ha
  have hfshift : Summable (fun z : ℤ => f (z - 1)) := by
    let e : ℤ ≃ ℤ :=
      { toFun := fun z => -1 + z
        invFun := fun z => z + 1
        left_inv := by intro z; change (-1 + z) + 1 = z; omega
        right_inv := by intro z; change -1 + (z + 1) = z; omega }
    have he : (fun z : ℤ => f (z - 1)) = f ∘ e := by
      funext z
      change f (z - 1) = f (-1 + z)
      congr 1
      omega
    rw [he]
    exact e.summable_iff.mpr hf
  have hmajor : Summable (fun z : ℤ => f z + f (z - 1)) := hf.add hfshift
  have hpoint (z : ℤ) : 0 ≤ g z ∧ g z ≤ f z + f (z - 1) := by
    constructor
    · exact Real.exp_nonneg _
    · by_cases hz : z ≤ 0
      · have hzR : (z : ℝ) ≤ 0 := by exact_mod_cast hz
        have hsquare : (z : ℝ) ^ 2 ≤ ((z : ℝ) - δ) ^ 2 := by
          have hprod := mul_nonneg hδ0 (sub_nonneg.mpr (by linarith : 2 * (z : ℝ) ≤ δ))
          nlinarith
        have hexp : Real.exp (-a * ((z : ℝ) - δ) ^ 2) ≤ f z := by
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonpos_left hsquare (by linarith : -a ≤ 0)
        exact hexp.trans (le_add_of_nonneg_right (Real.exp_nonneg _))
      · have hz1 : 1 ≤ z := by omega
        have hzR : 1 ≤ (z : ℝ) := by exact_mod_cast hz1
        have hsquare : ((z : ℝ) - 1) ^ 2 ≤ ((z : ℝ) - δ) ^ 2 := by
          have hprod := mul_nonneg (sub_nonneg.mpr hδ1) (sub_nonneg.mpr (by linarith : 1 + δ ≤ 2 * (z : ℝ)))
          nlinarith
        have hexp : Real.exp (-a * ((z : ℝ) - δ) ^ 2) ≤ f (z - 1) := by
          apply Real.exp_le_exp.mpr
          rw [Int.cast_sub, Int.cast_one]
          exact mul_le_mul_of_nonpos_left hsquare (by linarith : -a ≤ 0)
        exact hexp.trans (le_add_of_nonneg_left (Real.exp_nonneg _))
  have hg : Summable g := hmajor.of_nonneg_of_le
    (fun z => (hpoint z).1) (fun z => (hpoint z).2)
  have hqSummable : Summable (fun z : ℤ => Real.exp (-a * ((z : ℝ) - u) ^ 2)) := by
    have hcompSummable : Summable (fun z : ℤ => Real.exp (-a * ((e z : ℤ) - u) ^ 2)) := by
      rw [hcomp]
      exact hg
    exact e.summable_iff.mp hcompSummable
  have hshift : (∑' z : ℤ, f (z - 1)) = ∑' z, f z := by
    let e : ℤ ≃ ℤ :=
      { toFun := fun z => -1 + z
        invFun := fun z => z + 1
        left_inv := by intro z; change (-1 + z) + 1 = z; omega
        right_inv := by intro z; change -1 + (z + 1) = z; omega }
    calc
      _ = ∑' z : ℤ, f (e z) := by
        apply tsum_congr
        intro z
        change f (z - 1) = f (-1 + z)
        congr 1
        omega
      _ = _ := e.tsum_eq f
  have hmajorSum : (∑' z : ℤ, (f z + f (z - 1))) = 2 * (∑' z : ℤ, f z) := by
    rw [hf.tsum_add hfshift, hshift]
    ring
  rw [hReindex]
  refine ⟨hqSummable, ?_⟩
  · calc
      _ ≤ ∑' z : ℤ, (f z + f (z - 1)) :=
        hg.tsum_le_tsum (fun z => (hpoint z).2) hmajor
      _ = 2 * (∑' z : ℤ, f z) := hmajorSum
      _ ≤ 2 * (1 + Real.sqrt (Real.pi / a)) := by
        have h := intGaussian_tsum_le ha
        have hnonneg : 0 ≤ (2 : ℝ) := by norm_num
        simpa [f, gaussian1D] using mul_le_mul_of_nonneg_left h hnonneg


/-- Positive rate lattice Gaussian weights are summable with a bound uniform in their planar center. -/
theorem shiftedSiteGaussian_control {a : ℝ} (ha : 0 < a) (v : Plane) :
    Summable (fun x : Site => Real.exp (-a * ‖siteToPlane x - v‖ ^ 2)) ∧
      ∑' x : Site, Real.exp (-a * ‖siteToPlane x - v‖ ^ 2) ≤
        4 * (1 + Real.sqrt (Real.pi / a)) ^ 2 := by
  let f : ℤ → ℝ := fun z => Real.exp (-a * ((z : ℝ) - v 0) ^ 2)
  let g : ℤ → ℝ := fun z => Real.exp (-a * ((z : ℝ) - v 1) ^ 2)
  obtain ⟨hf, hfb⟩ := intGaussian_shifted_summable_and_tsum_le (a := a) (u := v 0) ha
  obtain ⟨hg, hgb⟩ := intGaussian_shifted_summable_and_tsum_le (a := a) (u := v 1) ha
  have hf' : Summable f := by simpa [f] using hf
  have hg' : Summable g := by simpa [g] using hg
  have hprod : Summable (fun p : ℤ × ℤ => f p.1 * g p.2) := by
    apply (summable_prod_of_nonneg
      (fun p : ℤ × ℤ => mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))).2
    constructor
    · intro x
      exact hg'.mul_left (f x)
    · change Summable (fun x : ℤ => ∑' y : ℤ, f x * g y)
      have heq : (fun x : ℤ => ∑' y : ℤ, f x * g y) =
          fun x => f x * (∑' y : ℤ, g y) := by
        funext x
        exact hg'.tsum_mul_left (f x)
      rw [heq]
      exact hf'.mul_right _
  have hpair :
      (∑' p : ℤ × ℤ, f p.1 * g p.2) = (∑' z : ℤ, f z) * (∑' z : ℤ, g z) := by
    rw [← hf'.tsum_mul_tsum hg' hprod]
  let e := Critical2DKPZ.MomentBounds.siteEquivProd.symm
  have hsitecomp :
      (fun p : ℤ × ℤ => Real.exp (-a * ‖siteToPlane (e p) - v‖ ^ 2)) =
        fun p => f p.1 * g p.2 := by
    funext p
    have h0 : (e p) 0 = p.1 := by
      change (![p.1, p.2] : Site) 0 = p.1
      rfl
    have h1 : (e p) 1 = p.2 := by
      change (![p.1, p.2] : Site) 1 = p.2
      rfl
    have hnorm : ‖siteToPlane (e p) - v‖ ^ 2 =
        ((p.1 : ℝ) - v 0) ^ 2 + ((p.2 : ℝ) - v 1) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      simp [siteToPlane, h0, h1]
    rw [hnorm]
    rw [show -a * (((p.1 : ℝ) - v 0) ^ 2 + ((p.2 : ℝ) - v 1) ^ 2) =
      (-a * ((p.1 : ℝ) - v 0) ^ 2) + (-a * ((p.2 : ℝ) - v 1) ^ 2) by ring,
      Real.exp_add]
  have hsite :
      (∑' x : Site, Real.exp (-a * ‖siteToPlane x - v‖ ^ 2)) =
        ∑' p : ℤ × ℤ, f p.1 * g p.2 := by
    calc
      _ = ∑' p : ℤ × ℤ, Real.exp (-a * ‖siteToPlane (e p) - v‖ ^ 2) :=
        e.tsum_eq (fun x : Site => Real.exp (-a * ‖siteToPlane x - v‖ ^ 2)) |>.symm
      _ = _ := by
        apply tsum_congr
        intro p
        exact congrFun hsitecomp p
  have hsiteSummable : Summable (fun x : Site => Real.exp (-a * ‖siteToPlane x - v‖ ^ 2)) := by
    have hcompSummable : Summable
        (fun p : ℤ × ℤ => Real.exp (-a * ‖siteToPlane (e p) - v‖ ^ 2)) := by
      rw [hsitecomp]
      exact hprod
    exact e.summable_iff.mp hcompSummable
  have hfb' : 0 ≤ 2 * (1 + Real.sqrt (Real.pi / a)) := by positivity
  have hgb' : 0 ≤ 2 * (1 + Real.sqrt (Real.pi / a)) := by positivity
  have hsumf : 0 ≤ ∑' z : ℤ, f z := tsum_nonneg (fun z => Real.exp_nonneg _)
  have hsumg : 0 ≤ ∑' z : ℤ, g z := tsum_nonneg (fun z => Real.exp_nonneg _)
  have hprodBound :
      (∑' z : ℤ, f z) * (∑' z : ℤ, g z) ≤
        (2 * (1 + Real.sqrt (Real.pi / a))) ^ 2 := by
    calc
      (∑' z : ℤ, f z) * (∑' z : ℤ, g z) ≤
          (2 * (1 + Real.sqrt (Real.pi / a))) * (∑' z : ℤ, g z) :=
        mul_le_mul_of_nonneg_right hfb hsumg
      _ ≤ (2 * (1 + Real.sqrt (Real.pi / a))) ^ 2 := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left hgb hfb'
  constructor
  · exact hsiteSummable
  · rw [hsite, hpair]
    nlinarith [hprodBound]

private theorem gaussian_norm_sq_absorb {a r : ℝ} (ha : 0 < a) :
    r ^ 2 * Real.exp (-a * r ^ 2) ≤
      (2 / a) * Real.exp (-(a / 2) * r ^ 2) := by
  let u : ℝ := (a / 2) * r ^ 2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have huExp : u ≤ Real.exp u := by
    have h := Real.add_one_le_exp u
    linarith
  have hprod : u * Real.exp (-u) ≤ 1 := by
    calc
      u * Real.exp (-u) ≤ Real.exp u * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right huExp (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hprod2 : u * Real.exp (-2 * u) ≤ Real.exp (-u) := by
    have hexp : Real.exp (-2 * u) = Real.exp (-u) * Real.exp (-u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      u * Real.exp (-2 * u) = (u * Real.exp (-u)) * Real.exp (-u) := by
        rw [hexp]
        ring
      _ ≤ 1 * Real.exp (-u) := mul_le_mul_of_nonneg_right hprod (Real.exp_nonneg _)
      _ = _ := by ring
  have hcoeff : (2 / a) * u = r ^ 2 := by
    dsimp [u]
    field_simp [ne_of_gt ha]
  have hexp : Real.exp (-a * r ^ 2) = Real.exp (-2 * u) := by
    congr 1
    dsimp [u]
    ring
  calc
    _ = (2 / a) * (u * Real.exp (-2 * u)) := by
      rw [hexp, ← hcoeff]
      ring
    _ ≤ (2 / a) * Real.exp (-u) :=
      mul_le_mul_of_nonneg_left hprod2 (by positivity)
    _ = _ := by dsimp [u]; congr 2; ring

/-- A shifted lattice Gaussian has a uniformly bounded centered second moment. -/
theorem shiftedSiteGaussian_secondMoment_control {a : ℝ} (ha : 0 < a) (v : Plane) :
    Summable (fun x : Site => ‖siteToPlane x - v‖ ^ 2 *
        Real.exp (-a * ‖siteToPlane x - v‖ ^ 2)) ∧
      ∑' x : Site, ‖siteToPlane x - v‖ ^ 2 *
        Real.exp (-a * ‖siteToPlane x - v‖ ^ 2) ≤
      8 / a * (1 + Real.sqrt (2 * Real.pi / a)) ^ 2 := by
  let f : Site → ℝ := fun x => ‖siteToPlane x - v‖ ^ 2 *
    Real.exp (-a * ‖siteToPlane x - v‖ ^ 2)
  let g : Site → ℝ := fun x => Real.exp (-(a / 2) * ‖siteToPlane x - v‖ ^ 2)
  have hshift := shiftedSiteGaussian_control (by positivity : 0 < a / 2) v
  have hmajor : Summable (fun x : Site => (2 / a) * g x) := by
    exact hshift.1.mul_left _
  have hpoint (x : Site) : f x ≤ (2 / a) * g x := by
    dsimp [f, g]
    exact gaussian_norm_sq_absorb ha
  have hsum : Summable f := by
    apply hmajor.of_nonneg_of_le
    · intro x
      dsimp [f]
      positivity
    · exact hpoint
  have hpi : Real.pi / (a / 2) = 2 * Real.pi / a := by
    field_simp [ne_of_gt ha]
  refine ⟨hsum, ?_⟩
  calc
    _ = ∑' x : Site, f x := by rfl
    _ ≤ ∑' x : Site, (2 / a) * g x := hsum.tsum_le_tsum hpoint hmajor
    _ = (2 / a) * ∑' x : Site, g x := tsum_mul_left
    _ ≤ (2 / a) * (4 * (1 + Real.sqrt (Real.pi / (a / 2))) ^ 2) :=
      mul_le_mul_of_nonneg_left hshift.2 (by positivity)
    _ = _ := by rw [hpi]; ring

/-- The lattice embedding into the plane preserves subtraction. -/
theorem siteToPlane_sub (x y : Site) :
    siteToPlane (y - x) = siteToPlane y - siteToPlane x := by
  ext i
  simp [siteToPlane]

/-- The sum of two scaled squared distances splits into a total displacement term and a completed square. -/
theorem gaussian_square_completion {k l : ℝ} (hk : 0 < k) (hl : 0 < l)
    (p q : Plane) :
    ‖p‖ ^ 2 / k + ‖q - p‖ ^ 2 / l =
      ‖q‖ ^ 2 / (k + l) + (k + l) / (k * l) *
        ‖p - (k / (k + l)) • q‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq p, EuclideanSpace.real_norm_sq_eq q,
    EuclideanSpace.real_norm_sq_eq (q - p),
    EuclideanSpace.real_norm_sq_eq (p - (k / (k + l)) • q)]
  simp only [Fin.sum_univ_two, WithLp.ofLp_sub, WithLp.ofLp_smul,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [ne_of_gt hk, ne_of_gt hl, ne_of_gt (add_pos hk hl)]
  ring_nf

/-- The unnormalized Gaussian convolution has the harmonic-time scale. -/
private theorem rawGaussian_convolution_control {c : ℝ} (hc : 0 < c)
    {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (y : Site) :
    Summable (fun x : Site => Real.exp (-c * ‖siteToPlane x‖ ^ 2 / k -
      c * ‖siteToPlane (y - x)‖ ^ 2 / l)) ∧
      ∑' x : Site, Real.exp (-c * ‖siteToPlane x‖ ^ 2 / k -
        c * ‖siteToPlane (y - x)‖ ^ 2 / l) ≤
      4 * (Real.sqrt 2 + Real.sqrt (Real.pi / c)) ^ 2 *
        ((k : ℝ) * l / (k + l)) * Real.exp (-c * ‖siteToPlane y‖ ^ 2 / (k + l)) := by
  let K : ℝ := k
  let L : ℝ := l
  let H : ℝ := K * L / (K + L)
  let a : ℝ := c * (K + L) / (K * L)
  have hK : 1 ≤ K := by dsimp [K]; exact_mod_cast hk
  have hL : 1 ≤ L := by dsimp [L]; exact_mod_cast hl
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hsumpos : 0 < K + L := by positivity
  have hprodpos : 0 < K * L := mul_pos hKpos hLpos
  have hHpos : 0 < H := by dsimp [H]; positivity
  have hHhalf : (1 / 2 : ℝ) ≤ H := by
    dsimp [H]
    have hmul : 2 * K * L ≥ K + L := by nlinarith [mul_nonneg (sub_nonneg.mpr hK) (sub_nonneg.mpr hL)]
    rw [le_div_iff₀ hsumpos]
    nlinarith
  have ha : 0 < a := by dsimp [a]; positivity
  have haH : a = c / H := by
    dsimp [a, H]
    field_simp [ne_of_gt hKpos, ne_of_gt hLpos, ne_of_gt hsumpos]
  let v : Plane := (K / (K + L)) • siteToPlane y
  have hshift := shiftedSiteGaussian_control ha v
  have hpoint (x : Site) :
      Real.exp (-c * ‖siteToPlane x‖ ^ 2 / K -
        c * ‖siteToPlane (y - x)‖ ^ 2 / L) =
        Real.exp (-c * ‖siteToPlane y‖ ^ 2 / (K + L)) *
          Real.exp (-a * ‖siteToPlane x - v‖ ^ 2) := by
    rw [siteToPlane_sub]
    rw [← Real.exp_add]
    congr 1
    have hsq := gaussian_square_completion hKpos hLpos
      (siteToPlane x) (siteToPlane y)
    dsimp [v, a]
    rw [show -c * ‖siteToPlane x‖ ^ 2 / K -
        c * ‖siteToPlane y - siteToPlane x‖ ^ 2 / L =
        -c * (‖siteToPlane x‖ ^ 2 / K +
          ‖siteToPlane y - siteToPlane x‖ ^ 2 / L) by ring, hsq]
    ring
  have hsum :
      (∑' x : Site, Real.exp (-c * ‖siteToPlane x‖ ^ 2 / K -
        c * ‖siteToPlane (y - x)‖ ^ 2 / L)) =
        Real.exp (-c * ‖siteToPlane y‖ ^ 2 / (K + L)) *
          (∑' x : Site, Real.exp (-a * ‖siteToPlane x - v‖ ^ 2)) := by
    calc
      _ = ∑' x : Site, Real.exp (-c * ‖siteToPlane y‖ ^ 2 / (K + L)) *
            Real.exp (-a * ‖siteToPlane x - v‖ ^ 2) := by
          apply tsum_congr
          intro x
          exact hpoint x
      _ = _ := hshift.1.tsum_mul_left _
  have hrawSummable : Summable (fun x : Site =>
      Real.exp (-c * ‖siteToPlane x‖ ^ 2 / K -
        c * ‖siteToPlane (y - x)‖ ^ 2 / L)) := by
    have hfun : (fun x : Site => Real.exp (-c * ‖siteToPlane x‖ ^ 2 / K -
        c * ‖siteToPlane (y - x)‖ ^ 2 / L)) =
        fun x => Real.exp (-c * ‖siteToPlane y‖ ^ 2 / (K + L)) *
          Real.exp (-a * ‖siteToPlane x - v‖ ^ 2) := by
      funext x
      exact hpoint x
    rw [hfun]
    exact hshift.1.mul_left _
  have hsqrt : Real.sqrt (Real.pi / a) =
      Real.sqrt (Real.pi / c) * Real.sqrt H := by
    rw [haH, show Real.pi / (c / H) = (Real.pi / c) * H by
      field_simp [ne_of_gt hc, ne_of_gt hHpos],
      Real.sqrt_mul (by positivity : 0 ≤ Real.pi / c)]
  have hroot : 1 + Real.sqrt (Real.pi / a) ≤
      (Real.sqrt 2 + Real.sqrt (Real.pi / c)) * Real.sqrt H := by
    rw [hsqrt]
    have h2 : 1 ≤ Real.sqrt 2 * Real.sqrt H := by
      have h := Real.sqrt_le_sqrt (by nlinarith [hHhalf] : 1 ≤ 2 * H)
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at h
      simpa using h
    nlinarith [Real.sqrt_nonneg (Real.pi / c), Real.sqrt_nonneg H]
  have hrootNonneg : 0 ≤ 1 + Real.sqrt (Real.pi / a) := by positivity
  have hbound : 4 * (1 + Real.sqrt (Real.pi / a)) ^ 2 ≤
      4 * (Real.sqrt 2 + Real.sqrt (Real.pi / c)) ^ 2 * H := by
    have hs := (sq_le_sq₀ hrootNonneg (by positivity)).2 hroot
    rw [mul_pow, Real.sq_sqrt hHpos.le] at hs
    nlinarith [hs]
  refine ⟨hrawSummable, ?_⟩
  calc
    _ = Real.exp (-c * ‖siteToPlane y‖ ^ 2 / (K + L)) *
        (∑' x : Site, Real.exp (-a * ‖siteToPlane x - v‖ ^ 2)) := hsum
    _ ≤ Real.exp (-c * ‖siteToPlane y‖ ^ 2 / (K + L)) *
        (4 * (1 + Real.sqrt (Real.pi / a)) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hshift.2 (Real.exp_nonneg _)
    _ ≤ 4 * (Real.sqrt 2 + Real.sqrt (Real.pi / c)) ^ 2 * H *
        Real.exp (-c * ‖siteToPlane y‖ ^ 2 / (K + L)) := by
      calc
        _ ≤ Real.exp (-c * ‖siteToPlane y‖ ^ 2 / (K + L)) *
            (4 * (Real.sqrt 2 + Real.sqrt (Real.pi / c)) ^ 2 * H) :=
          mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg _)
        _ = _ := by ring
    _ = _ := by dsimp [H, K, L]

/-- A two-rate Gaussian convolution retains the slower spatial rate. -/
theorem rawGaussian_twoRate_control {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) (w : Site) :
    Summable (fun x : Site => Real.exp
      (-a * ‖siteToPlane x‖ ^ 2 / k - b * ‖siteToPlane (w - x)‖ ^ 2 / n)) ∧
      ∑' x : Site, Real.exp
        (-a * ‖siteToPlane x‖ ^ 2 / k - b * ‖siteToPlane (w - x)‖ ^ 2 / n) ≤
        8 * (1 + Real.pi / a) * k *
          Real.exp (-a * ‖siteToPlane w‖ ^ 2 / (k + n)) := by
  let K : ℝ := (k : ℝ) / a
  let L : ℝ := (n : ℝ) / b
  let H : ℝ := K * L / (K + L)
  let d : ℝ := (K + L) / (K * L)
  let γ : ℝ := 1 / (K + L)
  let v : Plane := (K / (K + L)) • siteToPlane w
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hK : 0 < K := by dsimp [K]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hKL : 0 < K + L := by positivity
  have hprod : 0 < K * L := mul_pos hK hL
  have hH : 0 < H := by dsimp [H]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hpoint (x : Site) :
      Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k -
          b * ‖siteToPlane (w - x)‖ ^ 2 / n) =
        Real.exp (-γ * ‖siteToPlane w‖ ^ 2) *
          Real.exp (-d * ‖siteToPlane x - v‖ ^ 2) := by
    rw [siteToPlane_sub, ← Real.exp_add]
    congr 1
    have hsq := gaussian_square_completion hK hL
      (siteToPlane x) (siteToPlane w)
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_one.trans_le hk))
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_one.trans_le hn))
    have hfirst : -a * ‖siteToPlane x‖ ^ 2 / k =
        -‖siteToPlane x‖ ^ 2 / K := by
      dsimp [K]
      field_simp [hkR, ne_of_gt ha]
    have hsecond : -b * ‖siteToPlane w - siteToPlane x‖ ^ 2 / n =
        -‖siteToPlane w - siteToPlane x‖ ^ 2 / L := by
      dsimp [L]
      field_simp [hnR, ne_of_gt hb]
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
                ‖siteToPlane w - siteToPlane x‖ ^ 2 / L) := by
            ring
          _ = -(‖siteToPlane w‖ ^ 2 / (K + L) +
                (K + L) / (K * L) *
                  ‖siteToPlane x - (K / (K + L)) • siteToPlane w‖ ^ 2) := hsqNeg
          _ = -γ * ‖siteToPlane w‖ ^ 2 + -d * ‖siteToPlane x - v‖ ^ 2 := by
            dsimp [γ, d, v]
            ring
  have hshift := shiftedSiteGaussian_control hd v
  have hrawSummable : Summable (fun x : Site => Real.exp
      (-a * ‖siteToPlane x‖ ^ 2 / k - b * ‖siteToPlane (w - x)‖ ^ 2 / n)) := by
    have hfun : (fun x : Site => Real.exp
        (-a * ‖siteToPlane x‖ ^ 2 / k - b * ‖siteToPlane (w - x)‖ ^ 2 / n)) =
        fun x => Real.exp (-γ * ‖siteToPlane w‖ ^ 2) *
          Real.exp (-d * ‖siteToPlane x - v‖ ^ 2) := by
      funext x
      exact hpoint x
    rw [hfun]
    exact hshift.1.mul_left _
  have hsum :
      (∑' x : Site, Real.exp (-a * ‖siteToPlane x‖ ^ 2 / k -
        b * ‖siteToPlane (w - x)‖ ^ 2 / n)) =
        Real.exp (-γ * ‖siteToPlane w‖ ^ 2) *
          (∑' x : Site, Real.exp (-d * ‖siteToPlane x - v‖ ^ 2)) := by
    calc
      _ = ∑' x : Site, Real.exp (-γ * ‖siteToPlane w‖ ^ 2) *
            Real.exp (-d * ‖siteToPlane x - v‖ ^ 2) := by
          apply tsum_congr
          intro x
          exact hpoint x
      _ = _ := hshift.1.tsum_mul_left _
  have hHle : H ≤ K := by
    dsimp [H]
    rw [div_le_iff₀ hKL]
    nlinarith [sq_nonneg K]
  have hroot : Real.sqrt (Real.pi / d) ≤ Real.sqrt (Real.pi / a) * Real.sqrt k := by
    have hdeq : Real.pi / d = Real.pi * H := by
      dsimp [d]
      dsimp [H]
      field_simp [ne_of_gt hprod, ne_of_gt hKL]
    have hright : Real.sqrt (Real.pi / a) * Real.sqrt k =
        Real.sqrt Real.pi * Real.sqrt K := by
      rw [← Real.sqrt_mul (by positivity : 0 ≤ Real.pi / a)]
      rw [show (Real.pi / a) * k = Real.pi * K by
        dsimp [K]
        field_simp [ne_of_gt ha]]
      rw [Real.sqrt_mul Real.pi_nonneg]
    rw [hdeq, Real.sqrt_mul Real.pi_nonneg, hright]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hHle) (Real.sqrt_nonneg _)
  have hrootSq : (1 + Real.sqrt (Real.pi / d)) ^ 2 ≤
      2 * (1 + Real.pi / a) * k := by
    have hroot' : 1 + Real.sqrt (Real.pi / d) ≤
        (1 + Real.sqrt (Real.pi / a)) * Real.sqrt k := by
      have hkroot : 1 ≤ Real.sqrt k := by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hk)
      nlinarith [Real.sqrt_nonneg (Real.pi / a), Real.sqrt_nonneg (Real.pi / d)]
    have hsq := (sq_le_sq₀ (by positivity) (by positivity)).2 hroot'
    rw [mul_pow, Real.sq_sqrt (by exact_mod_cast (Nat.zero_le k))] at hsq
    have hx : (Real.sqrt (Real.pi / a)) ^ 2 = Real.pi / a :=
      Real.sq_sqrt (by positivity)
    nlinarith [sq_nonneg (Real.sqrt (Real.pi / a) - 1)]
  have hrate : a / (k + n) ≤ γ := by
    change a / ((k : ℝ) + n) ≤ 1 / (K + L)
    have hkR : 0 < (k : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hk)
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hn)
    have hden₁ : 0 < (k : ℝ) + n := by positivity
    have hden₂ : 0 < K + L := hKL
    rw [div_le_div_iff₀ hden₁ hden₂]
    dsimp [K, L]
    field_simp [ne_of_gt ha, ne_of_gt hb]
    nlinarith [mul_le_mul_of_nonneg_right hab hnR.le]
  refine ⟨hrawSummable, ?_⟩
  calc
    _ = Real.exp (-γ * ‖siteToPlane w‖ ^ 2) *
        (∑' x : Site, Real.exp (-d * ‖siteToPlane x - v‖ ^ 2)) := hsum
    _ ≤ Real.exp (-γ * ‖siteToPlane w‖ ^ 2) *
        (4 * (1 + Real.sqrt (Real.pi / d)) ^ 2) :=
      mul_le_mul_of_nonneg_left hshift.2 (Real.exp_nonneg _)
    _ ≤ Real.exp (-γ * ‖siteToPlane w‖ ^ 2) *
        (8 * (1 + Real.pi / a) * k) := by
      exact mul_le_mul_of_nonneg_left (by nlinarith [hrootSq]) (Real.exp_nonneg _)
    _ ≤ Real.exp (-a * ‖siteToPlane w‖ ^ 2 / (k + n)) *
        (8 * (1 + Real.pi / a) * k) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply Real.exp_le_exp.mpr
      have hx : 0 ≤ ‖siteToPlane w‖ ^ 2 := sq_nonneg _
      have hmul := mul_le_mul_of_nonneg_right hrate hx
      have hmul' : a * ‖siteToPlane w‖ ^ 2 / (k + n) ≤
          γ * ‖siteToPlane w‖ ^ 2 := by
        calc
          _ = (a / (k + n)) * ‖siteToPlane w‖ ^ 2 := by ring
          _ ≤ _ := hmul
      calc
        -γ * ‖siteToPlane w‖ ^ 2 = -(γ * ‖siteToPlane w‖ ^ 2) := by ring
        _ ≤ -(a * ‖siteToPlane w‖ ^ 2 / (k + n)) := neg_le_neg hmul'
        _ = -a * ‖siteToPlane w‖ ^ 2 / (k + n) := by ring
    _ = _ := by ring

private theorem hatGaussian_parity_add {k l : ℕ} (x y : Site)
    (hp : Even ((k : ℤ) + x 0 + x 1))
    (hq : Even ((l : ℤ) + (y - x) 0 + (y - x) 1)) :
    Even (((k + l : ℕ) : ℤ) + y 0 + y 1) := by
  have hsum : ((k : ℤ) + x 0 + x 1) +
      ((l : ℤ) + (y - x) 0 + (y - x) 1) =
        ((k + l : ℕ) : ℤ) + y 0 + y 1 := by
    simp only [Nat.cast_add, Pi.sub_apply]
    ring
  rw [← hsum]
  exact Even.add hp hq

/-- Convolution of the parity-correct Gaussian envelopes preserves the heat scale.
The sum is summable by `hatGaussian_summable`. -/
theorem hatGaussian_convolution_le {c : ℝ} (hc : 0 < c)
    {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (y : Site) :
    ∑' x : Site, hatGaussian c k x * hatGaussian c l (y - x) ≤
      4 * (Real.sqrt 2 + Real.sqrt (Real.pi / c)) ^ 2 *
        hatGaussian c (k + l) y := by
  have hkne : k ≠ 0 := by omega
  have hlne : l ≠ 0 := by omega
  let K : ℝ := k
  let L : ℝ := l
  let C : ℝ := 4 * (Real.sqrt 2 + Real.sqrt (Real.pi / c)) ^ 2
  let raw : Site → ℝ := fun x =>
    Real.exp (-c * ‖siteToPlane x‖ ^ 2 / K -
      c * ‖siteToPlane (y - x)‖ ^ 2 / L)
  let base : Site → ℝ := fun x => K⁻¹ * L⁻¹ * raw x
  have hK : 0 < K := by dsimp [K]; exact_mod_cast Nat.zero_lt_of_lt hk
  have hL : 0 < L := by dsimp [L]; exact_mod_cast Nat.zero_lt_of_lt hl
  have hraw := rawGaussian_convolution_control hc hk hl y
  have hbaseSummable : Summable base := by
    dsimp [base, raw]
    exact hraw.1.mul_left (K⁻¹ * L⁻¹)
  have hbaseeq (x : Site) : K⁻¹ * L⁻¹ * raw x =
      (K⁻¹ * Real.exp (-c * ‖siteToPlane x‖ ^ 2 / K)) *
        (L⁻¹ * Real.exp (-c * ‖siteToPlane (y - x)‖ ^ 2 / L)) := by
    dsimp [raw]
    rw [show -c * ‖siteToPlane x‖ ^ 2 / K -
        c * ‖siteToPlane (y - x)‖ ^ 2 / L =
        (-c * ‖siteToPlane x‖ ^ 2 / K) +
          (-c * ‖siteToPlane (y - x)‖ ^ 2 / L) by ring,
      Real.exp_add]
    ring
  have hpoint (x : Site) :
      0 ≤ hatGaussian c k x * hatGaussian c l (y - x) ∧
        hatGaussian c k x * hatGaussian c l (y - x) ≤ base x := by
    by_cases hp : Even ((k : ℤ) + x 0 + x 1)
    · by_cases hq : Even ((l : ℤ) + (y - x) 0 + (y - x) 1)
      · have hval : hatGaussian c k x * hatGaussian c l (y - x) = base x := by
          have hq' : Even ((l : ℤ) + (y 0 - x 0) + (y 1 - x 1)) := by
            simpa only [Pi.sub_apply] using hq
          simpa [hatGaussian, hkne, hlne, hp, hq', base, K, L] using (hbaseeq x).symm
        rw [hval]
        exact ⟨by positivity, le_rfl⟩
      · constructor
        · have hq' : ¬ Even ((l : ℤ) + (y 0 - x 0) + (y 1 - x 1)) := by
            simpa only [Pi.sub_apply] using hq
          have hzero : hatGaussian c k x * hatGaussian c l (y - x) = 0 := by
            simp [hatGaussian, hkne, hlne, hp, hq']
          rw [hzero]
        · have hq' : ¬ Even ((l : ℤ) + (y 0 - x 0) + (y 1 - x 1)) := by
            simpa only [Pi.sub_apply] using hq
          have hzero : hatGaussian c k x * hatGaussian c l (y - x) = 0 := by
            simp [hatGaussian, hkne, hlne, hp, hq']
          rw [hzero]
          positivity
    · constructor
      · have hzero : hatGaussian c k x * hatGaussian c l (y - x) = 0 := by
          simp [hatGaussian, hkne, hlne, hp]
        rw [hzero]
      · have hzero : hatGaussian c k x * hatGaussian c l (y - x) = 0 := by
          simp [hatGaussian, hkne, hlne, hp]
        rw [hzero]
        positivity
  have hprodSummable : Summable (fun x : Site => hatGaussian c k x * hatGaussian c l (y - x)) :=
    hbaseSummable.of_nonneg_of_le (fun x => (hpoint x).1) (fun x => (hpoint x).2)
  by_cases hpar : Even (((k + l : ℕ) : ℤ) + y 0 + y 1)
  · have hsumle := hprodSummable.tsum_le_tsum (fun x => (hpoint x).2) hbaseSummable
    have hbaseSum : (∑' x : Site, base x) = K⁻¹ * L⁻¹ * (∑' x : Site, raw x) := by
      exact hraw.1.tsum_mul_left _
    have hrawBound : (∑' x : Site, raw x) ≤
        C * (K * L / (K + L)) *
          Real.exp (-c * ‖siteToPlane y‖ ^ 2 / (K + L)) := by
      simpa [raw, C, K, L] using hraw.2
    have hrawScale : K⁻¹ * L⁻¹ * (∑' x : Site, raw x) ≤
        C / (K + L) * Real.exp (-c * ‖siteToPlane y‖ ^ 2 / (K + L)) := by
      calc
        _ ≤ K⁻¹ * L⁻¹ *
            (C * (K * L / (K + L)) *
              Real.exp (-c * ‖siteToPlane y‖ ^ 2 / (K + L))) :=
          mul_le_mul_of_nonneg_left hrawBound (by positivity)
        _ = _ := by
          field_simp [ne_of_gt hK, ne_of_gt hL, ne_of_gt (add_pos hK hL)]
    have htarget : C / (K + L) * Real.exp (-c * ‖siteToPlane y‖ ^ 2 / (K + L)) =
        4 * (Real.sqrt 2 + Real.sqrt (Real.pi / c)) ^ 2 * hatGaussian c (k + l) y := by
      have hpar' : Even ((k : ℤ) + (l : ℤ) + y 0 + y 1) := by
        simpa only [Nat.cast_add] using hpar
      have hsumK : K + L = (k + l : ℕ) := by
        dsimp [K, L]
        exact_mod_cast Nat.cast_add k l
      rw [hsumK]
      simp [C, hatGaussian, hkne, hlne, hpar']
      field_simp [ne_of_gt (by positivity : (0 : ℝ) < (k + l : ℕ))]
    calc
      _ ≤ ∑' x : Site, base x := hsumle
      _ = K⁻¹ * L⁻¹ * (∑' x : Site, raw x) := hbaseSum
      _ ≤ C / (K + L) * Real.exp (-c * ‖siteToPlane y‖ ^ 2 / (K + L)) := hrawScale
      _ = _ := htarget
  · have hzero (x : Site) : hatGaussian c k x * hatGaussian c l (y - x) = 0 := by
      by_cases hp : Even ((k : ℤ) + x 0 + x 1)
      · by_cases hq : Even ((l : ℤ) + (y - x) 0 + (y - x) 1)
        · exact (hpar (hatGaussian_parity_add x y hp hq)).elim
        · have hq' : ¬ Even ((l : ℤ) + (y 0 - x 0) + (y 1 - x 1)) := by
            simpa only [Pi.sub_apply] using hq
          simp [hatGaussian, hkne, hlne, hp, hq']
      · simp [hatGaussian, hkne, hlne, hp]
    have hleft : (∑' x : Site, hatGaussian c k x * hatGaussian c l (y - x)) = 0 := by
      calc
        _ = ∑' x : Site, (0 : ℝ) := tsum_congr (fun x => hzero x)
        _ = 0 := tsum_zero
    have hright : 4 * (Real.sqrt 2 + Real.sqrt (Real.pi / c)) ^ 2 *
        hatGaussian c (k + l) y = 0 := by
      have hpar' : ¬ Even ((k : ℤ) + (l : ℤ) + y 0 + y 1) := by
        simpa only [Nat.cast_add] using hpar
      simp [hatGaussian, hkne, hlne, hpar']
    rw [hleft, hright]

private theorem site_gaussian_summable {a : ℝ} (ha : 0 < a) :
    Summable (fun z : Site => Real.exp (-a * ‖siteToPlane z‖ ^ 2)) := by
  let f : ℤ → ℝ := fun z => gaussian1D a (z : ℝ)
  have hf : Summable f := gaussian1D_int_summable ha
  have hprod : Summable (fun p : ℤ × ℤ => f p.1 * f p.2) := by
    apply (summable_prod_of_nonneg
      (fun p : ℤ × ℤ => mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))).2
    constructor
    · intro x
      exact hf.mul_left (f x)
    · change Summable (fun x : ℤ => ∑' y : ℤ, f x * f y)
      have heq : (fun x : ℤ => ∑' y : ℤ, f x * f y) =
          fun x => f x * (∑' y : ℤ, f y) := by
        funext x
        exact hf.tsum_mul_left (f x)
      rw [heq]
      exact hf.mul_right (∑' y : ℤ, f y)
  let e := Critical2DKPZ.MomentBounds.siteEquivProd.symm
  apply (e.summable_iff).1
  have hcomp : Summable (fun p : ℤ × ℤ =>
      Real.exp (-a * ‖siteToPlane (e p)‖ ^ 2)) := by
    apply hprod.congr
    intro p
    rw [Critical2DKPZ.norm_siteToPlane_sq]
    have h0 : (e p) 0 = p.1 := by
      change (![p.1, p.2] : Site) 0 = p.1
      rfl
    have h1 : (e p) 1 = p.2 := by
      change (![p.1, p.2] : Site) 1 = p.2
      rfl
    rw [h0, h1]
    calc
      f p.1 * f p.2 =
          Real.exp (-a * (p.1 : ℝ) ^ 2) * Real.exp (-a * (p.2 : ℝ) ^ 2) := by
            simp [f, gaussian1D]
      _ = Real.exp (-a * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
  change Summable (fun p : ℤ × ℤ =>
    Real.exp (-a * ‖siteToPlane (e p)‖ ^ 2))
  exact hcomp

private theorem site_gaussian_tsum_bound {a : ℝ} (ha : 0 < a) :
    ∑' z : Site, Real.exp (-a * ‖siteToPlane z‖ ^ 2) ≤
      (1 + Real.sqrt (Real.pi / a)) ^ 2 := by
  let f : ℤ → ℝ := fun z => gaussian1D a (z : ℝ)
  have hf : Summable f := gaussian1D_int_summable ha
  have hprod : Summable (fun p : ℤ × ℤ => f p.1 * f p.2) := by
    apply (summable_prod_of_nonneg
      (fun p : ℤ × ℤ => mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))).2
    constructor
    · intro x
      exact hf.mul_left (f x)
    · change Summable (fun x : ℤ => ∑' y : ℤ, f x * f y)
      have heq : (fun x : ℤ => ∑' y : ℤ, f x * f y) =
          fun x => f x * (∑' y : ℤ, f y) := by
        funext x
        exact hf.tsum_mul_left (f x)
      rw [heq]
      exact hf.mul_right (∑' y : ℤ, f y)
  have hpair :
      (∑' p : ℤ × ℤ, Real.exp (-a * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) =
        (∑' z : ℤ, f z) ^ 2 := by
    have heq : (fun p : ℤ × ℤ =>
        Real.exp (-a * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) =
          fun p => f p.1 * f p.2 := by
      funext p
      rw [show -a * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) =
          (-a * (p.1 : ℝ) ^ 2) + (-a * (p.2 : ℝ) ^ 2) by ring, Real.exp_add]
      simp [f, gaussian1D]
    rw [heq, ← hf.tsum_mul_tsum hf hprod]
    ring
  have hSitePair :
      (∑' z : Site, Real.exp (-a * ‖siteToPlane z‖ ^ 2)) =
        ∑' p : ℤ × ℤ, Real.exp (-a * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
    let e := Critical2DKPZ.MomentBounds.siteEquivProd.symm
    calc
      _ = ∑' p : ℤ × ℤ, Real.exp (-a * ‖siteToPlane (e p)‖ ^ 2) :=
        e.tsum_eq (fun z : Site => Real.exp (-a * ‖siteToPlane z‖ ^ 2)) |>.symm
      _ = _ := by
        apply tsum_congr
        intro p
        rw [Critical2DKPZ.norm_siteToPlane_sq]
        have h0 : (e p) 0 = p.1 := by
          change (![p.1, p.2] : Site) 0 = p.1
          rfl
        have h1 : (e p) 1 = p.2 := by
          change (![p.1, p.2] : Site) 1 = p.2
          rfl
        rw [h0, h1]
  rw [hSitePair, hpair]
  have h1 := intGaussian_tsum_le ha
  have hsum_nonneg : 0 ≤ (∑' z : ℤ, f z) :=
    tsum_nonneg (fun z => Real.exp_nonneg _)
  have hKnonneg : 0 ≤ 1 + Real.sqrt (Real.pi / a) := by positivity
  have hsquare := (sq_le_sq₀ hsum_nonneg hKnonneg).2 (by simpa [f] using h1)
  simpa [pow_two] using hsquare

/-- The parity-correct Gaussian envelope has uniformly bounded total mass.
The envelope is summable by `hatGaussian_summable`. -/
theorem hatGaussian_totalMass_le {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 1 ≤ n) :
    ∑' x : Site, hatGaussian c n x ≤ (1 + Real.sqrt (Real.pi / c)) ^ 2 := by
  let t : ℝ := n
  have ht : 0 < t := by dsimp [t]; exact_mod_cast (Nat.zero_lt_one.trans_le hn)
  have hcdiv : 0 < c / t := div_pos hc ht
  have hSiteSummable := site_gaussian_summable hcdiv
  have hhatPoint (x : Site) : 0 ≤ hatGaussian c n x ∧
      hatGaussian c n x ≤ t⁻¹ * Real.exp (-(c / t * ‖siteToPlane x‖ ^ 2)) := by
    have htn : (n : ℝ) = t := rfl
    have hn0 : n ≠ 0 := by omega
    have hexp : -(c * ‖siteToPlane x‖ ^ 2) / t =
        -(c / t * ‖siteToPlane x‖ ^ 2) := by
      field_simp [ne_of_gt ht]
    by_cases hp : Even ((n : ℤ) + x 0 + x 1)
    · constructor
      · simp [hatGaussian, hn0, hp, t, htn]
        positivity
      · simp [hatGaussian, hn0, hp, t, htn]
        rw [hexp]
    · constructor
      · simp [hatGaussian, hn0, hp, t, htn]
      · simp [hatGaussian, hn0, hp, t, htn]
        positivity
  have hrawBaseSummable : Summable (fun x : Site =>
      Real.exp (-(c / t * ‖siteToPlane x‖ ^ 2))) := by
    apply hSiteSummable.congr
    intro x
    congr 1
    ring
  have hrawSummable : Summable (fun x : Site =>
      t⁻¹ * Real.exp (-(c / t * ‖siteToPlane x‖ ^ 2))) :=
    hrawBaseSummable.mul_left _
  have hhatSummable : Summable (fun x : Site => hatGaussian c n x) :=
    hrawSummable.of_nonneg_of_le (fun x => (hhatPoint x).1) (fun x => (hhatPoint x).2)
  have hrawBound := site_gaussian_tsum_bound hcdiv
  have hrawBound' : (∑' x : Site,
      Real.exp (-(c / t * ‖siteToPlane x‖ ^ 2))) ≤
        (1 + Real.sqrt (Real.pi / (c / t))) ^ 2 := by
    calc
      _ = ∑' x : Site, Real.exp (-(c / t) * ‖siteToPlane x‖ ^ 2) := by
        apply tsum_congr
        intro x
        congr 1
        ring
      _ ≤ _ := hrawBound
  have hrawSum : (∑' x : Site,
      t⁻¹ * Real.exp (-(c / t * ‖siteToPlane x‖ ^ 2))) ≤
        t⁻¹ * (1 + Real.sqrt (Real.pi / (c / t))) ^ 2 := by
    calc
      _ = t⁻¹ * (∑' x : Site, Real.exp (-(c / t * ‖siteToPlane x‖ ^ 2))) :=
        hrawBaseSummable.tsum_mul_left _
      _ ≤ _ := mul_le_mul_of_nonneg_left hrawBound' (inv_nonneg.mpr ht.le)
  have hroot : Real.sqrt (Real.pi / (c / t)) =
      Real.sqrt (Real.pi / c) * Real.sqrt t := by
    rw [show Real.pi / (c / t) = (Real.pi / c) * t by field_simp [ne_of_gt hc, ne_of_gt ht],
      Real.sqrt_mul (div_nonneg Real.pi_pos.le hc.le)]
  have htn : (1 : ℝ) ≤ t := by dsimp [t]; exact_mod_cast hn
  have hsqrtT : 1 ≤ Real.sqrt t := by simpa using Real.sqrt_le_sqrt htn
  have hrootle : 1 + Real.sqrt (Real.pi / c) * Real.sqrt t ≤
      (1 + Real.sqrt (Real.pi / c)) * Real.sqrt t := by
    have hrootnonneg : 0 ≤ Real.sqrt (Real.pi / c) := Real.sqrt_nonneg _
    nlinarith
  have hsquare :
      (1 + Real.sqrt (Real.pi / (c / t))) ^ 2 ≤
        (1 + Real.sqrt (Real.pi / c)) ^ 2 * t := by
    rw [hroot]
    have hright_nonneg : 0 ≤ (1 + Real.sqrt (Real.pi / c)) * Real.sqrt t := by positivity
    have hleft_nonneg : 0 ≤ 1 + Real.sqrt (Real.pi / c) * Real.sqrt t := by positivity
    have hs := (sq_le_sq₀ hleft_nonneg hright_nonneg).2 hrootle
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ t)] at hs
    simpa [pow_two] using hs
  calc
    _ ≤ t⁻¹ * (1 + Real.sqrt (Real.pi / (c / t))) ^ 2 :=
      (hhatSummable.tsum_le_tsum (fun x => (hhatPoint x).2) hrawSummable).trans hrawSum
    _ ≤ (1 + Real.sqrt (Real.pi / c)) ^ 2 := by
      rw [hroot]
      have hsquare' :
          (1 + Real.sqrt (Real.pi / c) * Real.sqrt t) ^ 2 ≤
            (1 + Real.sqrt (Real.pi / c)) ^ 2 * t := by simpa [hroot] using hsquare
      have hmul := mul_le_mul_of_nonneg_left hsquare' (inv_nonneg.mpr ht.le)
      calc
        _ ≤ t⁻¹ * ((1 + Real.sqrt (Real.pi / c)) ^ 2 * t) := hmul
        _ = _ := by field_simp [ne_of_gt ht]

/-- The parity restricted lattice Gaussian kernel is nonnegative. -/
theorem hatGaussian_nonneg {c : ℝ} (n : ℕ) (x : Site) :
    0 ≤ hatGaussian c n x := by
  by_cases hn : n = 0
  · subst n
    by_cases hx : x = 0 <;> simp [hatGaussian, hx]
  · by_cases hp : Even ((n : ℤ) + x 0 + x 1)
    · simp [hatGaussian, hn, hp]
      positivity
    · simp [hatGaussian, hn, hp]

/-- For `n ≥ 1` the Gaussian envelope is at most `1/n`: its exponential factor is at most one. -/
theorem hatGaussian_le_inv {c : ℝ} (hc : 0 < c) {n : ℕ}
    (hn : 1 ≤ n) (x : Site) : hatGaussian c n x ≤ (n : ℝ)⁻¹ := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hn)
  have hn0 : n ≠ 0 := by omega
  have hexp : Real.exp (-(c * ‖siteToPlane x‖ ^ 2) / n) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hnum : -(c * ‖siteToPlane x‖ ^ 2) ≤ 0 :=
      neg_nonpos.mpr (mul_nonneg hc.le (sq_nonneg _))
    exact div_nonpos_of_nonpos_of_nonneg hnum hnR.le
  by_cases hp : Even ((n : ℤ) + x 0 + x 1)
  · simp [hatGaussian, hn0, hp]
    calc
      (n : ℝ)⁻¹ * Real.exp (-(c * ‖siteToPlane x‖ ^ 2) / n) ≤
          (n : ℝ)⁻¹ * 1 := by
            gcongr
      _ = (n : ℝ)⁻¹ := by ring
  · simp [hatGaussian, hn0, hp]

/-- The parity restricted lattice Gaussian kernel is summable at positive rate and time. -/
theorem hatGaussian_summable {c : ℝ} (hc : 0 < c) {n : ℕ}
    (hn : 1 ≤ n) : Summable (fun x : Site => hatGaussian c n x) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hn)
  have hcdiv : 0 < c / n := div_pos hc hnR
  have hsite := site_gaussian_summable hcdiv
  have hraw : Summable (fun x : Site =>
      Real.exp (-(c / n * ‖siteToPlane x‖ ^ 2))) := by
    apply hsite.congr
    intro x
    congr 1
    ring
  have hmaj : Summable (fun x : Site =>
      (n : ℝ)⁻¹ * Real.exp (-(c / n * ‖siteToPlane x‖ ^ 2))) :=
    hraw.mul_left _
  apply hmaj.of_nonneg_of_le
  · exact fun x => hatGaussian_nonneg n x
  · intro x
    have hne : n ≠ 0 := by omega
    have hexp : -(c * ‖siteToPlane x‖ ^ 2) / n =
        -(c / n * ‖siteToPlane x‖ ^ 2) := by
      field_simp [ne_of_gt hnR]
    by_cases hp : Even ((n : ℤ) + x 0 + x 1)
    · simp [hatGaussian, hne, hp, hexp]
    · simp [hatGaussian, hne, hp]
      positivity

private theorem srwKernel_sq_le_hatGaussian {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hkernel : ∀ n x, srwKernel n x ≤ C * hatGaussian c n x)
    {n : ℕ} (hn : 1 ≤ n) (x : Site) :
    (srwKernel n x) ^ 2 ≤ C ^ 2 / n * hatGaussian c n x := by
  have hq : 0 ≤ srwKernel n x := Critical2DKPZ.srwKernel_nonneg _ _
  have hg : 0 ≤ hatGaussian c n x := hatGaussian_nonneg n x
  have hbound := hkernel n x
  have hsq : (srwKernel n x) ^ 2 ≤ (C * hatGaussian c n x) ^ 2 :=
    (sq_le_sq₀ hq (mul_nonneg hC hg)).2 hbound
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hn)
  have hgle := hatGaussian_le_inv hc hn x
  have hgsq : hatGaussian c n x ^ 2 ≤ (n : ℝ)⁻¹ * hatGaussian c n x := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right hgle hg
  calc
    (srwKernel n x) ^ 2 ≤ (C * hatGaussian c n x) ^ 2 := hsq
    _ = C ^ 2 * hatGaussian c n x ^ 2 := by rw [mul_pow]
    _ ≤ C ^ 2 * ((n : ℝ)⁻¹ * hatGaussian c n x) :=
      mul_le_mul_of_nonneg_left hgsq (sq_nonneg C)
    _ = C ^ 2 / n * hatGaussian c n x := by
      simp only [div_eq_mul_inv]
      ring

/-- Near-range bound (`k < l ≤ 3k`) for the squared kernel difference against the Gaussian
envelope, given a kernel bound by the envelope. The envelope is summable by
`hatGaussian_summable`. -/
theorem hatGaussian_sq_diff_near {c C : ℝ} (hc : 0 < c)
    (hC : 0 < C)
    (hkernel : ∀ n x, srwKernel n x ≤ C * hatGaussian c n x)
    {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hnear : l ≤ 3 * k)
    (w : Site) :
    ∑' y : Site, hatGaussian c k y *
      (srwKernel (l - k) (w - y) - srwKernel l w) ^ 2 ≤
      (6 * C ^ 2 * (4 * (Real.sqrt 2 + Real.sqrt (Real.pi / c)) ^ 2) +
        4 * C ^ 2 * (1 + Real.sqrt (Real.pi / c)) ^ 2) *
        (k : ℝ) / (l * (l - k)) * hatGaussian c l w := by
  let n : ℕ := l - k
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hn)
  have hl : 1 ≤ l := le_trans hk (Nat.le_of_lt hkl)
  have hlR : 0 < (l : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le hl)
  have hsumK : Summable (fun y : Site => hatGaussian c k y) :=
    hatGaussian_summable hc hk
  have hmass := hatGaussian_totalMass_le hc hk
  let M : ℝ := (1 + Real.sqrt (Real.pi / c)) ^ 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let K : ℝ := 4 * (Real.sqrt 2 + Real.sqrt (Real.pi / c)) ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hconv := hatGaussian_convolution_le hc hk hn w
  have hgnn (m : ℕ) (z : Site) : 0 ≤ hatGaussian c m z :=
    hatGaussian_nonneg m z
  have hgle (m : ℕ) (hm : 1 ≤ m) (z : Site) :
      hatGaussian c m z ≤ (m : ℝ)⁻¹ := hatGaussian_le_inv hc hm z
  have hq2n (z : Site) :
      (srwKernel n z) ^ 2 ≤ C ^ 2 / n * hatGaussian c n z :=
    srwKernel_sq_le_hatGaussian hc hC.le hkernel hn z
  have hq2l : (srwKernel l w) ^ 2 ≤ C ^ 2 / l * hatGaussian c l w :=
    srwKernel_sq_le_hatGaussian hc hC.le hkernel hl w
  have hqnConst (z : Site) : (srwKernel n z) ^ 2 ≤ C ^ 2 / n ^ 2 := by
    calc
      _ ≤ C ^ 2 / n * hatGaussian c n z := hq2n z
      _ ≤ C ^ 2 / n * (n : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left (hgle n hn z) (by positivity)
      _ = C ^ 2 / n ^ 2 := by
        simp only [div_eq_mul_inv]
        ring
  have hterm1Summable : Summable (fun y : Site =>
      hatGaussian c k y * (srwKernel n (w - y)) ^ 2) := by
    have hmajor : Summable (fun y : Site =>
        hatGaussian c k y * (C ^ 2 / n ^ 2)) := by
      simpa only [mul_comm] using hsumK.mul_left (C ^ 2 / n ^ 2)
    apply hmajor.of_nonneg_of_le
    · intro y
      exact mul_nonneg (hgnn k y) (sq_nonneg _)
    · intro y
      exact mul_le_mul_of_nonneg_left (hqnConst (w - y)) (hgnn k y)
  have hprodSummable : Summable (fun y : Site =>
      hatGaussian c k y * hatGaussian c n (w - y)) := by
    have hmajor : Summable (fun y : Site =>
        hatGaussian c k y * (n : ℝ)⁻¹) := by
      simpa only [mul_comm] using hsumK.mul_left ((n : ℝ)⁻¹)
    apply hmajor.of_nonneg_of_le
    · intro y
      exact mul_nonneg (hgnn k y) (hgnn n (w - y))
    · intro y
      exact mul_le_mul_of_nonneg_left (hgle n hn (w - y)) (hgnn k y)
  have hterm1 :
      ∑' y : Site, hatGaussian c k y * (srwKernel n (w - y)) ^ 2 ≤
        C ^ 2 / n * (K * hatGaussian c (k + n) w) := by
    have hpoint (y : Site) :
        hatGaussian c k y * (srwKernel n (w - y)) ^ 2 ≤
          (C ^ 2 / n) * (hatGaussian c k y * hatGaussian c n (w - y)) := by
      calc
        _ ≤ hatGaussian c k y * (C ^ 2 / n * hatGaussian c n (w - y)) :=
          mul_le_mul_of_nonneg_left (hq2n (w - y)) (hgnn k y)
        _ = _ := by ring
    have hsummajor : Summable (fun y : Site =>
        (C ^ 2 / n) * (hatGaussian c k y * hatGaussian c n (w - y))) :=
      hprodSummable.mul_left _
    have htsum := hterm1Summable.tsum_le_tsum hpoint hsummajor
    calc
      _ ≤ C ^ 2 / n *
          (∑' y : Site, hatGaussian c k y * hatGaussian c n (w - y)) := by
            simpa only [tsum_mul_left] using htsum
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left hconv (by positivity)
  have hterm2Summable : Summable (fun y : Site =>
      hatGaussian c k y * (srwKernel l w) ^ 2) := by
    simpa only [mul_comm] using hsumK.mul_left ((srwKernel l w) ^ 2)
  have hterm2 :
      ∑' y : Site, hatGaussian c k y * (srwKernel l w) ^ 2 ≤
        C ^ 2 / l * (M * hatGaussian c l w) := by
    have hmass' : (∑' y : Site, hatGaussian c k y) ≤ M := by
      simpa [M] using hmass
    calc
      _ = (srwKernel l w) ^ 2 *
          ∑' y : Site, hatGaussian c k y := by
            rw [tsum_mul_right]
            ring
      _ ≤ (C ^ 2 / l * hatGaussian c l w) *
          (∑' y : Site, hatGaussian c k y) :=
        mul_le_mul_of_nonneg_right hq2l
          (tsum_nonneg (fun y => hgnn k y))
      _ ≤ (C ^ 2 / l * hatGaussian c l w) * M :=
        mul_le_mul_of_nonneg_left hmass'
          (mul_nonneg (by positivity) (hgnn l w))
      _ = _ := by ring
  have hdiffSummable : Summable (fun y : Site => hatGaussian c k y *
      (srwKernel n (w - y) - srwKernel l w) ^ 2) := by
    apply (hterm1Summable.add hterm2Summable).mul_left 2 |>.of_nonneg_of_le
    · intro y
      exact mul_nonneg (hgnn k y) (sq_nonneg _)
    · intro y
      have hsq : (srwKernel n (w - y) - srwKernel l w) ^ 2 ≤
          2 * ((srwKernel n (w - y)) ^ 2 + (srwKernel l w) ^ 2) := by
        nlinarith [sq_nonneg (srwKernel n (w - y) + srwKernel l w)]
      calc
        _ ≤ hatGaussian c k y *
              (2 * ((srwKernel n (w - y)) ^ 2 + (srwKernel l w) ^ 2)) :=
                mul_le_mul_of_nonneg_left hsq (hgnn k y)
        _ = 2 * (hatGaussian c k y * (srwKernel n (w - y)) ^ 2 +
              hatGaussian c k y * (srwKernel l w) ^ 2) := by ring
  have hsumdiff :
      ∑' y : Site, hatGaussian c k y *
        (srwKernel n (w - y) - srwKernel l w) ^ 2 ≤
        2 * (∑' y : Site, hatGaussian c k y * (srwKernel n (w - y)) ^ 2) +
        2 * (∑' y : Site, hatGaussian c k y * (srwKernel l w) ^ 2) := by
    calc
      _ ≤ ∑' y : Site, 2 * (hatGaussian c k y * (srwKernel n (w - y)) ^ 2 +
          hatGaussian c k y * (srwKernel l w) ^ 2) := by
            apply hdiffSummable.tsum_le_tsum
            · intro y
              have hsq : (srwKernel n (w - y) - srwKernel l w) ^ 2 ≤
                  2 * ((srwKernel n (w - y)) ^ 2 + (srwKernel l w) ^ 2) := by
                nlinarith [sq_nonneg (srwKernel n (w - y) + srwKernel l w)]
              calc
                _ ≤ hatGaussian c k y *
                    (2 * ((srwKernel n (w - y)) ^ 2 + (srwKernel l w) ^ 2)) :=
                  mul_le_mul_of_nonneg_left hsq (hgnn k y)
                _ = _ := by ring
            · exact (hterm1Summable.add hterm2Summable).mul_left _
      _ = 2 * (∑' y : Site, hatGaussian c k y * (srwKernel n (w - y)) ^ 2) +
          2 * (∑' y : Site, hatGaussian c k y * (srwKernel l w) ^ 2) := by
            calc
              _ = ∑' y : Site, 2 * (hatGaussian c k y * (srwKernel n (w - y)) ^ 2 +
                    hatGaussian c k y * (srwKernel l w) ^ 2) := by rw [tsum_mul_left]
              _ = ∑' y : Site, (2 * (hatGaussian c k y * (srwKernel n (w - y)) ^ 2) +
                    2 * (hatGaussian c k y * (srwKernel l w) ^ 2)) := by
                congr 1
                funext y
                ring
              _ = (∑' y : Site, 2 * (hatGaussian c k y * (srwKernel n (w - y)) ^ 2)) +
                    (∑' y : Site, 2 * (hatGaussian c k y * (srwKernel l w) ^ 2)) :=
                Summable.tsum_add (hterm1Summable.mul_left 2) (hterm2Summable.mul_left 2)
              _ = _ := by rw [tsum_mul_left, tsum_mul_left]
  have hcoeff1 : 2 * (C ^ 2 / n) * K ≤
      6 * C ^ 2 * K * ((k : ℝ) / (l * (l - k))) := by
    have hsub : (l : ℝ) - k = (n : ℝ) := by
      change (l : ℝ) - (k : ℝ) = ((l - k : ℕ) : ℝ)
      exact (Nat.cast_sub (Nat.le_of_lt hkl)).symm
    have hnearR : (l : ℝ) ≤ 3 * (k : ℝ) := by exact_mod_cast hnear
    have hratio : (1 : ℝ) / n ≤ 3 * (k : ℝ) / ((l : ℝ) * n) := by
      rw [div_le_div_iff₀ hnR (mul_pos hlR hnR)]
      have hmul := mul_le_mul_of_nonneg_right hnearR hnR.le
      nlinarith
    have hfactor : 0 ≤ 2 * C ^ 2 * K := by positivity
    calc
      2 * (C ^ 2 / n) * K = (2 * C ^ 2 * K) * ((1 : ℝ) / n) := by ring
      _ ≤ (2 * C ^ 2 * K) * (3 * (k : ℝ) / ((l : ℝ) * n)) :=
        mul_le_mul_of_nonneg_left hratio hfactor
      _ = 6 * C ^ 2 * K * ((k : ℝ) / (l * (l - k))) := by
        rw [← hsub]
        ring
  have hcoeff2 : 2 * (C ^ 2 / l) * M ≤
      4 * C ^ 2 * M * ((k : ℝ) / (l * (l - k))) := by
    have hsub : (l : ℝ) - k = (n : ℝ) := by
      change (l : ℝ) - (k : ℝ) = ((l - k : ℕ) : ℝ)
      exact (Nat.cast_sub (Nat.le_of_lt hkl)).symm
    have hnearR : (l : ℝ) ≤ 3 * (k : ℝ) := by exact_mod_cast hnear
    have hnk : (n : ℝ) ≤ 2 * (k : ℝ) := by rw [← hsub]; nlinarith
    have hratio : (1 : ℝ) / l ≤ 2 * (k : ℝ) / ((l : ℝ) * n) := by
      rw [div_le_div_iff₀ hlR (mul_pos hlR hnR)]
      have hmul := mul_le_mul_of_nonneg_right hnk hlR.le
      nlinarith
    have hfactor : 0 ≤ 2 * C ^ 2 * M := by positivity
    calc
      2 * (C ^ 2 / l) * M = (2 * C ^ 2 * M) * ((1 : ℝ) / l) := by ring
      _ ≤ (2 * C ^ 2 * M) * (2 * (k : ℝ) / ((l : ℝ) * n)) :=
        mul_le_mul_of_nonneg_left hratio hfactor
      _ = 4 * C ^ 2 * M * ((k : ℝ) / (l * (l - k))) := by
        rw [← hsub]
        ring
  have hgL : 0 ≤ hatGaussian c l w := hgnn l w
  calc
    _ ≤ 2 * (∑' y : Site, hatGaussian c k y * (srwKernel n (w - y)) ^ 2) +
        2 * (∑' y : Site, hatGaussian c k y * (srwKernel l w) ^ 2) := hsumdiff
    _ ≤ 2 * (C ^ 2 / n * (K * hatGaussian c (k + n) w)) +
        2 * (C ^ 2 / l * (M * hatGaussian c l w)) :=
          add_le_add (mul_le_mul_of_nonneg_left hterm1 (by norm_num))
            (mul_le_mul_of_nonneg_left hterm2 (by norm_num))
    _ = (2 * (C ^ 2 / n) * K + 2 * (C ^ 2 / l) * M) *
        hatGaussian c l w := by
          have hknl : k + n = l := by dsimp [n]; omega
          rw [hknl]
          ring
    _ ≤ _ := by
      have hsumcoeff := add_le_add hcoeff1 hcoeff2
      have hmul := mul_le_mul_of_nonneg_right hsumcoeff hgL
      calc
        _ = (2 * (C ^ 2 / n) * K + 2 * (C ^ 2 / l) * M) *
            hatGaussian c l w := by
              ring
        _ ≤ (6 * C ^ 2 * K * ((k : ℝ) / (l * (l - k))) +
            4 * C ^ 2 * M * ((k : ℝ) / (l * (l - k)))) * hatGaussian c l w := hmul
        _ = _ := by ring

/-- The walk-kernel Gaussian bound and the Gaussian convolution estimate hold with a common constant uniform in time and location. The Gaussian envelopes are summable by `hatGaussian_summable` at positive times. -/
theorem hatGaussian_kernel_convolution_bounds :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, 0 < c → c ≤ c₀ → ∃ C : ℝ, 0 < C ∧
      (∀ n x, srwKernel n x ≤ C * hatGaussian c n x) ∧
      (∀ k l : ℕ, ∀ y : Site,
        ∑' x, hatGaussian c k x * hatGaussian c l (y - x) ≤
          C * hatGaussian c (k + l) y) := by
  obtain ⟨c₀, hc₀, hkernel⟩ := exists_srwKernel_le_hatGaussian
  refine ⟨c₀, hc₀, fun c hc hcc => ?_⟩
  obtain ⟨CK, hCK, hkernelC⟩ := hkernel c hc hcc
  let Cconv : ℝ := 4 * (Real.sqrt 2 + Real.sqrt (Real.pi / c)) ^ 2
  let C : ℝ := max 1 (max CK Cconv)
  have hC : 0 < C := by positivity
  have hCKC : CK ≤ C := le_trans (le_max_left CK Cconv) (le_max_right 1 _)
  have hCconv : Cconv ≤ C := le_trans (le_max_right CK Cconv) (le_max_right 1 _)
  have hCone : 1 ≤ C := le_max_left 1 _
  have hGnonneg (n : ℕ) (x : Site) : 0 ≤ hatGaussian c n x := by
    by_cases hn : n = 0
    · subst n
      by_cases hx : x = 0 <;> simp [hatGaussian, hx]
    · by_cases hp : Even ((n : ℤ) + x 0 + x 1)
      · simp [hatGaussian, hn, hp]
        positivity
      · simp [hatGaussian, hn, hp]
  refine ⟨C, hC, ?_, ?_⟩
  · intro n x
    exact (hkernelC n x).trans
      (mul_le_mul_of_nonneg_right hCKC (hGnonneg n x))
  · intro k l y
    by_cases hk : k = 0
    · subst k
      by_cases hl : l = 0
      · subst l
        by_cases hy : y = 0
        · subst y
          have hsum : (∑' x : Site,
              hatGaussian c 0 x * hatGaussian c 0 (0 - x)) = 1 := by
            simp [hatGaussian, tsum_ite_eq]
          rw [hsum]
          simp [hatGaussian]
          exact hCone
        · have hsum : (∑' x : Site,
              hatGaussian c 0 x * hatGaussian c 0 (y - x)) = 0 := by
            calc
              _ = ∑' x : Site, (0 : ℝ) := tsum_congr (fun x => by
                by_cases hx : x = 0
                · subst x
                  simp [hatGaussian, hy]
                · simp [hatGaussian, hx])
              _ = 0 := tsum_zero
          rw [hsum]
          simp [hatGaussian, hy]
      · have hsum : (∑' x : Site,
            hatGaussian c 0 x * hatGaussian c l (y - x)) = hatGaussian c l y := by
          have hdelta : hatGaussian c 0 = (fun x : Site => if x = 0 then 1 else 0) := by
            funext x
            simp [hatGaussian]
          rw [hdelta]
          simp only [ite_mul, one_mul, zero_mul, tsum_ite_eq, sub_zero]
        rw [hsum]
        simpa [Nat.zero_add] using mul_le_mul_of_nonneg_right hCone (hGnonneg l y)
    · by_cases hl : l = 0
      · subst l
        have hsum : (∑' x : Site,
            hatGaussian c k x * hatGaussian c 0 (y - x)) = hatGaussian c k y := by
          have hdelta (x : Site) : hatGaussian c 0 (y - x) = if x = y then 1 else 0 := by
            simp [hatGaussian, sub_eq_zero, eq_comm]
          simp_rw [hdelta]
          simp only [mul_ite, mul_one, mul_zero]
          rw [tsum_eq_single y]
          · simp
          · intro x hxy
            simp [hxy]
        rw [hsum]
        simpa [Nat.add_zero] using mul_le_mul_of_nonneg_right hCone (hGnonneg k y)
      · have hkpos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
        have hlpos : 1 ≤ l := Nat.one_le_iff_ne_zero.mpr hl
        have hconv := hatGaussian_convolution_le hc hkpos hlpos y
        exact hconv.trans (mul_le_mul_of_nonneg_right hCconv
          (hGnonneg (k + l) y))
