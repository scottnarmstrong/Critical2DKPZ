/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.SiteToPlane

/-! # CSZ25 profile observables -/

@[expose] public section

open scoped BigOperators InnerProductSpace

namespace Critical2DKPZ.MomentBounds

private theorem square_le_four_mul_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 ≤ 4 * Real.exp x := by
  have hxhalf : 0 ≤ x / 2 := by positivity
  have hlin := Real.add_one_le_exp (x / 2)
  have hhalfExp : x / 2 ≤ Real.exp (x / 2) := by linarith
  have hsq := mul_le_mul hhalfExp hhalfExp hxhalf (Real.exp_pos _).le
  have hexp : Real.exp (x / 2) * Real.exp (x / 2) = Real.exp x := by
    rw [← Real.exp_add]
    congr 1
    ring
  nlinarith

private theorem square_le_exp_two_mul_div_sq {t x : ℝ}
    (ht : 0 < t) (hx : 0 ≤ x) :
    x ^ 2 ≤ Real.exp (2 * t * x) / t ^ 2 := by
  have hexp := square_le_four_mul_exp_of_nonneg (x := 2 * (t * x)) (by positivity)
  rw [show 2 * (t * x) = 2 * t * x by ring] at hexp
  apply (le_div_iff₀ (sq_pos_of_pos ht)).2
  calc
    x ^ 2 * t ^ 2 = (t * x) ^ 2 := by ring
    _ ≤ Real.exp (2 * t * x) := by nlinarith [hexp]

/-- A squared distance is bounded by the diffusive exponential localization weight. -/
theorem square_le_scaled_exp_of_sqrt
    (t : ℝ) (ht : 0 < t) (L : ℕ) (hL : 0 < L) (d : ℝ) (hd : 0 ≤ d) :
    d ^ 2 ≤ ((L : ℝ) / t ^ 2) *
      Real.exp (2 * t * d / Real.sqrt (L : ℝ)) := by
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  have hroot : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.2 hLreal
  let r := d / Real.sqrt (L : ℝ)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hscalar := square_le_exp_two_mul_div_sq ht hr
  have hrateq : 2 * t * r = 2 * t * d / Real.sqrt (L : ℝ) := by
    dsimp [r]
    ring
  have hdSq : d ^ 2 = (L : ℝ) * r ^ 2 := by
    dsimp [r]
    rw [div_pow, Real.sq_sqrt hLreal.le]
    field_simp [ne_of_gt hLreal]
  calc
    d ^ 2 = (L : ℝ) * r ^ 2 := hdSq
    _ ≤ (L : ℝ) * (Real.exp (2 * t * r) / t ^ 2) :=
      mul_le_mul_of_nonneg_left hscalar hLreal.le
    _ = ((L : ℝ) / t ^ 2) * Real.exp (2 * t * d / Real.sqrt (L : ℝ)) := by
      rw [hrateq]
      ring

/-- The centre of mass is the profile-weighted sum of lattice points in the Euclidean plane. -/
noncomputable def profileMean (φ : Site → ℝ) : Plane :=
  ∑' w, φ w • Critical2DKPZ.siteToPlane w

/-- For a finitely supported profile, the centre of mass is the corresponding
finite vector sum. -/
theorem profileMean_eq_sum_of_support (φ : Site → ℝ) (A : Finset Site)
    (hφ : ∀ z ∉ A, φ z = 0) :
    profileMean φ = ∑ z ∈ A, φ z • Critical2DKPZ.siteToPlane z := by
  unfold profileMean
  apply tsum_eq_sum
  intro z hz
  simp [hφ z hz]

/-- The profile spread is the profile-weighted squared Euclidean distance from its centre of mass. -/
noncomputable def profileSpread (φ : Site → ℝ) : ℝ :=
  ∑' z, ‖Critical2DKPZ.siteToPlane z - profileMean φ‖ ^ 2 * φ z

/-- Nonnegative profiles have nonnegative mean-squared displacement. -/
theorem profileSpread_nonneg (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z) :
    0 ≤ profileSpread φ := by
  unfold profileSpread
  exact tsum_nonneg fun z =>
    mul_nonneg (pow_nonneg (norm_nonneg _) _) (hφ z)

/-- For a finitely supported profile, the spread sum reduces to that finite
support. -/
theorem profileSpread_eq_sum_of_support (φ : Site → ℝ) (A : Finset Site)
    (hφ : ∀ z ∉ A, φ z = 0) :
    profileSpread φ =
      ∑ z ∈ A, ‖Critical2DKPZ.siteToPlane z - profileMean φ‖ ^ 2 * φ z := by
  unfold profileSpread
  apply tsum_eq_sum
  intro z hz
  simp [hφ z hz]

/-- The centre of mass minimizes the weighted squared distance for a finitely supported probability profile. -/
theorem profileSpread_le_quadratic_about_of_support (φ : Site → ℝ)
    (A : Finset Site) (hφ : ∀ z ∉ A, φ z = 0)
    (hmass : ∑ z ∈ A, φ z = 1) (x : Plane) :
    profileSpread φ ≤
      ∑ z ∈ A, ‖Critical2DKPZ.siteToPlane z - x‖ ^ 2 * φ z := by
  have hmean := profileMean_eq_sum_of_support φ A hφ
  have hcross (y : Plane) :
      ∑ z ∈ A, ⟪Critical2DKPZ.siteToPlane z, y⟫_ℝ * φ z =
        ⟪profileMean φ, y⟫_ℝ := by
    rw [hmean, sum_inner]
    apply Finset.sum_congr rfl
    intro z hz
    rw [real_inner_smul_left]
    ring
  have hspread : profileSpread φ =
      (∑ z ∈ A, ‖Critical2DKPZ.siteToPlane z‖ ^ 2 * φ z) -
        ‖profileMean φ‖ ^ 2 := by
    rw [profileSpread_eq_sum_of_support φ A hφ]
    calc
      (∑ z ∈ A,
          ‖Critical2DKPZ.siteToPlane z - profileMean φ‖ ^ 2 * φ z) =
        ∑ z ∈ A,
          (‖Critical2DKPZ.siteToPlane z‖ ^ 2 * φ z -
            2 * (⟪Critical2DKPZ.siteToPlane z, profileMean φ⟫_ℝ * φ z) +
            ‖profileMean φ‖ ^ 2 * φ z) := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [norm_sub_sq_real]
          ring
      _ = (∑ z ∈ A, ‖Critical2DKPZ.siteToPlane z‖ ^ 2 * φ z) -
          2 * (∑ z ∈ A,
            ⟪Critical2DKPZ.siteToPlane z, profileMean φ⟫_ℝ * φ z) +
          (∑ z ∈ A, ‖profileMean φ‖ ^ 2 * φ z) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = (∑ z ∈ A, ‖Critical2DKPZ.siteToPlane z‖ ^ 2 * φ z) -
          2 * ⟪profileMean φ, profileMean φ⟫_ℝ + ‖profileMean φ‖ ^ 2 := by
          rw [hcross, ← Finset.mul_sum, hmass]
          norm_num
      _ = (∑ z ∈ A, ‖Critical2DKPZ.siteToPlane z‖ ^ 2 * φ z) -
          ‖profileMean φ‖ ^ 2 := by
          rw [real_inner_self_eq_norm_sq]
          ring
  have hquadratic :
      ∑ z ∈ A, ‖Critical2DKPZ.siteToPlane z - x‖ ^ 2 * φ z =
        (∑ z ∈ A, ‖Critical2DKPZ.siteToPlane z‖ ^ 2 * φ z) -
          2 * ⟪profileMean φ, x⟫_ℝ + ‖x‖ ^ 2 := by
    calc
      (∑ z ∈ A, ‖Critical2DKPZ.siteToPlane z - x‖ ^ 2 * φ z) =
        ∑ z ∈ A,
          (‖Critical2DKPZ.siteToPlane z‖ ^ 2 * φ z -
            2 * (⟪Critical2DKPZ.siteToPlane z, x⟫_ℝ * φ z) + ‖x‖ ^ 2 * φ z) := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [norm_sub_sq_real]
          ring
      _ = (∑ z ∈ A, ‖Critical2DKPZ.siteToPlane z‖ ^ 2 * φ z) -
          2 * (∑ z ∈ A,
            ⟪Critical2DKPZ.siteToPlane z, x⟫_ℝ * φ z) +
          (∑ z ∈ A, ‖x‖ ^ 2 * φ z) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = (∑ z ∈ A, ‖Critical2DKPZ.siteToPlane z‖ ^ 2 * φ z) -
          2 * ⟪profileMean φ, x⟫_ℝ + ‖x‖ ^ 2 := by
          rw [hcross, ← Finset.mul_sum, hmass]
          norm_num
  rw [hspread, hquadratic]
  have hsq : 0 ≤ ‖profileMean φ - x‖ ^ 2 := sq_nonneg _
  rw [norm_sub_sq_real] at hsq
  linarith

/-- Infinite-support form of the centre-of-mass minimization identity. The
first and second spatial moments are assumed summable explicitly. -/
theorem profileSpread_le_quadratic_about_of_summable
    (φ : Site → ℝ) (hφnonneg : ∀ z, 0 ≤ φ z)
    (hmass : HasSum φ 1)
    (hfirst : Summable (fun z => ‖Critical2DKPZ.siteToPlane z‖ * φ z))
    (hsecond : Summable (fun z => ‖Critical2DKPZ.siteToPlane z‖ ^ 2 * φ z))
    (hmean : Summable (fun z => φ z • Critical2DKPZ.siteToPlane z)) (x : Plane) :
    profileSpread φ ≤
      ∑' z, ‖Critical2DKPZ.siteToPlane z - x‖ ^ 2 * φ z := by
  let m := profileMean φ
  let firstTerm := fun z : Site => ‖Critical2DKPZ.siteToPlane z‖ ^ 2 * φ z
  let crossTerm := fun y : Plane => fun z : Site =>
    ⟪Critical2DKPZ.siteToPlane z, y⟫_ℝ * φ z
  let constantTerm := fun y : Plane => fun z : Site => ‖y‖ ^ 2 * φ z
  have hcross (y : Plane) :
      (∑' z, crossTerm y z) = ⟪m, y⟫_ℝ := by
    have hmap := (innerSL ℝ (E := Plane) y).map_tsum hmean
    calc
      (∑' z, crossTerm y z) =
          ∑' z, ⟪y, φ z • Critical2DKPZ.siteToPlane z⟫_ℝ := by
        apply tsum_congr
        intro z
        rw [real_inner_smul_right, real_inner_comm]
        ring
      _ = ⟪y, m⟫_ℝ := by
        dsimp [m, profileMean] at hmap ⊢
        exact hmap.symm
      _ = ⟪m, y⟫_ℝ := real_inner_comm _ _
  have hcrossSummable (y : Plane) : Summable (crossTerm y) := by
    have habs : Summable (fun z => |crossTerm y z|) := by
      apply Summable.of_nonneg_of_le (fun z => abs_nonneg _)
        (fun z => ?_) ((hfirst).mul_left ‖y‖)
      dsimp [crossTerm]
      rw [abs_mul, abs_of_nonneg (hφnonneg z)]
      calc
        |⟪Critical2DKPZ.siteToPlane z, y⟫_ℝ| * φ z ≤
            (‖Critical2DKPZ.siteToPlane z‖ * ‖y‖) * φ z :=
          mul_le_mul_of_nonneg_right (abs_real_inner_le_norm _ _) (hφnonneg z)
        _ = ‖y‖ * (‖Critical2DKPZ.siteToPlane z‖ * φ z) := by ring
    exact Summable.of_norm (by simpa only [Real.norm_eq_abs] using habs)
  have hconstSummable (y : Plane) : Summable (constantTerm y) :=
    (hmass.summable).mul_left (‖y‖ ^ 2)
  have hquadSummable (y : Plane) :
      Summable (fun z => firstTerm z - 2 * crossTerm y z + constantTerm y z) := by
    exact (hsecond.sub ((hcrossSummable y).mul_left 2)).add (hconstSummable y)
  have hpoint (y : Plane) (z : Site) :
      ‖Critical2DKPZ.siteToPlane z - y‖ ^ 2 * φ z =
        firstTerm z - 2 * crossTerm y z + constantTerm y z := by
    dsimp [firstTerm, crossTerm, constantTerm]
    rw [norm_sub_sq_real]
    ring
  have hdecomp (y : Plane) :
      (∑' (z : Site), ‖Critical2DKPZ.siteToPlane z - y‖ ^ 2 * φ z) =
        (∑' (z : Site), firstTerm z) - 2 * ⟪m, y⟫_ℝ + ‖y‖ ^ 2 := by
    have hBmul :
        (∑' (z : Site), 2 * crossTerm y z) = 2 * (∑' (z : Site), crossTerm y z) := tsum_mul_left
    have hCsum :
        (∑' (z : Site), constantTerm y z) = ‖y‖ ^ 2 := by
      dsimp [constantTerm]
      rw [tsum_mul_left, hmass.tsum_eq, mul_one]
    calc
      (∑' (z : Site), ‖Critical2DKPZ.siteToPlane z - y‖ ^ 2 * φ z) =
          ∑' (z : Site), (firstTerm z - 2 * crossTerm y z + constantTerm y z) := by
        apply tsum_congr
        intro z
        exact hpoint y z
      _ = (∑' (z : Site), firstTerm z) - 2 * (∑' (z : Site), crossTerm y z) +
            ∑' (z : Site), constantTerm y z := by
        rw [Summable.tsum_add (hsecond.sub ((hcrossSummable y).mul_left 2))
          (hconstSummable y), Summable.tsum_sub hsecond ((hcrossSummable y).mul_left 2), hBmul]
      _ = (∑' z, firstTerm z) - 2 * ⟪m, y⟫_ℝ + ‖y‖ ^ 2 := by
        rw [hcross y, hCsum]
  have hspread : profileSpread φ =
      (∑' (z : Site), firstTerm z) - ‖m‖ ^ 2 := by
    dsimp [profileSpread]
    rw [hdecomp m, real_inner_self_eq_norm_sq]
    ring
  have hquad := hdecomp x
  rw [hspread, hquad]
  have hsq : 0 ≤ ‖m - x‖ ^ 2 := sq_nonneg _
  rw [norm_sub_sq_real] at hsq
  linarith

/-- Exponential localization controls the mean-squared displacement of a
finitely supported probability profile. The constant is explicit. -/
theorem profileSpread_le_of_exponential_localization_finiteSupport
    (t : ℝ) (ht : 0 < t) (L : ℕ) (hL : 0 < L)
    (φ : Site → ℝ) (A : Finset Site) (hφ : ∀ z ∉ A, φ z = 0)
    (hφnonneg : ∀ z, 0 ≤ φ z) (hmass : ∑ z ∈ A, φ z = 1)
    (x₀ : Plane) (c₁ : ℝ)
    (hlocal :
      ∑ z ∈ A, φ z * Real.exp
        (2 * t * ‖Critical2DKPZ.siteToPlane z - x₀‖ / Real.sqrt (L : ℝ)) ≤ c₁) :
    profileSpread φ ≤ ((L : ℝ) / t ^ 2) * c₁ := by
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  have hroot : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.2 hLreal
  have hcenter := profileSpread_le_quadratic_about_of_support
    φ A hφ hmass x₀
  have hterm (z : Site) :
      ‖Critical2DKPZ.siteToPlane z - x₀‖ ^ 2 ≤
        ((L : ℝ) / t ^ 2) * Real.exp
          (2 * t * ‖Critical2DKPZ.siteToPlane z - x₀‖ / Real.sqrt (L : ℝ)) := by
    exact square_le_scaled_exp_of_sqrt t ht L hL _ (norm_nonneg _)
  have hsum :
      (∑ z ∈ A, ‖Critical2DKPZ.siteToPlane z - x₀‖ ^ 2 * φ z) ≤
        ((L : ℝ) / t ^ 2) *
          ∑ z ∈ A, φ z * Real.exp
            (2 * t * ‖Critical2DKPZ.siteToPlane z - x₀‖ / Real.sqrt (L : ℝ)) := by
    calc
      (∑ z ∈ A, ‖Critical2DKPZ.siteToPlane z - x₀‖ ^ 2 * φ z) ≤
          ∑ z ∈ A,
            (((L : ℝ) / t ^ 2) * Real.exp
              (2 * t * ‖Critical2DKPZ.siteToPlane z - x₀‖ / Real.sqrt (L : ℝ))) * φ z :=
        Finset.sum_le_sum fun z hz => mul_le_mul_of_nonneg_right (hterm z) (hφnonneg z)
      _ = ((L : ℝ) / t ^ 2) *
          ∑ z ∈ A, φ z * Real.exp
            (2 * t * ‖Critical2DKPZ.siteToPlane z - x₀‖ / Real.sqrt (L : ℝ)) := by
        calc
          _ = ∑ z ∈ A, ((L : ℝ) / t ^ 2) *
              (φ z * Real.exp
                (2 * t * ‖Critical2DKPZ.siteToPlane z - x₀‖ / Real.sqrt (L : ℝ))) := by
            apply Finset.sum_congr rfl
            intro z hz
            ring
          _ = _ := by rw [Finset.mul_sum]
  have hcoef : 0 ≤ (L : ℝ) / t ^ 2 := div_nonneg hLreal.le (sq_nonneg _)
  calc
    profileSpread φ ≤
        ∑ z ∈ A, ‖Critical2DKPZ.siteToPlane z - x₀‖ ^ 2 * φ z := hcenter
    _ ≤ ((L : ℝ) / t ^ 2) *
        ∑ z ∈ A, φ z * Real.exp
          (2 * t * ‖Critical2DKPZ.siteToPlane z - x₀‖ / Real.sqrt (L : ℝ)) := hsum
    _ ≤ ((L : ℝ) / t ^ 2) * c₁ := mul_le_mul_of_nonneg_left hlocal hcoef

/-- Exponential localization bounds the quadratic spread of a probability profile by an explicit multiple of the horizon. -/
theorem profileSpread_le_of_exponential_localization
    (φ : Site → ℝ) (hφnonneg : ∀ z, 0 ≤ φ z) (hmass : HasSum φ 1)
    (t : ℝ) (ht : 0 < t) (L : ℕ) (hL : 0 < L)
    (x₀ : Plane) (c₁ : ℝ)
    (hlocalSummable : Summable (fun z => φ z * Real.exp
      (2 * t * ‖Critical2DKPZ.siteToPlane z - x₀‖ / Real.sqrt (L : ℝ))))
    (hlocalBound : (∑' z, φ z * Real.exp
      (2 * t * ‖Critical2DKPZ.siteToPlane z - x₀‖ / Real.sqrt (L : ℝ))) ≤ c₁) :
    profileSpread φ ≤ ((L : ℝ) / t ^ 2) * c₁ := by
  let d := fun z : Site => ‖Critical2DKPZ.siteToPlane z - x₀‖
  let localWeight := fun z : Site => φ z * Real.exp
    (2 * t * d z / Real.sqrt (L : ℝ))
  let quadAtCenter := fun z : Site => d z ^ 2 * φ z
  have hLreal : 0 < (L : ℝ) := by exact_mod_cast hL
  have hcoef : 0 ≤ (L : ℝ) / t ^ 2 := div_nonneg hLreal.le (sq_nonneg _)
  have hφsum : Summable φ := hmass.summable
  have hquadAtCenter : Summable quadAtCenter := by
    apply Summable.of_nonneg_of_le
      (fun z => mul_nonneg (sq_nonneg _) (hφnonneg z))
      (fun z => ?_)
      (hlocalSummable.mul_left ((L : ℝ) / t ^ 2))
    have hterm := square_le_scaled_exp_of_sqrt t ht L hL (d z) (norm_nonneg _)
    dsimp [quadAtCenter, localWeight, d]
    calc
      ‖Critical2DKPZ.siteToPlane z - x₀‖ ^ 2 * φ z ≤
          (((L : ℝ) / t ^ 2) * Real.exp
            (2 * t * ‖Critical2DKPZ.siteToPlane z - x₀‖ / Real.sqrt (L : ℝ))) * φ z :=
        mul_le_mul_of_nonneg_right hterm (hφnonneg z)
      _ = ((L : ℝ) / t ^ 2) *
          (φ z * Real.exp
            (2 * t * ‖Critical2DKPZ.siteToPlane z - x₀‖ / Real.sqrt (L : ℝ))) := by ring
  have hfirstAtCenter : Summable (fun z => d z * φ z) := by
    apply Summable.of_nonneg_of_le
      (fun z => mul_nonneg (norm_nonneg _) (hφnonneg z))
      (fun z => ?_)
      (hφsum.add hquadAtCenter)
    have hd := norm_nonneg (Critical2DKPZ.siteToPlane z - x₀)
    have hineq : d z ≤ 1 + d z ^ 2 := by
      dsimp [d]
      nlinarith [sq_nonneg (‖Critical2DKPZ.siteToPlane z - x₀‖ - 1 / 2)]
    dsimp [d, quadAtCenter]
    calc
      d z * φ z ≤ (1 + d z ^ 2) * φ z :=
        mul_le_mul_of_nonneg_right hineq (hφnonneg z)
      _ = φ z + d z ^ 2 * φ z := by ring
  have hfirst : Summable (fun z => ‖Critical2DKPZ.siteToPlane z‖ * φ z) := by
    apply Summable.of_nonneg_of_le
      (fun z => mul_nonneg (norm_nonneg _) (hφnonneg z))
      (fun z => ?_)
      (hfirstAtCenter.add (hφsum.mul_left ‖x₀‖))
    have hz : ‖Critical2DKPZ.siteToPlane z‖ ≤ d z + ‖x₀‖ := by
      dsimp [d]
      calc
        ‖Critical2DKPZ.siteToPlane z‖ =
            ‖(Critical2DKPZ.siteToPlane z - x₀) + x₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖Critical2DKPZ.siteToPlane z - x₀‖ + ‖x₀‖ := norm_add_le _ _
    calc
      ‖Critical2DKPZ.siteToPlane z‖ * φ z ≤ (d z + ‖x₀‖) * φ z :=
        mul_le_mul_of_nonneg_right hz (hφnonneg z)
      _ = d z * φ z + ‖x₀‖ * φ z := by ring
  have hsecond : Summable (fun z => ‖Critical2DKPZ.siteToPlane z‖ ^ 2 * φ z) := by
    apply Summable.of_nonneg_of_le
      (fun z => mul_nonneg (sq_nonneg _) (hφnonneg z))
      (fun z => ?_)
      ((hquadAtCenter.add (hφsum.mul_left (‖x₀‖ ^ 2))).mul_left 2)
    have hz : ‖Critical2DKPZ.siteToPlane z‖ ≤ d z + ‖x₀‖ := by
      dsimp [d]
      calc
        ‖Critical2DKPZ.siteToPlane z‖ =
            ‖(Critical2DKPZ.siteToPlane z - x₀) + x₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖Critical2DKPZ.siteToPlane z - x₀‖ + ‖x₀‖ := norm_add_le _ _
    have hsq : ‖Critical2DKPZ.siteToPlane z‖ ^ 2 ≤
        2 * (d z ^ 2 + ‖x₀‖ ^ 2) := by
      have hdK := sq_nonneg (d z - ‖x₀‖)
      have hsumNonneg : 0 ≤ d z + ‖x₀‖ := by positivity
      have hmul := mul_le_mul hz hz (norm_nonneg _) hsumNonneg
      nlinarith
    calc
      ‖Critical2DKPZ.siteToPlane z‖ ^ 2 * φ z ≤
          (2 * (d z ^ 2 + ‖x₀‖ ^ 2)) * φ z :=
        mul_le_mul_of_nonneg_right hsq (hφnonneg z)
      _ = 2 * (d z ^ 2 * φ z + ‖x₀‖ ^ 2 * φ z) := by ring
  have hmean : Summable (fun z => φ z • Critical2DKPZ.siteToPlane z) := by
    have hnorm :
        (fun z => ‖φ z • Critical2DKPZ.siteToPlane z‖) =
          (fun z => ‖Critical2DKPZ.siteToPlane z‖ * φ z) := by
      funext z
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hφnonneg z)]
      ring
    exact Summable.of_norm (hnorm ▸ hfirst)
  have hcenter := profileSpread_le_quadratic_about_of_summable
    φ hφnonneg hmass hfirst hsecond hmean x₀
  have hlocalBound' : (∑' z, localWeight z) ≤ c₁ := by
    simpa [localWeight, d] using hlocalBound
  have hpointwise (z : Site) : quadAtCenter z ≤
      ((L : ℝ) / t ^ 2) * localWeight z := by
    have hterm := square_le_scaled_exp_of_sqrt t ht L hL (d z) (norm_nonneg _)
    change d z ^ 2 * φ z ≤
      ((L : ℝ) / t ^ 2) *
        (φ z * Real.exp (2 * t * d z / Real.sqrt (L : ℝ)))
    calc
      d z ^ 2 * φ z ≤
          (((L : ℝ) / t ^ 2) * Real.exp
            (2 * t * d z / Real.sqrt (L : ℝ))) * φ z :=
        mul_le_mul_of_nonneg_right hterm (hφnonneg z)
      _ = ((L : ℝ) / t ^ 2) *
          (φ z * Real.exp (2 * t * d z / Real.sqrt (L : ℝ))) := by ring
  have hquadBound₀ :
      (∑' z, quadAtCenter z) ≤ ∑' z, ((L : ℝ) / t ^ 2) * localWeight z :=
    hquadAtCenter.tsum_le_tsum hpointwise
      (hlocalSummable.mul_left ((L : ℝ) / t ^ 2))
  have hquadBound₁ :
      (∑' z, ((L : ℝ) / t ^ 2) * localWeight z) =
        ((L : ℝ) / t ^ 2) * ∑' z, localWeight z := tsum_mul_left
  have hquadBound :
      (∑' z, d z ^ 2 * φ z) ≤
        ((L : ℝ) / t ^ 2) * c₁ := by
    calc
      (∑' z, d z ^ 2 * φ z) = ∑' z, quadAtCenter z := by rfl
      _ ≤ ∑' z, ((L : ℝ) / t ^ 2) * localWeight z := hquadBound₀
      _ = ((L : ℝ) / t ^ 2) * ∑' z, localWeight z := hquadBound₁
      _ ≤ ((L : ℝ) / t ^ 2) * c₁ :=
        mul_le_mul_of_nonneg_left hlocalBound' hcoef
  calc
    profileSpread φ ≤ ∑' z, ‖Critical2DKPZ.siteToPlane z - x₀‖ ^ 2 * φ z := hcenter
    _ = ∑' z, d z ^ 2 * φ z := by rfl
    _ ≤ ((L : ℝ) / t ^ 2) * c₁ := hquadBound

end Critical2DKPZ.MomentBounds

end
