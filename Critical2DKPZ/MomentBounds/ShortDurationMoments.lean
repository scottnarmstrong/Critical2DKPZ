/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.SmoothedCovariance
public import Critical2DKPZ.MomentBounds.CCR25GaussianMoments
public import Critical2DKPZ.RandomWalk.KernelBridge
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Mul

/-! # Finite-horizon Gaussian path moments -/

@[expose] public section

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- Integer moments of a single normalized Gaussian path weight. -/
theorem integral_pathWeight_pow {n : ℕ} (β : ℝ) (a : ℕ) (w : Site)
    (s : Fin n → Fin 4) (k : ℕ) :
    ∫ ω : Disorder, Critical2DKPZ.Polymer.pathWeight β a w s ω ^ k
        ∂disorderLaw =
      Real.exp (((k : ℝ) ^ 2 - k) * n * β ^ 2 / 2) := by
  let e := Critical2DKPZ.Polymer.pathIndex a w s
  let d : ℝ := -(∑ _j : Finset.Icc 1 n, β ^ 2 / 2)
  have hpoint (ω : Disorder) :
      Critical2DKPZ.Polymer.pathWeight β a w s ω ^ k =
        Critical2DKPZ.Polymer.finiteExp e (fun _ => (k : ℝ) * β) ((k : ℝ) * d) ω := by
    rw [Critical2DKPZ.Polymer.pathWeight_eq_finiteExp]
    simp only [Critical2DKPZ.Polymer.finiteExp]
    rw [← Real.exp_nat_mul]
    congr 1
    simp only [e]
    rw [mul_add, Finset.mul_sum]
    simp only [d, mul_neg]
    rw [Finset.mul_sum]
    ring_nf
  rw [show (fun ω : Disorder =>
      Critical2DKPZ.Polymer.pathWeight β a w s ω ^ k) =
        fun ω => Critical2DKPZ.Polymer.finiteExp e
          (fun _ => (k : ℝ) * β) ((k : ℝ) * d) ω from funext hpoint]
  rw [Critical2DKPZ.Polymer.integral_finiteExp e
    (Critical2DKPZ.Polymer.pathIndex_injective a w s)]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.Icc 1 n).card = n := by
    simp
  have hsum :
      (∑ x ∈ (Finset.Icc 1 n).attach, β ^ 2 / 2) =
        (n : ℝ) * β ^ 2 / 2 := by
    rw [Finset.sum_const]
    simp only [nsmul_eq_mul, Finset.card_attach]
    rw [hcard]
    ring
  dsimp [d]
  rw [hsum, Finset.card_attach, hcard]
  ring_nf

/-- The fourth centered moment of a normalized path weight is an explicit
function of its duration and the Gaussian variance parameter. -/
theorem integral_abs_pathWeight_sub_one_pow_four {n : ℕ}
    (β : ℝ) (a : ℕ) (w : Site) (s : Fin n → Fin 4) :
    ∫ ω : Disorder,
        |Critical2DKPZ.Polymer.pathWeight β a w s ω - 1| ^ 4 ∂disorderLaw =
      Real.exp (6 * (n : ℝ) * β ^ 2) -
        4 * Real.exp (3 * (n : ℝ) * β ^ 2) +
        6 * Real.exp ((n : ℝ) * β ^ 2) - 3 := by
  let W : Disorder → ℝ := Critical2DKPZ.Polymer.pathWeight β a w s
  have hpow (j : ℕ) : Integrable (fun ω : Disorder => W ω ^ j) disorderLaw := by
    have h := (Critical2DKPZ.Polymer.memLp_pathWeight β a w s
      (j : ℝ≥0∞) (by simp)).integrable_norm_pow'
    simpa only [W, Real.norm_eq_abs,
      abs_of_pos (Critical2DKPZ.Polymer.pathWeight_pos β a w s _)] using h
  have hleft : Integrable (fun ω : Disorder => W ω ^ 4 - 4 * W ω ^ 3) disorderLaw :=
    (hpow 4).sub ((hpow 3).const_mul 4)
  have hrightBase : Integrable
      (fun ω : Disorder => 6 * W ω ^ 2 - 4 * W ω) disorderLaw := by
    have h := ((hpow 2).const_mul 6).sub ((hpow 1).const_mul 4)
    refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply, pow_one]
  have hWint : Integrable (fun ω : Disorder => 4 * W ω) disorderLaw := by
    simpa only [pow_one] using (hpow 1).const_mul 4
  have hmean : ∫ ω : Disorder, W ω ∂disorderLaw = 1 := by
    simpa only [W] using Critical2DKPZ.Polymer.integral_pathWeight β a w s
  have hright : Integrable (fun ω : Disorder =>
      6 * W ω ^ 2 - 4 * W ω + 1) disorderLaw := by
    have h := hrightBase.add (integrable_const 1)
    refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
    rfl
  have hpoint (ω : Disorder) : |W ω - 1| ^ 4 =
      (W ω ^ 4 - 4 * W ω ^ 3) + (6 * W ω ^ 2 - 4 * W ω + 1) := by
    calc
      |W ω - 1| ^ 4 = |(W ω - 1) ^ 4| := pow_abs _ _
      _ = (W ω - 1) ^ 4 := abs_of_nonneg
        ((show Even 4 by norm_num).pow_nonneg (W ω - 1))
      _ = _ := by ring
  calc
    _ = ∫ ω : Disorder,
        (W ω ^ 4 - 4 * W ω ^ 3) + (6 * W ω ^ 2 - 4 * W ω + 1) ∂disorderLaw := by
      congr 1
      funext ω
      exact hpoint ω
    _ = (∫ ω : Disorder, W ω ^ 4 - 4 * W ω ^ 3 ∂disorderLaw) +
        ∫ ω : Disorder, 6 * W ω ^ 2 - 4 * W ω + 1 ∂disorderLaw :=
      integral_add hleft hright
    _ = _ := by
      rw [integral_sub (hpow 4) ((hpow 3).const_mul 4),
        integral_add hrightBase (integrable_const 1),
        show (fun ω : Disorder => 6 * W ω ^ 2 - 4 * W ω) =
          (fun ω => 6 * W ω ^ 2) - (fun ω => 4 * W ω) from
            funext (fun _ => rfl),
        integral_sub' ((hpow 2).const_mul 6) hWint,
        integral_const_mul, integral_const_mul, integral_const_mul, integral_const]
      rw [integral_pathWeight_pow β a w s 4,
        integral_pathWeight_pow β a w s 3,
        integral_pathWeight_pow β a w s 2, hmean]
      norm_num
      ring_nf

/-- On the unit interval, the exponential has a quadratic upper remainder. -/
theorem exp_le_one_add_self_add_sq_of_unit_interval {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have hnorm : ‖x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0]
    exact hx1
  have hTaylor := Real.norm_exp_sub_one_sub_id_le hnorm
  have hrem0 : 0 ≤ Real.exp x - 1 - x := by
    nlinarith [Real.quadratic_le_exp_of_nonneg hx0]
  have hrem : Real.exp x - 1 - x ≤ x ^ 2 := by
    have habs : |Real.exp x - 1 - x| ≤ x ^ 2 := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hx0] using hTaylor
    rw [abs_of_nonneg hrem0] at habs
    exact habs
  linarith

/-- The fourth centered moment of a lognormal variable with variance parameter
`u` is bounded by `42 u²` when `6u ≤ 1`. -/
theorem exp_centered_fourth_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : 6 * u ≤ 1) :
    Real.exp (6 * u) - 4 * Real.exp (3 * u) +
      6 * Real.exp u - 3 ≤ 42 * u ^ 2 := by
  have h6 := exp_le_one_add_self_add_sq_of_unit_interval
    (mul_nonneg (by norm_num) hu0) hu1
  have h1 := exp_le_one_add_self_add_sq_of_unit_interval hu0 (by linarith)
  have h3 : 1 + 3 * u ≤ Real.exp (3 * u) := by
    linarith [Real.add_one_le_exp (3 * u)]
  linarith

/-- Uniform `O(β⁴)` centered fourth-moment bound for one path on a short
Gaussian horizon. -/
theorem integral_abs_pathWeight_sub_one_pow_four_le {n : ℕ}
    (β : ℝ) (a : ℕ) (w : Site) (s : Fin n → Fin 4)
    (hsmall : 6 * (n : ℝ) * β ^ 2 ≤ 1) :
    ∫ ω : Disorder,
        |Critical2DKPZ.Polymer.pathWeight β a w s ω - 1| ^ 4 ∂disorderLaw ≤
      42 * ((n : ℝ) * β ^ 2) ^ 2 := by
  rw [integral_abs_pathWeight_sub_one_pow_four]
  have hu0 : 0 ≤ (n : ℝ) * β ^ 2 := by positivity
  have hsmall' : 6 * ((n : ℝ) * β ^ 2) ≤ 1 := by
    calc
      6 * ((n : ℝ) * β ^ 2) = 6 * (n : ℝ) * β ^ 2 := by ring
      _ ≤ 1 := hsmall
  simpa only [mul_assoc] using exp_centered_fourth_le hu0 hsmall'

/-- For real variables, the fourth absolute power is the ordinary fourth
power. -/
theorem abs_pow_four_eq (x : ℝ) : |x| ^ 4 = x ^ 4 := by
  calc
    |x| ^ 4 = |x ^ 4| := pow_abs x 4
    _ = x ^ 4 := abs_of_nonneg ((show Even 4 by norm_num).pow_nonneg x)

/-- Jensen's inequality transfers the one-path estimate to the finite path
average defining a point-to-plane partition function. -/
theorem integral_abs_pointToPlane_sub_one_pow_four_le {k : ℕ}
    (β : ℝ) (a : ℕ) (w : Site)
    (hsmall : 6 * (k : ℝ) * β ^ 2 ≤ 1) :
    ∫ ω : Disorder,
        |Critical2DKPZ.pointToPlane β a k w ω - 1| ^ 4 ∂disorderLaw ≤
      42 * ((k : ℝ) * β ^ 2) ^ 2 := by
  let weight : ℝ := (4 : ℝ)⁻¹ ^ k
  have hweight : ∑ s : Fin k → Fin 4, weight = 1 := by
    simpa only [weight] using Critical2DKPZ.Polymer.sum_walkProbability k
  have hcenter (ω : Disorder) :
      Critical2DKPZ.pointToPlane β a k w ω - 1 =
        ∑ s : Fin k → Fin 4,
          weight * (Critical2DKPZ.Polymer.pathWeight β a w s ω - 1) := by
    rw [Critical2DKPZ.Polymer.pointToPlane_eq_sum]
    calc
      (∑ s : Fin k → Fin 4,
          (4 : ℝ)⁻¹ ^ k * Critical2DKPZ.Polymer.pathWeight β a w s ω) - 1 =
        (∑ s : Fin k → Fin 4,
          (4 : ℝ)⁻¹ ^ k * Critical2DKPZ.Polymer.pathWeight β a w s ω) -
          ∑ s : Fin k → Fin 4, (4 : ℝ)⁻¹ ^ k := by
            rw [Critical2DKPZ.Polymer.sum_walkProbability]
      _ = ∑ s : Fin k → Fin 4,
          ((4 : ℝ)⁻¹ ^ k * Critical2DKPZ.Polymer.pathWeight β a w s ω -
            (4 : ℝ)⁻¹ ^ k) := by rw [← Finset.sum_sub_distrib]
      _ = ∑ s : Fin k → Fin 4,
          weight * (Critical2DKPZ.Polymer.pathWeight β a w s ω - 1) := by
            apply Finset.sum_congr rfl
            intro s hs
            simp only [weight]
            ring
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 4) :=
    (even_two_mul 2 : Even 4).convexOn_pow
  have hcenterFourth (ω : Disorder) :
      (Critical2DKPZ.pointToPlane β a k w ω - 1) ^ 4 ≤
        ∑ s : Fin k → Fin 4, weight *
          (Critical2DKPZ.Polymer.pathWeight β a w s ω - 1) ^ 4 := by
    have hj := hconv.map_sum_le
      (t := Finset.univ) (w := fun _ : Fin k → Fin 4 => weight)
      (p := fun s => Critical2DKPZ.Polymer.pathWeight β a w s ω - 1)
      (fun _ _ => by positivity) hweight (fun _ _ => Set.mem_univ _)
    calc
      (Critical2DKPZ.pointToPlane β a k w ω - 1) ^ 4 =
          (∑ s : Fin k → Fin 4,
            weight * (Critical2DKPZ.Polymer.pathWeight β a w s ω - 1)) ^ 4 := by
        rw [hcenter ω]
      _ ≤ _ := by simpa only [smul_eq_mul] using hj
  have hpointwise (ω : Disorder) :
      |Critical2DKPZ.pointToPlane β a k w ω - 1| ^ 4 ≤
        ∑ s : Fin k → Fin 4, weight *
          |Critical2DKPZ.Polymer.pathWeight β a w s ω - 1| ^ 4 := by
    calc
      _ = (Critical2DKPZ.pointToPlane β a k w ω - 1) ^ 4 := by
        exact abs_pow_four_eq _
      _ ≤ _ := hcenterFourth ω
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [abs_pow_four_eq]
  have hpathInt (s : Fin k → Fin 4) :
      Integrable (fun ω : Disorder =>
        |Critical2DKPZ.Polymer.pathWeight β a w s ω - 1| ^ 4) disorderLaw := by
    have hm : MemLp (fun ω : Disorder =>
        Critical2DKPZ.Polymer.pathWeight β a w s ω - 1) (4 : ℝ≥0∞) disorderLaw :=
      (Critical2DKPZ.Polymer.memLp_pathWeight β a w s 4 (by simp)).sub
        (memLp_const 1)
    have hi := hm.integrable_norm_pow'
    simpa only [Real.norm_eq_abs] using hi
  have hleftInt : Integrable (fun ω : Disorder =>
      |Critical2DKPZ.pointToPlane β a k w ω - 1| ^ 4) disorderLaw := by
    have hm : MemLp (fun ω : Disorder =>
        Critical2DKPZ.pointToPlane β a k w ω - 1) (4 : ℝ≥0∞) disorderLaw :=
      (Critical2DKPZ.Polymer.memLp_pointToPlane β a k w 4 (by simp)).sub
        (memLp_const 1)
    have hi := hm.integrable_norm_pow'
    simpa only [Real.norm_eq_abs] using hi
  have hrightInt : Integrable (fun ω : Disorder =>
      ∑ s : Fin k → Fin 4, weight *
        |Critical2DKPZ.Polymer.pathWeight β a w s ω - 1| ^ 4) disorderLaw :=
    integrable_finsetSum _ fun s _ => (hpathInt s).const_mul weight
  have hsumInt :
      (∫ ω : Disorder,
        ∑ s : Fin k → Fin 4, weight *
          |Critical2DKPZ.Polymer.pathWeight β a w s ω - 1| ^ 4 ∂disorderLaw) =
        ∑ s : Fin k → Fin 4, weight *
          ∫ ω : Disorder,
            |Critical2DKPZ.Polymer.pathWeight β a w s ω - 1| ^ 4 ∂disorderLaw := by
    rw [integral_finsetSum _ fun s _ => (hpathInt s).const_mul weight]
    simp only [integral_const_mul]
  calc
    _ ≤ ∫ ω : Disorder,
        ∑ s : Fin k → Fin 4, weight *
          |Critical2DKPZ.Polymer.pathWeight β a w s ω - 1| ^ 4 ∂disorderLaw :=
      integral_mono_ae hleftInt hrightInt (Filter.Eventually.of_forall hpointwise)
    _ = _ := hsumInt
    _ ≤ ∑ s : Fin k → Fin 4, weight * (42 * ((k : ℝ) * β ^ 2) ^ 2) := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left
        (integral_abs_pathWeight_sub_one_pow_four_le β a w s hsmall)
        (by positivity)
    _ = 42 * ((k : ℝ) * β ^ 2) ^ 2 := by
      rw [← Finset.sum_mul, hweight]
      ring

/-- The heat-smoothed starting profile is a finite probability mixture of
point-to-plane partition functions, so the same short-horizon bound holds. -/
theorem integral_abs_smoothedP2Plane_sub_one_pow_four_le {s n : ℕ}
    (β : ℝ) (x : Site)
    (hsmall : 6 * ((n - s : ℕ) : ℝ) * β ^ 2 ≤ 1) :
    ∫ ω : Disorder,
        |Critical2DKPZ.smoothedP2Plane β s n x ω - 1| ^ 4 ∂disorderLaw ≤
      42 * ((n - s : ℕ) * β ^ 2) ^ 2 := by
  let k : ℕ := n - s
  have hweight (y : Site) : 0 ≤ Critical2DKPZ.srwKernel s (y - x) :=
    Critical2DKPZ.Polymer.kernel_nonneg s (y - x)
  have hmass :
      (∑ y ∈ Critical2DKPZ.Polymer.endpoints x s,
        Critical2DKPZ.srwKernel s (y - x)) = 1 :=
    Critical2DKPZ.Polymer.sum_srwKernel_endpoints s x
  have hcenter (ω : Disorder) :
      Critical2DKPZ.smoothedP2Plane β s n x ω - 1 =
        ∑ y ∈ Critical2DKPZ.Polymer.endpoints x s,
          Critical2DKPZ.srwKernel s (y - x) *
            (Critical2DKPZ.pointToPlane β s k y ω - 1) := by
    rw [Critical2DKPZ.Polymer.smoothedP2Plane_eq_sum]
    calc
      (∑ y ∈ Critical2DKPZ.Polymer.endpoints x s,
          Critical2DKPZ.srwKernel s (y - x) *
            Critical2DKPZ.pointToPlane β s k y ω) - 1 =
        (∑ y ∈ Critical2DKPZ.Polymer.endpoints x s,
          Critical2DKPZ.srwKernel s (y - x) *
            Critical2DKPZ.pointToPlane β s k y ω) -
          ∑ y ∈ Critical2DKPZ.Polymer.endpoints x s,
            Critical2DKPZ.srwKernel s (y - x) := by rw [hmass]
      _ = ∑ y ∈ Critical2DKPZ.Polymer.endpoints x s,
          (Critical2DKPZ.srwKernel s (y - x) *
            Critical2DKPZ.pointToPlane β s k y ω -
            Critical2DKPZ.srwKernel s (y - x)) := by
          rw [← Finset.sum_sub_distrib]
      _ = _ := by
          apply Finset.sum_congr rfl
          intro y hy
          ring
  have hconv : ConvexOn ℝ Set.univ (fun z : ℝ => z ^ 4) :=
    (even_two_mul 2 : Even 4).convexOn_pow
  have hcenterFourth (ω : Disorder) :
      (Critical2DKPZ.smoothedP2Plane β s n x ω - 1) ^ 4 ≤
        ∑ y ∈ Critical2DKPZ.Polymer.endpoints x s,
          Critical2DKPZ.srwKernel s (y - x) *
            (Critical2DKPZ.pointToPlane β s k y ω - 1) ^ 4 := by
    have hj := hconv.map_sum_le
      (t := Critical2DKPZ.Polymer.endpoints x s)
      (w := fun y => Critical2DKPZ.srwKernel s (y - x))
      (p := fun y => Critical2DKPZ.pointToPlane β s k y ω - 1)
      (fun y hy => hweight y)
      hmass
      (fun _ _ => Set.mem_univ _)
    calc
      _ = (∑ y ∈ Critical2DKPZ.Polymer.endpoints x s,
          Critical2DKPZ.srwKernel s (y - x) *
            (Critical2DKPZ.pointToPlane β s k y ω - 1)) ^ 4 := by
          rw [hcenter ω]
      _ ≤ _ := by simpa only [smul_eq_mul] using hj
  have hpointwise (ω : Disorder) :
      |Critical2DKPZ.smoothedP2Plane β s n x ω - 1| ^ 4 ≤
        ∑ y ∈ Critical2DKPZ.Polymer.endpoints x s,
          Critical2DKPZ.srwKernel s (y - x) *
            |Critical2DKPZ.pointToPlane β s k y ω - 1| ^ 4 := by
    calc
      _ = (Critical2DKPZ.smoothedP2Plane β s n x ω - 1) ^ 4 :=
        abs_pow_four_eq _
      _ ≤ _ := hcenterFourth ω
      _ = _ := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [abs_pow_four_eq]
  have hplaneInt (y : Site) :
      Integrable (fun ω : Disorder =>
        |Critical2DKPZ.pointToPlane β s k y ω - 1| ^ 4) disorderLaw := by
    have hm : MemLp (fun ω : Disorder =>
        Critical2DKPZ.pointToPlane β s k y ω - 1) (4 : ℝ≥0∞) disorderLaw :=
      (Critical2DKPZ.Polymer.memLp_pointToPlane β s k y 4 (by simp)).sub
        (memLp_const 1)
    have hi := hm.integrable_norm_pow'
    simpa only [Real.norm_eq_abs] using hi
  have hleftInt : Integrable (fun ω : Disorder =>
      |Critical2DKPZ.smoothedP2Plane β s n x ω - 1| ^ 4) disorderLaw := by
    have hm : MemLp (fun ω : Disorder =>
        Critical2DKPZ.smoothedP2Plane β s n x ω - 1) (4 : ℝ≥0∞) disorderLaw :=
      (Critical2DKPZ.Polymer.memLp_smoothedP2Plane β s n x 4 (by simp)).sub
        (memLp_const 1)
    have hi := hm.integrable_norm_pow'
    simpa only [Real.norm_eq_abs] using hi
  have hrightInt : Integrable (fun ω : Disorder =>
      ∑ y ∈ Critical2DKPZ.Polymer.endpoints x s,
        Critical2DKPZ.srwKernel s (y - x) *
          |Critical2DKPZ.pointToPlane β s k y ω - 1| ^ 4) disorderLaw :=
    integrable_finsetSum _ fun y _ =>
      (hplaneInt y).const_mul (Critical2DKPZ.srwKernel s (y - x))
  have hsumInt :
      (∫ ω : Disorder,
        ∑ y ∈ Critical2DKPZ.Polymer.endpoints x s,
          Critical2DKPZ.srwKernel s (y - x) *
            |Critical2DKPZ.pointToPlane β s k y ω - 1| ^ 4 ∂disorderLaw) =
        ∑ y ∈ Critical2DKPZ.Polymer.endpoints x s,
          Critical2DKPZ.srwKernel s (y - x) *
            ∫ ω : Disorder,
              |Critical2DKPZ.pointToPlane β s k y ω - 1| ^ 4 ∂disorderLaw := by
    rw [integral_finsetSum _ fun y _ =>
      (hplaneInt y).const_mul (Critical2DKPZ.srwKernel s (y - x))]
    simp only [integral_const_mul]
  calc
    _ ≤ ∫ ω : Disorder,
        ∑ y ∈ Critical2DKPZ.Polymer.endpoints x s,
          Critical2DKPZ.srwKernel s (y - x) *
            |Critical2DKPZ.pointToPlane β s k y ω - 1| ^ 4 ∂disorderLaw :=
      integral_mono_ae hleftInt hrightInt (Filter.Eventually.of_forall hpointwise)
    _ = _ := hsumInt
    _ ≤ ∑ y ∈ Critical2DKPZ.Polymer.endpoints x s,
          Critical2DKPZ.srwKernel s (y - x) *
            (42 * ((n - s : ℕ) * β ^ 2) ^ 2) := by
      apply Finset.sum_le_sum
      intro y hy
      have h := integral_abs_pointToPlane_sub_one_pow_four_le
        (k := k) β s y hsmall
      simpa only [k] using mul_le_mul_of_nonneg_left h (hweight y)
    _ = 42 * ((n - s : ℕ) * β ^ 2) ^ 2 := by
      rw [← Finset.sum_mul, hmass]
      ring

/-- Two successive walk steps can return to the origin with probability at
least `1/16`, independently of the current time. -/
theorem srwKernel_two_step_return_lower (n : ℕ) :
    (1 / 16 : ℝ) * Critical2DKPZ.srwKernel n 0 ≤
      Critical2DKPZ.srwKernel (n + 2) 0 := by
  have houterRec : Critical2DKPZ.srwKernel (n + 2) 0 =
      (∑ i : Fin 4, Critical2DKPZ.srwKernel (n + 1)
        (0 - Critical2DKPZ.srwStep i)) / 4 := by
    rw [show n + 2 = (n + 1) + 1 by omega,
      Critical2DKPZ.srwKernel_succ]
  have houterTerm : Critical2DKPZ.srwKernel (n + 1)
      (0 - Critical2DKPZ.srwStep 0) ≤
      ∑ i : Fin 4, Critical2DKPZ.srwKernel (n + 1)
        (0 - Critical2DKPZ.srwStep i) :=
    Finset.single_le_sum (fun i hi =>
      Critical2DKPZ.Polymer.kernel_nonneg (n + 1)
        (0 - Critical2DKPZ.srwStep i)) (Finset.mem_univ 0)
  have houter : Critical2DKPZ.srwKernel (n + 1)
      (-Critical2DKPZ.srwStep 0) / 4 ≤
      Critical2DKPZ.srwKernel (n + 2) 0 := by
    rw [houterRec]
    have hterm := houterTerm
    simpa only [zero_sub] using
      (div_le_div_of_nonneg_right hterm (by norm_num : 0 ≤ (4 : ℝ)))
  have hinnerRec : Critical2DKPZ.srwKernel (n + 1)
      (-Critical2DKPZ.srwStep 0) =
      (∑ i : Fin 4, Critical2DKPZ.srwKernel n
        ((-Critical2DKPZ.srwStep 0) - Critical2DKPZ.srwStep i)) / 4 := by
    rw [Critical2DKPZ.srwKernel_succ]
  have hreturn : (-Critical2DKPZ.srwStep 0) -
      Critical2DKPZ.srwStep (Critical2DKPZ.Polymer.oppositeStep 0) = 0 := by
    rw [Critical2DKPZ.Polymer.srwStep_opposite]
    abel
  have hinnerTerm : Critical2DKPZ.srwKernel n
      ((-Critical2DKPZ.srwStep 0) -
        Critical2DKPZ.srwStep (Critical2DKPZ.Polymer.oppositeStep 0)) ≤
      ∑ i : Fin 4, Critical2DKPZ.srwKernel n
        ((-Critical2DKPZ.srwStep 0) - Critical2DKPZ.srwStep i) :=
    Finset.single_le_sum (fun i hi =>
      Critical2DKPZ.Polymer.kernel_nonneg n
        ((-Critical2DKPZ.srwStep 0) - Critical2DKPZ.srwStep i))
      (Finset.mem_univ (Critical2DKPZ.Polymer.oppositeStep 0))
  have hinner : Critical2DKPZ.srwKernel n 0 / 4 ≤
      Critical2DKPZ.srwKernel (n + 1) (-Critical2DKPZ.srwStep 0) := by
    rw [hinnerRec]
    have hterm := hinnerTerm
    rw [hreturn] at hterm
    exact div_le_div_of_nonneg_right hterm (by norm_num : 0 ≤ (4 : ℝ))
  calc
    (1 / 16 : ℝ) * Critical2DKPZ.srwKernel n 0 =
        (Critical2DKPZ.srwKernel n 0 / 4) / 4 := by ring
    _ ≤ (Critical2DKPZ.srwKernel (n + 1)
        (-Critical2DKPZ.srwStep 0)) / 4 :=
      div_le_div_of_nonneg_right hinner (by norm_num : 0 ≤ (4 : ℝ))
    _ ≤ _ := houter

/-- A quantitative lower bound on every even-time return probability. -/
theorem srwKernel_even_return_reciprocal_lower (m : ℕ) :
    1 / (16 : ℝ) ^ m ≤ Critical2DKPZ.srwKernel (2 * m) 0 := by
  induction m with
  | zero =>
      rw [Critical2DKPZ.srwKernel_zero]
      norm_num
  | succ m ih =>
      have hstep := srwKernel_two_step_return_lower (2 * m)
      have hpow : 1 / (16 : ℝ) ^ (m + 1) =
          (1 / (16 : ℝ)) * (1 / (16 : ℝ) ^ m) := by
        rw [pow_succ]
        field_simp
      rw [show 2 * (m + 1) = 2 * m + 2 by omega]
      calc
        1 / (16 : ℝ) ^ (m + 1) =
            (1 / (16 : ℝ)) * (1 / (16 : ℝ) ^ m) := hpow
        _ ≤ (1 / (16 : ℝ)) * Critical2DKPZ.srwKernel (2 * m) 0 :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ ≤ Critical2DKPZ.srwKernel (2 * m + 2) 0 := by
          simpa only [one_div] using hstep

/-- The variance of a short smoothed profile is bounded below by its first
local-replica collision. -/
theorem smoothedP2Plane_variance_lower_of_short_horizon
    (L₀ : ℕ) (β : ℝ) (s n : ℕ) (x : Site)
    (hsn : s < n) (hn : n ≤ L₀) :
    (1 / (16 : ℝ) ^ (L₀ + 1)) * β ^ 2 ≤
      ProbabilityTheory.variance
        (fun ω : Disorder => Critical2DKPZ.smoothedP2Plane β s n x ω)
        disorderLaw := by
  let c : ℝ := 1 / (16 : ℝ) ^ (L₀ + 1)
  let m : ℕ := n - (s + 1)
  have hsle : s ≤ n := Nat.le_of_lt hsn
  have hmem : MemLp
      (fun ω : Disorder => Critical2DKPZ.smoothedP2Plane β s n x ω) 2 disorderLaw :=
    Critical2DKPZ.Polymer.memLp_smoothedP2Plane β s n x 2 (by norm_num)
  have hvarEq : ProbabilityTheory.variance
      (fun ω : Disorder => Critical2DKPZ.smoothedP2Plane β s n x ω) disorderLaw =
      (∫ ω : Disorder,
        Critical2DKPZ.smoothedP2Plane β s n x ω *
          Critical2DKPZ.smoothedP2Plane β s n x ω ∂disorderLaw) - 1 := by
    rw [ProbabilityTheory.variance_eq_sub hmem]
    simp only [Pi.pow_apply]
    rw [show (fun ω : Disorder =>
        Critical2DKPZ.smoothedP2Plane β s n x ω ^ 2) =
        fun ω => Critical2DKPZ.smoothedP2Plane β s n x ω *
          Critical2DKPZ.smoothedP2Plane β s n x ω from funext fun ω => by ring,
      Critical2DKPZ.Polymer.integral_smoothedP2Plane]
    norm_num
  have hlocal := Critical2DKPZ.Polymer.local_replica_formula
    β s n hsle x x
  rw [← hvarEq] at hlocal
  have hsecond : 1 ≤ ∫ ω : Disorder,
      Critical2DKPZ.pointToPlane β 0 (n - (s + 1)) 0 ω ^ 2 ∂disorderLaw := by
    have hmem2 := Critical2DKPZ.Polymer.memLp_pointToPlane β 0 (n - (s + 1))
      (0 : Site) 2 (by norm_num)
    have hv := ProbabilityTheory.variance_nonneg
      (fun ω : Disorder => Critical2DKPZ.pointToPlane β 0
        (n - (s + 1)) 0 ω) disorderLaw
    rw [ProbabilityTheory.variance_eq_sub hmem2,
      Critical2DKPZ.Polymer.integral_pointToPlane] at hv
    norm_num at hv
    linarith
  have hkernelLower : c ≤ Critical2DKPZ.srwKernel (2 * (s + 1)) 0 := by
    have hbase := srwKernel_even_return_reciprocal_lower (s + 1)
    have hexpNat : s + 1 ≤ L₀ + 1 := by omega
    have hexp : (16 : ℝ) ^ (s + 1) ≤ (16 : ℝ) ^ (L₀ + 1) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 16) hexpNat
    have hinv := one_div_le_one_div_of_le (by positivity :
      0 < (16 : ℝ) ^ (s + 1)) hexp
    dsimp [c]
    exact hinv.trans hbase
  have htermNonneg (r : ℕ) (hr : r ∈ Finset.Icc (s + 1) n) :
      0 ≤ Critical2DKPZ.srwKernel (2 * r) (x - x) *
        Critical2DKPZ.Polymer.sigmaSq β *
          (∫ ω : Disorder,
            Critical2DKPZ.pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw) := by
    have hq := Critical2DKPZ.Polymer.kernel_nonneg (2 * r) (x - x)
    have hsigma := Critical2DKPZ.MomentBounds.sigmaSq_nonneg β
    have hmoment : 0 ≤ ∫ ω : Disorder,
        Critical2DKPZ.pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw :=
      integral_nonneg fun ω => sq_nonneg _
    positivity
  have hsumLower' :
      Critical2DKPZ.srwKernel (2 * (s + 1)) (x - x) *
          Critical2DKPZ.Polymer.sigmaSq β *
          (∫ ω : Disorder,
            Critical2DKPZ.pointToPlane β 0 (n - (s + 1)) 0 ω ^ 2 ∂disorderLaw) ≤
        ∑ r ∈ Finset.Icc (s + 1) n,
          Critical2DKPZ.srwKernel (2 * r) (x - x) *
            Critical2DKPZ.Polymer.sigmaSq β *
            (∫ ω : Disorder,
              Critical2DKPZ.pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw) := by
    exact Finset.single_le_sum htermNonneg
      (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hsumLower :
      Critical2DKPZ.srwKernel (2 * (s + 1)) 0 *
          Critical2DKPZ.Polymer.sigmaSq β *
          (∫ ω : Disorder,
            Critical2DKPZ.pointToPlane β 0 (n - (s + 1)) 0 ω ^ 2 ∂disorderLaw) ≤
        ∑ r ∈ Finset.Icc (s + 1) n,
          Critical2DKPZ.srwKernel (2 * r) (x - x) *
            Critical2DKPZ.Polymer.sigmaSq β *
            (∫ ω : Disorder,
              Critical2DKPZ.pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw) := by
    simpa only [sub_self] using hsumLower'
  have hsigma : β ^ 2 ≤ Critical2DKPZ.Polymer.sigmaSq β :=
    Critical2DKPZ.MomentBounds.beta_sq_le_sigmaSq β
  have hkernel : 0 ≤ Critical2DKPZ.srwKernel (2 * (s + 1)) 0 :=
    Critical2DKPZ.Polymer.kernel_nonneg _ _
  have hmul : c * β ^ 2 ≤
      Critical2DKPZ.srwKernel (2 * (s + 1)) 0 *
        Critical2DKPZ.Polymer.sigmaSq β := by
    calc
      c * β ^ 2 ≤ Critical2DKPZ.srwKernel (2 * (s + 1)) 0 * β ^ 2 :=
        mul_le_mul_of_nonneg_right hkernelLower (sq_nonneg β)
      _ ≤ Critical2DKPZ.srwKernel (2 * (s + 1)) 0 *
          Critical2DKPZ.Polymer.sigmaSq β :=
        mul_le_mul_of_nonneg_left hsigma hkernel
  have hfirst : c * β ^ 2 ≤
      Critical2DKPZ.srwKernel (2 * (s + 1)) 0 *
        Critical2DKPZ.Polymer.sigmaSq β *
          (∫ ω : Disorder,
            Critical2DKPZ.pointToPlane β 0 (n - (s + 1)) 0 ω ^ 2 ∂disorderLaw) := by
    calc
      c * β ^ 2 ≤ Critical2DKPZ.srwKernel (2 * (s + 1)) 0 *
          Critical2DKPZ.Polymer.sigmaSq β := hmul
      _ = (Critical2DKPZ.srwKernel (2 * (s + 1)) 0 *
          Critical2DKPZ.Polymer.sigmaSq β) * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsecond
        (mul_nonneg hkernel (Critical2DKPZ.MomentBounds.sigmaSq_nonneg β))
  have hfinal := hfirst.trans hsumLower
  rw [← hlocal] at hfinal
  simpa only [c] using hfinal

/-- Over bounded horizons and at sufficiently small disorder strength, the centered fourth moment is controlled by both the squared variance and the fourth power of the disorder strength. -/
theorem smoothedP2Plane_fourth_moment_shortHorizon (L₀ : ℕ) :
    ∃ β₀ C : ℝ, 0 < β₀ ∧ ∀ β : ℝ, 0 ≤ β → β ≤ β₀ → ∀ s n : ℕ,
      s < n → n ≤ L₀ → ∀ x : Site,
      ∫ ω : Disorder,
        |Critical2DKPZ.smoothedP2Plane β s n x ω - 1| ^ 4 ∂disorderLaw ≤
          C * ProbabilityTheory.variance
            (fun ω : Disorder => Critical2DKPZ.smoothedP2Plane β s n x ω)
            disorderLaw ^ 2 ∧
      ∫ ω : Disorder,
        |Critical2DKPZ.smoothedP2Plane β s n x ω - 1| ^ 4 ∂disorderLaw ≤ C * β ^ 4 := by
  let β₀ : ℝ := 1 / (6 * (L₀ + 1 : ℝ))
  let c : ℝ := 1 / (16 : ℝ) ^ (L₀ + 1)
  let A : ℝ := 42 * (L₀ + 1 : ℝ) ^ 2
  let C : ℝ := A * (16 : ℝ) ^ (2 * (L₀ + 1))
  have hβ₀pos : 0 < β₀ := by
    dsimp [β₀]
    positivity
  have hβ₀le : β₀ ≤ 1 := by
    dsimp [β₀]
    have hden : 1 ≤ 6 * (L₀ + 1 : ℝ) := by
      have hL : 0 ≤ (L₀ : ℝ) := Nat.cast_nonneg _
      nlinarith
    calc
      1 / (6 * (L₀ + 1 : ℝ)) ≤ 1 / 1 :=
        one_div_le_one_div_of_le (by norm_num) hden
      _ = 1 := by norm_num
  have hCpos : 0 ≤ C := by
    dsimp [C, A]
    positivity
  have hAleC : A ≤ C := by
    dsimp [C]
    have hpow : 1 ≤ (16 : ℝ) ^ (2 * (L₀ + 1)) :=
      one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 16)
    dsimp [A]
    nlinarith [mul_nonneg (by positivity : 0 ≤ 42 * (L₀ + 1 : ℝ) ^ 2)
      (sub_nonneg.mpr hpow)]
  have hCcSq : C * c ^ 2 = A := by
    dsimp [C, c]
    have hp : (16 : ℝ) ^ (2 * (L₀ + 1)) =
        ((16 : ℝ) ^ (L₀ + 1)) ^ 2 := by
      rw [← pow_mul]
      congr 1
      omega
    rw [hp]
    field_simp
  refine ⟨β₀, C, hβ₀pos, fun β hβ0 hβle s n hsn hn x => ?_⟩
  have hβle1 : β ≤ 1 := hβle.trans hβ₀le
  have hβsqle : β ^ 2 ≤ β := by nlinarith [sq_nonneg β]
  have hk : n - s ≤ L₀ := by omega
  have hsmall : 6 * ((n - s : ℕ) : ℝ) * β ^ 2 ≤ 1 := by
    have hkR : (n - s : ℕ) ≤ (L₀ : ℝ) := by exact_mod_cast hk
    calc
      6 * ((n - s : ℕ) : ℝ) * β ^ 2 ≤
          6 * ((n - s : ℕ) : ℝ) * β := by
            exact mul_le_mul_of_nonneg_left hβsqle
              (by positivity : 0 ≤ 6 * ((n - s : ℕ) : ℝ))
      _ ≤ 6 * (L₀ : ℝ) * β := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hkR (by norm_num)) hβ0
      _ ≤ 6 * (L₀ + 1 : ℝ) * β₀ := by
        have hcoeff : 6 * (L₀ : ℝ) ≤ 6 * (L₀ + 1 : ℝ) := by nlinarith
        calc
          6 * (L₀ : ℝ) * β ≤ 6 * (L₀ + 1 : ℝ) * β :=
            mul_le_mul_of_nonneg_right hcoeff hβ0
          _ ≤ 6 * (L₀ + 1 : ℝ) * β₀ :=
            mul_le_mul_of_nonneg_left hβle (by positivity)
      _ = 1 := by dsimp [β₀]; field_simp
  have hfourth := integral_abs_smoothedP2Plane_sub_one_pow_four_le β x hsmall
  have hfourthβ :
      ∫ ω : Disorder,
        |Critical2DKPZ.smoothedP2Plane β s n x ω - 1| ^ 4 ∂disorderLaw ≤
          A * β ^ 4 := by
    have hkR : ((n - s : ℕ) : ℝ) ≤ (L₀ + 1 : ℝ) := by
      exact_mod_cast Nat.le_succ_of_le hk
    have hprod : 0 ≤ ((n - s : ℕ) : ℝ) * β ^ 2 := by positivity
    have hprodLe : ((n - s : ℕ) : ℝ) * β ^ 2 ≤
        (L₀ + 1 : ℝ) * β ^ 2 :=
      mul_le_mul_of_nonneg_right hkR (sq_nonneg β)
    have hsquare := (sq_le_sq₀ hprod (by positivity)).2 hprodLe
    dsimp [A]
    calc
      _ ≤ 42 * (((n - s : ℕ) : ℝ) * β ^ 2) ^ 2 := hfourth
      _ ≤ 42 * ((L₀ + 1 : ℝ) * β ^ 2) ^ 2 := by gcongr
      _ = 42 * (L₀ + 1 : ℝ) ^ 2 * β ^ 4 := by ring
  have hvarlower := smoothedP2Plane_variance_lower_of_short_horizon
    L₀ β s n x hsn hn
  have hfirst :
      ∫ ω : Disorder,
        |Critical2DKPZ.smoothedP2Plane β s n x ω - 1| ^ 4 ∂disorderLaw ≤
          C * ProbabilityTheory.variance
            (fun ω : Disorder => Critical2DKPZ.smoothedP2Plane β s n x ω)
            disorderLaw ^ 2 := by
    calc
      _ ≤ A * β ^ 4 := hfourthβ
      _ ≤ C * ProbabilityTheory.variance
          (fun ω : Disorder => Critical2DKPZ.smoothedP2Plane β s n x ω)
          disorderLaw ^ 2 := by
        have hvarnonneg := ProbabilityTheory.variance_nonneg
          (fun ω : Disorder => Critical2DKPZ.smoothedP2Plane β s n x ω)
          disorderLaw
        have hsq := (sq_le_sq₀ (by positivity : 0 ≤ c * β ^ 2)
          hvarnonneg).2 hvarlower
        calc
          A * β ^ 4 = C * (c ^ 2 * β ^ 4) := by
            rw [← hCcSq]
            ring
          _ ≤ C * ProbabilityTheory.variance
              (fun ω : Disorder => Critical2DKPZ.smoothedP2Plane β s n x ω)
              disorderLaw ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ hCpos
            nlinarith [hsq]
  exact ⟨hfirst, by
    calc
      _ ≤ A * β ^ 4 := hfourthβ
      _ ≤ C * β ^ 4 := mul_le_mul_of_nonneg_right hAleC (by positivity)⟩

end

end Critical2DKPZ.MomentBounds
