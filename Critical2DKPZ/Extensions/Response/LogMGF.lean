/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Logarithmic moment generating functions under finite measures

Bounded measurable observables have integrable exponential moments at every real parameter.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.Response

variable {α : Type*} [MeasurableSpace α]

/-- Unnormalised logarithmic moment generating function. Subtract its value at zero
when using a finite measure that is not a probability measure. -/
def logMgf (ν : Measure α) (v : α → ℝ) (q : ℝ) : ℝ :=
  Real.log (∫ y, Real.exp (q * v y) ∂ν)

/-- Unnormalised moment of order `k` with exponential weight. -/
def tiltedMoment (ν : Measure α) (v : α → ℝ) (k : ℕ) (q : ℝ) : ℝ :=
  ∫ y, v y ^ k * Real.exp (q * v y) ∂ν

omit [MeasurableSpace α] in
/-- A uniform bound for a bounded observable times its exponential weight. -/
theorem tiltedMoment_integrand_bound (v : α → ℝ) (M q : ℝ) (k : ℕ)
    (hv : ∀ y, |v y| ≤ M) (y : α) :
    ‖v y ^ k * Real.exp (q * v y)‖ ≤ M ^ k * Real.exp (|q| * M) := by
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  have hp : |v y| ^ k ≤ M ^ k := pow_le_pow_left₀ (abs_nonneg _) (hv y) k
  have hq : q * v y ≤ |q| * M := calc
    q * v y ≤ |q * v y| := le_abs_self _
    _ = |q| * |v y| := abs_mul _ _
    _ ≤ |q| * M := mul_le_mul_of_nonneg_left (hv y) (abs_nonneg _)
  exact mul_le_mul hp (Real.exp_le_exp.mpr hq) (Real.exp_pos _).le
    (hp.trans' (pow_nonneg (abs_nonneg _) k))

/-- All exponentially weighted moments are integrable under a finite measure. -/
theorem integrable_tiltedMoment (ν : Measure α) [IsFiniteMeasure ν] (v : α → ℝ)
    (hv : Measurable v) (M : ℝ) (hbound : ∀ y, |v y| ≤ M) (k : ℕ) (q : ℝ) :
    Integrable (fun y => v y ^ k * Real.exp (q * v y)) ν := by
  apply (integrable_const (M ^ k * Real.exp (|q| * M))).mono'
    ((hv.pow_const k).mul ((measurable_const.mul hv).exp)).aestronglyMeasurable
  exact Eventually.of_forall (tiltedMoment_integrand_bound v M q k hbound)

/-- Differentiation of the unnormalised moments raises their order by one. -/
theorem hasDerivAt_tiltedMoment (ν : Measure α) [IsFiniteMeasure ν] (v : α → ℝ)
    (hv : Measurable v) (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ y, |v y| ≤ M)
    (k : ℕ) (q : ℝ) :
    HasDerivAt (tiltedMoment ν v k) (tiltedMoment ν v (k + 1) q) q := by
  have hd (y : α) (u : ℝ) :
      HasDerivAt (fun u => v y ^ k * Real.exp (u * v y))
        (v y ^ (k + 1) * Real.exp (u * v y)) u := by
    convert (((hasDerivAt_id u).mul_const (v y)).exp.const_mul (v y ^ k)) using 1
    · rfl
    · dsimp
      ring
  have hb (y : α) (u : ℝ) (hu : u ∈ Metric.ball q 1) :
      ‖v y ^ (k + 1) * Real.exp (u * v y)‖ ≤
        M ^ (k + 1) * Real.exp ((|q| + 1) * M) := by
    apply (tiltedMoment_integrand_bound v M u (k + 1) hbound y).trans
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hM _)
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ hM
    have hu' : |u - q| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hu
    have hh := abs_add_le (u - q) q
    have heq : u - q + q = u := by ring
    rw [heq] at hh
    linarith only [hu', hh]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u y => v y ^ k * Real.exp (u * v y))
    (F' := fun u y => v y ^ (k + 1) * Real.exp (u * v y))
    (Metric.ball_mem_nhds q (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall (fun u =>
      ((hv.pow_const k).mul ((measurable_const.mul hv).exp)).aestronglyMeasurable))
    (integrable_tiltedMoment ν v hv M hbound k q)
    (((hv.pow_const (k + 1)).mul ((measurable_const.mul hv).exp)).aestronglyMeasurable)
    (Eventually.of_forall hb)
    (integrable_const (M ^ (k + 1) * Real.exp ((|q| + 1) * M)))
    (Eventually.of_forall (fun y u _ => hd y u))).2

/-- The order-zero weighted moment is the positive partition function. -/
theorem tiltedMoment_zero_pos (ν : Measure α) [IsFiniteMeasure ν] [NeZero ν]
    (v : α → ℝ) (hv : Measurable v) (M : ℝ) (hbound : ∀ y, |v y| ≤ M) (q : ℝ) :
    0 < tiltedMoment ν v 0 q := by
  have hi := integrable_tiltedMoment ν v hv M hbound 0 q
  simp only [tiltedMoment, pow_zero, one_mul] at hi ⊢
  exact integral_exp_pos hi

/-- The first three logarithmic derivatives are the algebraic cumulants of the
exponentially weighted moments. This holds for finite nonzero measures. -/
theorem logMgf_derivs (ν : Measure α) [IsFiniteMeasure ν] [NeZero ν]
    (v : α → ℝ) (hv : Measurable v) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ y, |v y| ≤ M) (q : ℝ) :
    let m := tiltedMoment ν v
    HasDerivAt (logMgf ν v) (m 1 q / m 0 q) q ∧
    HasDerivAt (fun u => m 1 u / m 0 u)
      (m 2 q / m 0 q - (m 1 q / m 0 q) ^ 2) q ∧
    HasDerivAt (fun u => m 2 u / m 0 u - (m 1 u / m 0 u) ^ 2)
      (m 3 q / m 0 q - 3 * (m 2 q / m 0 q) * (m 1 q / m 0 q) +
        2 * (m 1 q / m 0 q) ^ 3) q := by
  dsimp only
  have hd := hasDerivAt_tiltedMoment ν v hv M hM hbound
  have hpos := (tiltedMoment_zero_pos ν v hv M hbound q).ne'
  have hfirst := (hd 1 q).div (hd 0 q) hpos
  have hsecond := (hd 2 q).div (hd 0 q) hpos
  have hfirst' : HasDerivAt (fun u => tiltedMoment ν v 1 u / tiltedMoment ν v 0 u)
      (tiltedMoment ν v 2 q / tiltedMoment ν v 0 q -
        (tiltedMoment ν v 1 q / tiltedMoment ν v 0 q) ^ 2) q := by
    convert hfirst using 1
    field_simp [hpos]
  refine ⟨?_, hfirst', ?_⟩
  · change HasDerivAt (fun u => Real.log (∫ y, Real.exp (u * v y) ∂ν)) _ q
    have hh := (hd 0 q).log hpos
    simpa only [logMgf, tiltedMoment, pow_zero, one_mul, Nat.zero_add] using hh
  · convert hsecond.sub (hfirst'.pow 2) using 1
    norm_num only [Nat.reduceAdd, Nat.reduceSub, pow_one]
    field_simp [hpos]
    ring

/-- Exponentially tilted laws are probability measures for every real parameter. -/
theorem isProbabilityMeasure_bounded_tilt (ν : Measure α) [IsFiniteMeasure ν] [NeZero ν]
    (v : α → ℝ) (hv : Measurable v) (M : ℝ) (hbound : ∀ y, |v y| ≤ M) (q : ℝ) :
    IsProbabilityMeasure (ν.tilted (fun y => q * v y)) := by
  apply isProbabilityMeasure_tilted
  simpa only [pow_zero, one_mul] using integrable_tiltedMoment ν v hv M hbound 0 q

/-- Normalised weighted moments are moments of the tilted law. -/
theorem tiltedMoment_div_eq_integral (ν : Measure α) (v : α → ℝ) (k : ℕ) (q : ℝ) :
    tiltedMoment ν v k q / tiltedMoment ν v 0 q =
      ∫ y, v y ^ k ∂(ν.tilted (fun y => q * v y)) := by
  rw [integral_tilted]
  simp only [tiltedMoment, pow_zero, one_mul, smul_eq_mul]
  rw [← integral_div]
  congr 1
  ext y
  ring

/-- Powers of bounded measurable real observables are integrable under finite measures. -/
theorem integrable_bounded_pow (ν : Measure α) [IsFiniteMeasure ν] (v : α → ℝ)
    (hv : Measurable v) (M : ℝ) (hbound : ∀ y, |v y| ≤ M) (k : ℕ) :
    Integrable (fun y => v y ^ k) ν := by
  apply (integrable_const (M ^ k)).mono' (hv.pow_const k).aestronglyMeasurable
  filter_upwards [] with y
  simpa only [Real.norm_eq_abs, abs_pow] using pow_le_pow_left₀ (abs_nonneg (v y)) (hbound y) k

/-- The third central moment expanded into raw moments under a probability law. -/
theorem integral_centered_cube_eq (ν : Measure α) [IsProbabilityMeasure ν] (v : α → ℝ)
    (hv : Measurable v) (M : ℝ) (hbound : ∀ y, |v y| ≤ M) :
    (∫ y, (v y - ∫ z, v z ∂ν) ^ 3 ∂ν) =
      (∫ y, v y ^ 3 ∂ν) - 3 * (∫ y, v y ^ 2 ∂ν) * (∫ y, v y ∂ν) +
        2 * (∫ y, v y ∂ν) ^ 3 := by
  let m := ∫ y, v y ∂ν
  have hi := integrable_bounded_pow ν v hv M hbound
  have h1 : Integrable v ν := by simpa only [pow_one] using hi 1
  have hid : (fun y => (v y - m) ^ 3) =
      (fun y => v y ^ 3 - (3 * m) * v y ^ 2 + (3 * m ^ 2) * v y - m ^ 3) := by
    ext y; ring
  change (∫ y, (v y - m) ^ 3 ∂ν) = _
  have h2 : Integrable (fun y => (3 * m) * v y ^ 2) ν := (hi 2).const_mul _
  have hlin : Integrable (fun y => (3 * m ^ 2) * v y) ν := h1.const_mul _
  have hsub : Integrable (fun y => v y ^ 3 - (3 * m) * v y ^ 2) ν := (hi 3).sub h2
  have hadd : Integrable (fun y => v y ^ 3 - (3 * m) * v y ^ 2 + (3 * m ^ 2) * v y) ν :=
    hsub.add hlin
  rw [hid, integral_sub hadd (integrable_const (m ^ 3)), integral_add hsub hlin,
    integral_sub (hi 3) h2]
  simp only [integral_const_mul, integral_const, probReal_univ, one_smul]
  dsimp [m]
  ring

/-- The first three algebraic cumulants are the tilted mean, variance, and third
central moment, respectively. -/
theorem logMgf_derivs_eq_tilted (ν : Measure α) [IsFiniteMeasure ν] [NeZero ν]
    (v : α → ℝ) (hv : Measurable v) (M : ℝ) (hbound : ∀ y, |v y| ≤ M) (q : ℝ) :
    let m := tiltedMoment ν v
    let π := ν.tilted (fun y => q * v y)
    m 1 q / m 0 q = (∫ y, v y ∂π) ∧
    m 2 q / m 0 q - (m 1 q / m 0 q) ^ 2 = ProbabilityTheory.variance v π ∧
    m 3 q / m 0 q - 3 * (m 2 q / m 0 q) * (m 1 q / m 0 q) +
        2 * (m 1 q / m 0 q) ^ 3 =
      ∫ y, (v y - ∫ z, v z ∂π) ^ 3 ∂π := by
  dsimp only
  let π := ν.tilted (fun y => q * v y)
  let : IsProbabilityMeasure π := isProbabilityMeasure_bounded_tilt ν v hv M hbound q
  have hm := tiltedMoment_div_eq_integral ν v
  have h1 : tiltedMoment ν v 1 q / tiltedMoment ν v 0 q = ∫ y, v y ∂π := by
    simpa only [pow_one] using hm 1 q
  refine ⟨h1, ?_, ?_⟩
  · rw [h1, hm 2 q, ProbabilityTheory.variance_eq_sub
      (MemLp.of_bound hv.aestronglyMeasurable M (Eventually.of_forall (fun y => by
        simpa only [Real.norm_eq_abs] using hbound y)))]
    rfl
  · rw [h1, hm 2 q, hm 3 q]
    exact (integral_centered_cube_eq π v hv M hbound).symm

/-- A bounded observable has a bounded expectation under a probability law. -/
theorem abs_integral_le_of_bounded (ν : Measure α) [IsProbabilityMeasure ν]
    (v : α → ℝ) (M : ℝ) (hbound : ∀ y, |v y| ≤ M) :
    |∫ y, v y ∂ν| ≤ M := by
  have hh := norm_integral_le_of_norm_le_const (μ := ν)
    (Eventually.of_forall (fun y => show ‖v y‖ ≤ M from hbound y))
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hh

/-- Variance of a bounded observable lies between zero and the square of its bound. -/
theorem variance_le_of_bounded (ν : Measure α) [IsProbabilityMeasure ν]
    (v : α → ℝ) (hv : Measurable v) (M : ℝ) (hbound : ∀ y, |v y| ≤ M) :
    0 ≤ ProbabilityTheory.variance v ν ∧ ProbabilityTheory.variance v ν ≤ M ^ 2 := by
  refine ⟨ProbabilityTheory.variance_nonneg _ _, ?_⟩
  rw [ProbabilityTheory.variance_eq_sub (MemLp.of_bound hv.aestronglyMeasurable M
    (Eventually.of_forall (fun y => show ‖v y‖ ≤ M from hbound y)))]
  have hb : (∫ y, v y ^ 2 ∂ν) ≤ M ^ 2 := by
    have hh := integral_mono (integrable_bounded_pow ν v hv M hbound 2)
      (integrable_const (M ^ 2)) (fun y => by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (v y)) (hbound y) 2)
    simpa only [integral_const, probReal_univ, one_smul] using hh
  change (∫ y, v y ^ 2 ∂ν) - (∫ y, v y ∂ν) ^ 2 ≤ M ^ 2
  linarith only [hb, sq_nonneg (∫ y, v y ∂ν)]

/-- The centered cube is integrable, with absolute integral at most `(2M)³`. -/
theorem integral_centered_cube_bound (ν : Measure α) [IsProbabilityMeasure ν]
    (v : α → ℝ) (hv : Measurable v) (M : ℝ) (hbound : ∀ y, |v y| ≤ M) :
    Integrable (fun y => (v y - ∫ z, v z ∂ν) ^ 3) ν ∧
    |∫ y, (v y - ∫ z, v z ∂ν) ^ 3 ∂ν| ≤ 8 * M ^ 3 := by
  have hm := abs_integral_le_of_bounded ν v M hbound
  have hc (y : α) : |v y - ∫ z, v z ∂ν| ≤ 2 * M :=
    (abs_sub _ _).trans (by linarith only [hbound y, hm])
  refine ⟨integrable_bounded_pow ν _ (hv.sub measurable_const) (2 * M) hc 3, ?_⟩
  have hh := abs_integral_le_of_bounded ν (fun y => (v y - ∫ z, v z ∂ν) ^ 3)
    ((2 * M) ^ 3) (fun y => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hc y) 3)
  convert hh using 1
  ring

/-- The quantitative bounds of Proposition 4.1 for a finite nonzero measure. -/
theorem logMgf_bounds (ν : Measure α) [IsFiniteMeasure ν] [NeZero ν]
    (v : α → ℝ) (hv : Measurable v) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ y, |v y| ≤ M) (q : ℝ) :
    let m := tiltedMoment ν v
    |logMgf ν v q - logMgf ν v 0| ≤ M * |q| ∧
    |m 1 q / m 0 q| ≤ M ∧
    (0 ≤ m 2 q / m 0 q - (m 1 q / m 0 q) ^ 2 ∧
      m 2 q / m 0 q - (m 1 q / m 0 q) ^ 2 ≤ M ^ 2) ∧
    |m 3 q / m 0 q - 3 * (m 2 q / m 0 q) * (m 1 q / m 0 q) +
      2 * (m 1 q / m 0 q) ^ 3| ≤ 8 * M ^ 3 := by
  dsimp only
  have hm (u : ℝ) : |tiltedMoment ν v 1 u / tiltedMoment ν v 0 u| ≤ M := by
    let π := ν.tilted (fun y => u * v y)
    let : IsProbabilityMeasure π := isProbabilityMeasure_bounded_tilt ν v hv M hbound u
    rw [(logMgf_derivs_eq_tilted ν v hv M hbound u).1]
    exact abs_integral_le_of_bounded π v M hbound
  refine ⟨?_, hm q, ?_, ?_⟩
  · have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (s := Set.univ) (f := logMgf ν v)
      (fun u _ => (logMgf_derivs ν v hv M hM hbound u).1.hasDerivWithinAt)
      (fun u _ => show ‖tiltedMoment ν v 1 u / tiltedMoment ν v 0 u‖ ≤ M from hm u)
      (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ 0) (Set.mem_univ q)
    simpa only [Real.norm_eq_abs, sub_zero] using hh
  · let π := ν.tilted (fun y => q * v y)
    let : IsProbabilityMeasure π := isProbabilityMeasure_bounded_tilt ν v hv M hbound q
    rw [(logMgf_derivs_eq_tilted ν v hv M hbound q).2.1]
    exact variance_le_of_bounded π v hv M hbound
  · let π := ν.tilted (fun y => q * v y)
    let : IsProbabilityMeasure π := isProbabilityMeasure_bounded_tilt ν v hv M hbound q
    rw [(logMgf_derivs_eq_tilted ν v hv M hbound q).2.2]
    exact (integral_centered_cube_bound π v hv M hbound).2


end Critical2DKPZ.Extensions.Response
