/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.Response.StartingLaw
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

/-! # Calculus of the spatially tested cutoff response

The deterministic good event permits differentiation of the tested log-MGF three times.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped BoundedContinuousFunction ENNReal Topology
namespace Critical2DKPZ.Extensions.Response

/-- Raw exponentially weighted cutoff moment, in the terminal-heat orientation. -/
def cutoffMoment {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (t r : ℝ) (h v : Plane →ᵇ ℝ) (ω : Ω) (k : ℕ) (q : ℝ) (x : Plane) : ℝ :=
  shfPairing Z 0 t (fun y => Real.exp (h y + q * v y) * v y ^ k)
    (fun y => heatKernel r (y - x)) ω

/-- The first pointwise cutoff cumulant. -/
def cutoffMean {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (t r : ℝ) (h v : Plane →ᵇ ℝ) (ω : Ω) (q : ℝ) (x : Plane) : ℝ :=
  cutoffMoment Z t r h v ω 1 q x / cutoffMoment Z t r h v ω 0 q x

/-- The second pointwise cutoff cumulant. -/
def cutoffVariance {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (t r : ℝ) (h v : Plane →ᵇ ℝ) (ω : Ω) (q : ℝ) (x : Plane) : ℝ :=
  cutoffMoment Z t r h v ω 2 q x / cutoffMoment Z t r h v ω 0 q x -
    cutoffMean Z t r h v ω q x ^ 2

/-- The third pointwise cutoff cumulant. -/
def cutoffThird {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (t r : ℝ) (h v : Plane →ᵇ ℝ) (ω : Ω) (q : ℝ) (x : Plane) : ℝ :=
  cutoffMoment Z t r h v ω 3 q x / cutoffMoment Z t r h v ω 0 q x -
    3 * (cutoffMoment Z t r h v ω 2 q x / cutoffMoment Z t r h v ω 0 q x) *
      cutoffMean Z t r h v ω q x + 2 * cutoffMean Z t r h v ω q x ^ 3

/-- Uniform bound for an exponentially tilted bounded profile times a power. -/
theorem cutoff_profile_bound (h v : Plane →ᵇ ℝ) (k : ℕ) (q : ℝ) (y : Plane) :
    |Real.exp (h y + q * v y) * v y ^ k| ≤ Real.exp ‖h + q • v‖ * ‖v‖ ^ k := by
  rw [abs_mul, abs_pow]
  have he : |Real.exp (h y + q * v y)| ≤ Real.exp ‖h + q • v‖ := by
    simpa using exp_profile_bound (h + q • v) y
  exact mul_le_mul he (pow_le_pow_left₀ (abs_nonneg _) (v.norm_coe_le_norm y) k)
    (pow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le

/-- All raw cutoff moments are continuous in the spatial centre on the good event. -/
theorem continuous_cutoffMoment_x {Ω : Type*}
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t r : ℝ) (hr : 0 < r)
    (h v : Plane →ᵇ ℝ) (ω : Ω)
    (hint : Integrable (fun p : Plane × Plane => heatKernel (2 * r) p.2) (Z 0 t ω))
    (k : ℕ) (q : ℝ) : Continuous (cutoffMoment Z t r h v ω k q) :=
  continuous_pairing_x hr hint (by fun_prop) (cutoff_profile_bound h v k q)

/-- The weighted partition function is positive on the deterministic good event. -/
theorem cutoffMoment_zero_pos {Ω : Type*}
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t r : ℝ) (hr : 0 < r)
    (h v : Plane →ᵇ ℝ) (ω : Ω)
    (hint : ∀ x, Integrable (fun p : Plane × Plane => heatKernel r (p.2 - x)) (Z 0 t ω))
    (hpos : 0 < shfPairing Z 0 t (fun _ => 1) (heatKernel r) ω) (q : ℝ) (x : Plane) :
    0 < cutoffMoment Z t r h v ω 0 q x := by
  have hh := pairing_pos hr hint
    (show 0 < ∫ p, heatKernel r p.2 ∂(Z 0 t ω) by simpa only [shfPairing, one_mul] using hpos)
    (Real.continuous_exp.comp (h + q • v).continuous) (exp_profile_bound (h + q • v))
    (fun y => Real.exp_pos ((h + q • v) y)) x
  simpa [cutoffMoment, shfPairing] using hh

/-- Moment derivatives raise the raw moment order. -/
theorem hasDerivAt_cutoffMoment {Ω : Type*}
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t r : ℝ) (hr : 0 < r)
    (h v : Plane →ᵇ ℝ) (ω : Ω)
    (hint : ∀ x, Integrable (fun p : Plane × Plane => heatKernel r (p.2 - x)) (Z 0 t ω))
    (k : ℕ) (q : ℝ) (x : Plane) :
    HasDerivAt (fun u => cutoffMoment Z t r h v ω k u x)
      (cutoffMoment Z t r h v ω (k + 1) q x) q := by
  let ν := cutoffBase Z t r h x ω
  let : IsFiniteMeasure ν := isFiniteMeasure_cutoffBase Z t r hr h x ω (hint x)
  have hm (j : ℕ) (u : ℝ) : tiltedMoment ν v j u = cutoffMoment Z t r h v ω j u x :=
    integral_cutoffBase Z t r hr h v x ω j u
  have heq : tiltedMoment ν v k = fun u => cutoffMoment Z t r h v ω k u x := funext (hm k)
  rw [← heq, ← hm (k + 1) q]
  exact hasDerivAt_tiltedMoment ν v v.continuous.measurable ‖v‖ (norm_nonneg _)
    (fun y => v.norm_coe_le_norm y) k q

/-- Raw moments are continuous in the response parameter. -/
theorem continuous_cutoffMoment_q {Ω : Type*}
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t r : ℝ) (hr : 0 < r)
    (h v : Plane →ᵇ ℝ) (ω : Ω)
    (hint : ∀ x, Integrable (fun p : Plane × Plane => heatKernel r (p.2 - x)) (Z 0 t ω))
    (k : ℕ) (x : Plane) : Continuous (fun q => cutoffMoment Z t r h v ω k q x) :=
  continuous_iff_continuousAt.mpr (fun q =>
    (hasDerivAt_cutoffMoment Z t r hr h v ω hint k q x).continuousAt)

/-- The first three pointwise cutoff derivatives at `q` are the first three
cumulants of `v` under the `q`-tilted starting-point law. -/
theorem cutoff_cumulant_derivs {Ω : Type*}
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t r : ℝ) (hr : 0 < r)
    (h v : Plane →ᵇ ℝ) (ω : Ω)
    (hint : ∀ x, Integrable (fun p : Plane × Plane => heatKernel r (p.2 - x)) (Z 0 t ω))
    (hpos : 0 < shfPairing Z 0 t (fun _ => 1) (heatKernel r) ω) (q : ℝ) (x : Plane) :
    HasDerivAt (fun u => Real.log (cutoffMoment Z t r h v ω 0 u x) -
      Real.log (cutoffMoment Z t r h v ω 0 0 x)) (cutoffMean Z t r h v ω q x) q ∧
    HasDerivAt (fun u => cutoffMean Z t r h v ω u x) (cutoffVariance Z t r h v ω q x) q ∧
    HasDerivAt (fun u => cutoffVariance Z t r h v ω u x) (cutoffThird Z t r h v ω q x) q := by
  let ν := cutoffBase Z t r h x ω
  let : IsFiniteMeasure ν := isFiniteMeasure_cutoffBase Z t r hr h x ω (hint x)
  let : NeZero ν := neZero_cutoffBase Z t r hr h x ω hint hpos
  have hm (k : ℕ) (u : ℝ) : tiltedMoment ν v k u = cutoffMoment Z t r h v ω k u x :=
    integral_cutoffBase Z t r hr h v x ω k u
  have hlog : logMgf ν v = fun u => Real.log (cutoffMoment Z t r h v ω 0 u x) := by
    funext u
    have hh := hm 0 u
    simpa only [logMgf, tiltedMoment, pow_zero, one_mul] using congrArg Real.log hh
  have hd := logMgf_derivs ν v v.continuous.measurable ‖v‖ (norm_nonneg _)
    (fun y => v.norm_coe_le_norm y) q
  dsimp only at hd
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hlog, hm, cutoffMean] using (hd.1.sub_const (logMgf ν v 0))
  · simpa only [hm, cutoffMean, cutoffVariance] using hd.2.1
  · simpa only [hm, cutoffMean, cutoffVariance, cutoffThird] using hd.2.2

/-- Pointwise bounds for the logarithmic increment and its first three derivatives,
independent of the spatial centre. -/
theorem cutoff_cumulant_bounds {Ω : Type*}
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t r : ℝ) (hr : 0 < r)
    (h v : Plane →ᵇ ℝ) (ω : Ω)
    (hint : ∀ x, Integrable (fun p : Plane × Plane => heatKernel r (p.2 - x)) (Z 0 t ω))
    (hpos : 0 < shfPairing Z 0 t (fun _ => 1) (heatKernel r) ω) (q : ℝ) (x : Plane) :
    |Real.log (cutoffMoment Z t r h v ω 0 q x) - Real.log (cutoffMoment Z t r h v ω 0 0 x)| ≤
        ‖v‖ * |q| ∧
    |cutoffMean Z t r h v ω q x| ≤ ‖v‖ ∧
    (0 ≤ cutoffVariance Z t r h v ω q x ∧ cutoffVariance Z t r h v ω q x ≤ ‖v‖ ^ 2) ∧
    |cutoffThird Z t r h v ω q x| ≤ 8 * ‖v‖ ^ 3 := by
  let ν := cutoffBase Z t r h x ω
  let : IsFiniteMeasure ν := isFiniteMeasure_cutoffBase Z t r hr h x ω (hint x)
  let : NeZero ν := neZero_cutoffBase Z t r hr h x ω hint hpos
  have hm (k : ℕ) (u : ℝ) : tiltedMoment ν v k u = cutoffMoment Z t r h v ω k u x :=
    integral_cutoffBase Z t r hr h v x ω k u
  have hlog (u : ℝ) : logMgf ν v u = Real.log (cutoffMoment Z t r h v ω 0 u x) := by
    have hh := hm 0 u
    simpa only [logMgf, tiltedMoment, pow_zero, one_mul] using congrArg Real.log hh
  simpa only [hm, hlog, cutoffMean, cutoffVariance, cutoffThird] using
    logMgf_bounds ν v v.continuous.measurable ‖v‖ (norm_nonneg _) (fun y => v.norm_coe_le_norm y) q

/-- Spatial continuity of the cutoff log increment and its first three derivatives. -/
theorem continuous_cutoffCumulants_x {Ω : Type*}
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t r : ℝ) (hr : 0 < r)
    (h v : Plane →ᵇ ℝ) (ω : Ω)
    (hint : Integrable (fun p : Plane × Plane => heatKernel (2 * r) p.2) (Z 0 t ω))
    (hpos : 0 < shfPairing Z 0 t (fun _ => 1) (heatKernel r) ω) (q : ℝ) :
    Continuous (fun x => Real.log (cutoffMoment Z t r h v ω 0 q x) -
      Real.log (cutoffMoment Z t r h v ω 0 0 x)) ∧
    Continuous (cutoffMean Z t r h v ω q) ∧ Continuous (cutoffVariance Z t r h v ω q) ∧
    Continuous (cutoffThird Z t r h v ω q) := by
  have hc := continuous_cutoffMoment_x Z t r hr h v ω hint
  have hp := cutoffMoment_zero_pos Z t r hr h v ω (integrable_heat_shift hr hint) hpos
  have hratio (k : ℕ) : Continuous (fun x => cutoffMoment Z t r h v ω k q x /
      cutoffMoment Z t r h v ω 0 q x) := (hc k q).div (hc 0 q) (fun x => (hp q x).ne')
  refine ⟨((hc 0 q).log (fun x => (hp q x).ne')).sub
    ((hc 0 0).log (fun x => (hp 0 x).ne')), hratio 1, ?_, ?_⟩
  · exact (hratio 2).sub ((hratio 1).pow 2)
  · exact ((hratio 3).sub ((continuous_const.mul (hratio 2)).mul (hratio 1))).add
      (continuous_const.mul ((hratio 1).pow 3))

/-- The third pointwise cumulant is continuous in the response parameter. -/
theorem continuous_cutoffThird_q {Ω : Type*}
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t r : ℝ) (hr : 0 < r)
    (h v : Plane →ᵇ ℝ) (ω : Ω)
    (hint : ∀ x, Integrable (fun p : Plane × Plane => heatKernel r (p.2 - x)) (Z 0 t ω))
    (hpos : 0 < shfPairing Z 0 t (fun _ => 1) (heatKernel r) ω) (x : Plane) :
    Continuous (fun q => cutoffThird Z t r h v ω q x) := by
  have hc := continuous_cutoffMoment_q Z t r hr h v ω hint
  have hp := cutoffMoment_zero_pos Z t r hr h v ω hint hpos
  have hratio (k : ℕ) : Continuous (fun q => cutoffMoment Z t r h v ω k q x /
      cutoffMoment Z t r h v ω 0 q x) := (hc k x).div (hc 0 x) (fun q => (hp q x).ne')
  exact ((hratio 3).sub ((continuous_const.mul (hratio 2)).mul (hratio 1))).add
    (continuous_const.mul ((hratio 1).pow 3))

/-- All four tested pointwise cumulants are integrable in the spatial centre. -/
theorem integrable_testFn_cutoffCumulants {Ω : Type*}
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t r : ℝ) (hr : 0 < r)
    (h v : Plane →ᵇ ℝ) (ψ : TestFn) (ω : Ω)
    (hint : Integrable (fun p : Plane × Plane => heatKernel (2 * r) p.2) (Z 0 t ω))
    (hpos : 0 < shfPairing Z 0 t (fun _ => 1) (heatKernel r) ω) (q : ℝ) :
    Integrable (fun x => ψ x * (Real.log (cutoffMoment Z t r h v ω 0 q x) -
      Real.log (cutoffMoment Z t r h v ω 0 0 x))) ∧
    Integrable (fun x => ψ x * cutoffMean Z t r h v ω q x) ∧
    Integrable (fun x => ψ x * cutoffVariance Z t r h v ω q x) ∧
    Integrable (fun x => ψ x * cutoffThird Z t r h v ω q x) := by
  have hc := continuous_cutoffCumulants_x Z t r hr h v ω hint hpos q
  exact ⟨(ψ.continuous.mul hc.1).integrable_of_hasCompactSupport ψ.hasCompactSupport.mul_right,
    (ψ.continuous.mul hc.2.1).integrable_of_hasCompactSupport ψ.hasCompactSupport.mul_right,
    (ψ.continuous.mul hc.2.2.1).integrable_of_hasCompactSupport ψ.hasCompactSupport.mul_right,
    (ψ.continuous.mul hc.2.2.2).integrable_of_hasCompactSupport ψ.hasCompactSupport.mul_right⟩

/-- Integrating a uniformly dominated derivative against a test function commutes
with scalar differentiation. -/
theorem hasDerivAt_integral_testFn {F F₁ : ℝ → Plane → ℝ} (ψ : TestFn)
    (hF : ∀ q, Integrable (fun x => ψ x * F q x))
    (hF₁ : ∀ q, Integrable (fun x => ψ x * F₁ q x))
    (hd : ∀ q x, HasDerivAt (fun u => F u x) (F₁ q x) q)
    (C : ℝ) (hC : ∀ q x, |F₁ q x| ≤ C) (q : ℝ) :
    HasDerivAt (fun u => ∫ x, ψ x * F u x) (∫ x, ψ x * F₁ q x) q := by
  have hψ : Integrable (fun x => |ψ x|) :=
    (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).abs
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u x => ψ x * F u x) (F' := fun u x => ψ x * F₁ u x)
    (s := Set.univ) (bound := fun x => |ψ x| * C)
    (Filter.univ_mem : Set.univ ∈ 𝓝 q)
    (Eventually.of_forall (fun u => (hF u).aestronglyMeasurable)) (hF q)
    (hF₁ q).aestronglyMeasurable
    (Eventually.of_forall (fun x u _ => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hC u x) (abs_nonneg _)))
    (hψ.mul_const C) (Eventually.of_forall (fun x u _ => (hd u x).const_mul (ψ x)))).2

/-- A constant pointwise bound integrates to the L¹ norm of the test. -/
theorem abs_integral_testFn_mul_le {F : Plane → ℝ} (ψ : TestFn) (C : ℝ)
    (_hF : Integrable (fun x => ψ x * F x))
    (hC : ∀ x, |F x| ≤ C) : |∫ x, ψ x * F x| ≤ (∫ x, |ψ x|) * C := by
  have hψ : Integrable (fun x => |ψ x|) :=
    (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).abs
  have hh := norm_integral_le_of_norm_le (hψ.mul_const C)
    (Eventually.of_forall (fun x => show ‖ψ x * F x‖ ≤ |ψ x| * C by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)))
  simpa only [Real.norm_eq_abs, integral_mul_const] using hh

open scoped ContDiff in
/-- Three successive exact derivatives with continuous top derivative imply `C³`. -/
theorem contDiff_three_of_hasDerivAt (f f₁ f₂ f₃ : ℝ → ℝ)
    (h0 : ∀ q, HasDerivAt f (f₁ q) q) (h1 : ∀ q, HasDerivAt f₁ (f₂ q) q)
    (h2 : ∀ q, HasDerivAt f₂ (f₃ q) q) (h3 : Continuous f₃) : ContDiff ℝ 3 f := by
  have he0 : deriv f = f₁ := funext (fun q => (h0 q).deriv)
  have he1 : deriv f₁ = f₂ := funext (fun q => (h1 q).deriv)
  have he2 : deriv f₂ = f₃ := funext (fun q => (h2 q).deriv)
  have hc2 : ContDiff ℝ 1 f₂ := contDiff_one_iff_deriv.mpr
    ⟨fun q => (h2 q).differentiableAt, he2.symm ▸ h3⟩
  have hc1 : ContDiff ℝ 2 f₁ := by
    rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv, he1]
    refine ⟨fun q => (h1 q).differentiableAt, ?_, hc2⟩
    intro hh
    cases hh
  rw [show (3 : ℕ∞ω) = 2 + 1 from rfl, contDiff_succ_iff_deriv, he0]
  refine ⟨fun q => (h0 q).differentiableAt, ?_, hc1⟩
  intro hh
  cases hh

/-- Deterministic cutoff calculus on the note's doubled-width good event. -/
theorem responseCutoff_calculus_of_good {Ω : Type*}
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t r : ℝ) (hr : 0 < r)
    (h v : Plane →ᵇ ℝ) (ψ : TestFn) (ω : Ω)
    (hint : Integrable (fun p : Plane × Plane => heatKernel (2 * r) p.2) (Z 0 t ω))
    (hpos : 0 < shfPairing Z 0 t (fun _ => 1) (heatKernel r) ω) :
    ContDiff ℝ 3 (responseCutoff Z t r h v ψ ω) ∧
    (∀ q, HasDerivAt (responseCutoff Z t r h v ψ ω)
      (∫ x, ψ x * cutoffMean Z t r h v ω q x) q ∧
      HasDerivAt (deriv (responseCutoff Z t r h v ψ ω))
        (∫ x, ψ x * cutoffVariance Z t r h v ω q x) q ∧
      HasDerivAt (iteratedDeriv 2 (responseCutoff Z t r h v ψ ω))
        (∫ x, ψ x * cutoffThird Z t r h v ω q x) q ∧
      |iteratedDeriv 3 (responseCutoff Z t r h v ψ ω) q| ≤ 8 * (∫ x, |ψ x|) * ‖v‖ ^ 3) ∧
    (∀ q, Integrable (fun x => ψ x * cutoffMean Z t r h v ω q x) ∧
      Integrable (fun x => ψ x * cutoffVariance Z t r h v ω q x) ∧
      Integrable (fun x => ψ x * cutoffThird Z t r h v ω q x)) := by
  have hall := integrable_heat_shift hr hint
  have hd := cutoff_cumulant_derivs Z t r hr h v ω hall hpos
  have hb := cutoff_cumulant_bounds Z t r hr h v ω hall hpos
  have hi := integrable_testFn_cutoffCumulants Z t r hr h v ψ ω hint hpos
  let f₁ := fun q => ∫ x, ψ x * cutoffMean Z t r h v ω q x
  let f₂ := fun q => ∫ x, ψ x * cutoffVariance Z t r h v ω q x
  let f₃ := fun q => ∫ x, ψ x * cutoffThird Z t r h v ω q x
  have heq : responseCutoff Z t r h v ψ ω = fun q => ∫ x, ψ x *
      (Real.log (cutoffMoment Z t r h v ω 0 q x) - Real.log (cutoffMoment Z t r h v ω 0 0 x)) := by
    funext q
    simp only [responseCutoff, cutoffMoment, pow_zero, zero_mul, add_zero, mul_one]
  have h0 (q : ℝ) : HasDerivAt (responseCutoff Z t r h v ψ ω) (f₁ q) q := by
    rw [heq]
    exact hasDerivAt_integral_testFn ψ (fun u => (hi u).1) (fun u => (hi u).2.1)
      (fun u x => (hd u x).1) ‖v‖ (fun u x => (hb u x).2.1) q
  have h1 (q : ℝ) : HasDerivAt f₁ (f₂ q) q :=
    hasDerivAt_integral_testFn ψ (fun u => (hi u).2.1) (fun u => (hi u).2.2.1)
      (fun u x => (hd u x).2.1) (‖v‖ ^ 2) (fun u x =>
        (abs_of_nonneg (hb u x).2.2.1.1).trans_le (hb u x).2.2.1.2) q
  have h2 (q : ℝ) : HasDerivAt f₂ (f₃ q) q :=
    hasDerivAt_integral_testFn ψ (fun u => (hi u).2.2.1) (fun u => (hi u).2.2.2)
      (fun u x => (hd u x).2.2) (8 * ‖v‖ ^ 3) (fun u x => (hb u x).2.2.2) q
  have h3 : Continuous f₃ := by
    apply continuous_of_dominated (F := fun q x => ψ x * cutoffThird Z t r h v ω q x)
      (bound := fun x => |ψ x| * (8 * ‖v‖ ^ 3))
    · exact fun q => (hi q).2.2.2.aestronglyMeasurable
    · intro q
      exact Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hb q x).2.2.2 (abs_nonneg _))
    · exact (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).abs.mul_const _
    · exact Eventually.of_forall (fun x => continuous_const.mul
        (continuous_cutoffThird_q Z t r hr h v ω hall hpos x))
  have he1 : deriv (responseCutoff Z t r h v ψ ω) = f₁ := funext (fun q => (h0 q).deriv)
  have he2 : iteratedDeriv 2 (responseCutoff Z t r h v ψ ω) = f₂ := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, he1]
    exact funext (fun q => (h1 q).deriv)
  have he3 : iteratedDeriv 3 (responseCutoff Z t r h v ψ ω) = f₃ := by
    rw [iteratedDeriv_succ, he2]
    exact funext (fun q => (h2 q).deriv)
  refine ⟨contDiff_three_of_hasDerivAt _ f₁ f₂ f₃ h0 h1 h2 h3, ?_, ?_⟩
  · intro q
    refine ⟨h0 q, he1.symm ▸ h1 q, he2.symm ▸ h2 q, ?_⟩
    rw [he3]
    have hh := abs_integral_testFn_mul_le ψ (8 * ‖v‖ ^ 3) (hi q).2.2.2 (fun x => (hb q x).2.2.2)
    convert hh using 1
    ring
  · exact fun q => (hi q).2

/-- Proposition 4.1: almost surely the cutoff response is `C³`, with the exact
first two derivative integrals, integrability, and the uniform third derivative bound. -/
theorem responseCutoff_hasDerivAt (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (t r : ℝ) (ht : 0 < t) (hr : 0 < r) (h v : Plane →ᵇ ℝ) (ψ : TestFn) :
    ∀ᵐ ω ∂P,
      let m : ℕ → ℝ → Plane → ℝ := fun k q x =>
        shfPairing Z 0 t (fun y => Real.exp (h y + q * v y) * v y ^ k)
          (fun y => heatKernel r (y - x)) ω
      ContDiff ℝ 3 (responseCutoff Z t r h v ψ ω) ∧
      (∀ q, HasDerivAt (responseCutoff Z t r h v ψ ω)
        (∫ x, ψ x * (m 1 q x / m 0 q x)) q ∧
        HasDerivAt (deriv (responseCutoff Z t r h v ψ ω))
          (∫ x, ψ x * (m 2 q x / m 0 q x - (m 1 q x / m 0 q x) ^ 2)) q ∧
        |iteratedDeriv 3 (responseCutoff Z t r h v ψ ω) q| ≤ 8 * (∫ x, |ψ x|) * ‖v‖ ^ 3) ∧
      (∀ q, Integrable (fun x => ψ x * (m 1 q x / m 0 q x)) ∧
        Integrable (fun x => ψ x * (m 2 q x / m 0 q x - (m 1 q x / m 0 q x) ^ 2))) := by
  filter_upwards [ae_integrable_heat_end ϑ P Z hZ ht (by positivity : 0 < 2 * r) 0,
    ae_heat_end_pos ϑ P Z hZ ht hr] with ω hint hpos
  simp only [sub_zero] at hint
  have hc := responseCutoff_calculus_of_good Z t r hr h v ψ ω hint hpos
  refine ⟨hc.1, ?_, ?_⟩
  · intro q
    have hd := hc.2.1 q
    simpa only [cutoffMean, cutoffVariance, cutoffMoment] using
      And.intro hd.1 (And.intro hd.2.1 hd.2.2.2)
  · intro q
    have hi := hc.2.2 q
    simpa only [cutoffMean, cutoffVariance, cutoffMoment] using And.intro hi.1 hi.2.1

/-- The first two cutoff cumulants are the mean and variance of the polymer
starting-point law. -/
theorem cutoff_cumulants_eq_startingLaw {Ω : Type*}
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t r : ℝ) (hr : 0 < r)
    (h v : Plane →ᵇ ℝ) (ω : Ω)
    (hint : ∀ x, Integrable (fun p : Plane × Plane => heatKernel r (p.2 - x)) (Z 0 t ω))
    (hpos : 0 < shfPairing Z 0 t (fun _ => 1) (heatKernel r) ω) (q : ℝ) (x : Plane) :
    cutoffMean Z t r h v ω q x = (∫ y, v y ∂(startingLaw Z t r h v x q ω)) ∧
    cutoffVariance Z t r h v ω q x = ProbabilityTheory.variance v (startingLaw Z t r h v x q ω) := by
  let ν := cutoffBase Z t r h x ω
  let : IsFiniteMeasure ν := isFiniteMeasure_cutoffBase Z t r hr h x ω (hint x)
  let : NeZero ν := neZero_cutoffBase Z t r hr h x ω hint hpos
  have hm (k : ℕ) (u : ℝ) : tiltedMoment ν v k u = cutoffMoment Z t r h v ω k u x :=
    integral_cutoffBase Z t r hr h v x ω k u
  have hh := logMgf_derivs_eq_tilted ν v v.continuous.measurable ‖v‖
    (fun y => v.norm_coe_le_norm y) q
  simpa only [hm, cutoffMean, cutoffVariance, startingLaw, ν] using And.intro hh.1 hh.2.1

/-- Literal starting-law form of the cutoff derivative identities, with both
spatial integrands integrable. -/
theorem responseCutoff_deriv_eq_startingLaw (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (t r : ℝ) (ht : 0 < t) (hr : 0 < r) (h v : Plane →ᵇ ℝ) (ψ : TestFn) :
    ∀ᵐ ω ∂P, ∀ q,
      deriv (responseCutoff Z t r h v ψ ω) q =
        (∫ x, ψ x * ∫ y, v y ∂(startingLaw Z t r h v x q ω)) ∧
      iteratedDeriv 2 (responseCutoff Z t r h v ψ ω) q =
        (∫ x, ψ x * ProbabilityTheory.variance v (startingLaw Z t r h v x q ω)) ∧
      Integrable (fun x => ψ x * ∫ y, v y ∂(startingLaw Z t r h v x q ω)) ∧
      Integrable (fun x => ψ x * ProbabilityTheory.variance v (startingLaw Z t r h v x q ω)) := by
  filter_upwards [ae_integrable_heat_end ϑ P Z hZ ht (by positivity : 0 < 2 * r) 0,
    ae_heat_end_pos ϑ P Z hZ ht hr] with ω hint hpos
  simp only [sub_zero] at hint
  have hc := responseCutoff_calculus_of_good Z t r hr h v ψ ω hint hpos
  have he := cutoff_cumulants_eq_startingLaw Z t r hr h v ω (integrable_heat_shift hr hint) hpos
  intro q
  have hd := hc.2.1 q
  have hfirst := hd.1.deriv
  have hsecond : iteratedDeriv 2 (responseCutoff Z t r h v ψ ω) q =
      ∫ x, ψ x * cutoffVariance Z t r h v ω q x := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hd.2.1.deriv
  have hi := hc.2.2 q
  simpa only [(he q _).1, (he q _).2] using
    And.intro hfirst (And.intro hsecond (And.intro hi.1 hi.2.1))

/-- The cutoff response and its first two derivatives obey deterministic uniform
bounds on the good event; the second derivative is nonnegative for nonnegative tests.
Integrability of the spatial integrands is supplied by `integrable_testFn_cutoffCumulants`. -/
theorem responseCutoff_bounds_of_good {Ω : Type*}
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t r : ℝ) (hr : 0 < r)
    (h v : Plane →ᵇ ℝ) (ψ : TestFn) (ω : Ω)
    (hint : Integrable (fun p : Plane × Plane => heatKernel (2 * r) p.2) (Z 0 t ω))
    (hpos : 0 < shfPairing Z 0 t (fun _ => 1) (heatKernel r) ω) :
    ∀ q, |responseCutoff Z t r h v ψ ω q| ≤ (∫ x, |ψ x|) * ‖v‖ * |q| ∧
      |deriv (responseCutoff Z t r h v ψ ω) q| ≤ (∫ x, |ψ x|) * ‖v‖ ∧
      |iteratedDeriv 2 (responseCutoff Z t r h v ψ ω) q| ≤ (∫ x, |ψ x|) * ‖v‖ ^ 2 ∧
      ((∀ x, 0 ≤ ψ x) → 0 ≤ iteratedDeriv 2 (responseCutoff Z t r h v ψ ω) q) := by
  have hc := responseCutoff_calculus_of_good Z t r hr h v ψ ω hint hpos
  have hb := cutoff_cumulant_bounds Z t r hr h v ω (integrable_heat_shift hr hint) hpos
  have hi := integrable_testFn_cutoffCumulants Z t r hr h v ψ ω hint hpos
  intro q
  have hd := hc.2.1 q
  have hfirst := hd.1.deriv
  have hsecond : iteratedDeriv 2 (responseCutoff Z t r h v ψ ω) q =
      ∫ x, ψ x * cutoffVariance Z t r h v ω q x := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hd.2.1.deriv
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hh := abs_integral_testFn_mul_le ψ (‖v‖ * |q|) (hi q).1 (fun x => (hb q x).1)
    simpa only [responseCutoff, cutoffMoment, pow_zero, mul_one, zero_mul, add_zero, mul_assoc] using hh
  · rw [hfirst]
    exact abs_integral_testFn_mul_le ψ ‖v‖ (hi q).2.1 (fun x => (hb q x).2.1)
  · rw [hsecond]
    apply abs_integral_testFn_mul_le ψ (‖v‖ ^ 2) (hi q).2.2.1
    intro x
    rw [abs_of_nonneg (hb q x).2.2.1.1]
    exact (hb q x).2.2.1.2
  · intro hψ
    rw [hsecond]
    exact integral_nonneg (fun x => mul_nonneg (hψ x) (hb q x).2.2.1.1)

/-- The uniform cutoff bounds and convexity sign hold almost surely for each
positive smoothing width. -/
theorem responseCutoff_bounds (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (t r : ℝ) (ht : 0 < t) (hr : 0 < r) (h v : Plane →ᵇ ℝ) (ψ : TestFn) :
    ∀ᵐ ω ∂P, ∀ q, |responseCutoff Z t r h v ψ ω q| ≤ (∫ x, |ψ x|) * ‖v‖ * |q| ∧
      |deriv (responseCutoff Z t r h v ψ ω) q| ≤ (∫ x, |ψ x|) * ‖v‖ ∧
      |iteratedDeriv 2 (responseCutoff Z t r h v ψ ω) q| ≤ (∫ x, |ψ x|) * ‖v‖ ^ 2 ∧
      ((∀ x, 0 ≤ ψ x) → 0 ≤ iteratedDeriv 2 (responseCutoff Z t r h v ψ ω) q) := by
  filter_upwards [ae_integrable_heat_end ϑ P Z hZ ht (by positivity : 0 < 2 * r) 0,
    ae_heat_end_pos ϑ P Z hZ ht hr] with ω hint hpos
  simp only [sub_zero] at hint
  exact responseCutoff_bounds_of_good Z t r hr h v ψ ω hint hpos

end Critical2DKPZ.Extensions.Response
