/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Localizers
public import Critical2DKPZ.Definitions.TestFn
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Uniform derivative bounds for scaled smooth cutoffs -/

@[expose] public section

noncomputable section

open Filter
open MeasureTheory
open TopologicalSpace
open scoped SchwartzMap Topology

namespace Critical2DKPZ.Spectral

/-- A scaled copy of the canonical bump, equal to one on the ball of radius `n + 1`. -/
def scaledLocalizer (n : ℕ) : TestFn := by
  let a : ℝ := ((n : ℝ) + 1)⁻¹
  have ha : a ≠ 0 := by dsimp [a]; positivity
  let e : Plane ≃ₜ Plane := Homeomorph.smulOfNeZero a ha
  exact {
    toFun := fun x => Critical2DKPZ.localizer 0 (a • x)
    contDiff' := (Critical2DKPZ.localizer 0).contDiff.comp (by fun_prop)
    hasCompactSupport' := by
      have heq : (fun x : Plane => Critical2DKPZ.localizer 0 (a • x)) =
          (Critical2DKPZ.localizer 0) ∘ e := by
        funext x
        simp [e, Homeomorph.smulOfNeZero, Homeomorph.smul]
      rw [heq]
      exact (Critical2DKPZ.localizer 0).hasCompactSupport.comp_homeomorph e
    tsupport_subset' := fun _ _ => trivial }

/-- The scaled localizer is the unit localizer evaluated at the rescaled point. -/
@[simp] theorem scaledLocalizer_apply (n : ℕ) (x : Plane) :
    scaledLocalizer n x = Critical2DKPZ.localizer 0 (((n : ℝ) + 1)⁻¹ • x) := rfl

/-- The scaled localizer equals one on the indicated norm ball. -/
theorem scaledLocalizer_eq_one_of_norm_le (n : ℕ) {x : Plane}
    (hx : ‖x‖ ≤ (n : ℝ) + 1) : scaledLocalizer n x = 1 := by
  rw [scaledLocalizer_apply]
  apply Critical2DKPZ.localizer_eq_one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (by positivity))]
  calc
    ((n : ℝ) + 1)⁻¹ * ‖x‖ ≤ ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hx (le_of_lt (inv_pos.mpr (by positivity)))
    _ = 1 := by field_simp
    _ ≤ ((0 : ℕ) : ℝ) + 1 := by
      simpa only [Nat.cast_zero, zero_add] using (le_rfl : (1 : ℝ) ≤ 1)

/-- The derivatives of the scaled localizers are bounded uniformly in the scale, up to any fixed
order. -/
theorem exists_uniform_derivative_bound_scaledLocalizer (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n i, i ≤ m → ∀ x : Plane,
      ‖iteratedFDeriv ℝ i (scaledLocalizer n) x‖ ≤ K := by
  let χ : TestFn := Critical2DKPZ.localizer 0
  obtain ⟨K, hK, hbound⟩ :=
    χ.hasCompactSupport.exists_bound_iteratedFDeriv χ.contDiff m
  refine ⟨K, hK, fun n i hi x => ?_⟩
  let a : ℝ := ((n : ℝ) + 1)⁻¹
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    rw [inv_le_one₀ (by positivity)]
    linarith
  have hcomp :
      iteratedFDeriv ℝ i (scaledLocalizer n) x =
        a ^ i • iteratedFDeriv ℝ i χ (a • x) := by
    have heq : (scaledLocalizer n : Plane → ℝ) = fun y : Plane => χ (a • y) := by
      funext y
      simp [scaledLocalizer_apply, a, χ]
    rw [heq]
    rw [iteratedFDeriv_comp_const_smul a (χ.contDiff.of_le (by simp))]
  rw [hcomp, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ha i)]
  calc
    a ^ i * ‖iteratedFDeriv ℝ i χ (a • x)‖ ≤ 1 * K :=
      mul_le_mul (pow_le_one₀ ha ha1) (hbound i hi (a • x))
        (norm_nonneg _) zero_le_one
    _ = K := one_mul _

/-- Regard a scaled smooth cutoff as a Schwartz function. -/
noncomputable def scaledLocalizerSchwartz (n : ℕ) : SchwartzMap Plane ℝ :=
  (scaledLocalizer n).hasCompactSupport.toSchwartzMap (scaledLocalizer n).contDiff

/-- Cut off a Schwartz function using the scaled localizer. -/
noncomputable def scaledCutoffSchwartz (n : ℕ) (f : SchwartzMap Plane ℝ) :
    SchwartzMap Plane ℝ :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) (scaledLocalizerSchwartz n) f

/-- Cutting off a Schwartz function with the scaled localizer multiplies their values. -/
@[simp] theorem scaledCutoffSchwartz_apply (n : ℕ) (f : SchwartzMap Plane ℝ)
    (x : Plane) : scaledCutoffSchwartz n f x = scaledLocalizer n x * f x := by
  simp [scaledCutoffSchwartz, scaledLocalizerSchwartz]

/-- The compactly supported smooth cutoff of a real Schwartz function, as a test function. -/
def scaledCutoffTestFn (n : ℕ) (f : SchwartzMap Plane ℝ) : TestFn where
  toFun x := scaledLocalizer n x * f x
  contDiff' := (scaledLocalizer n).contDiff.mul (f.smooth ⊤)
  hasCompactSupport' := (scaledLocalizer n).hasCompactSupport.mul_right
  tsupport_subset' := fun _ _ => trivial

/-- The scaled cutoff test evaluates to the localizer times the Schwartz function. -/
@[simp] theorem scaledCutoffTestFn_apply (n : ℕ) (f : SchwartzMap Plane ℝ)
    (x : Plane) : scaledCutoffTestFn n f x = scaledLocalizer n x * f x := rfl


/-- Every fixed point eventually lies where the scaled cutoff equals one. -/
theorem eventually_scaledLocalizer_eq_one (x : Plane) :
    ∀ᶠ n : ℕ in atTop, scaledLocalizer n x = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
  filter_upwards [eventually_ge_atTop N] with n hn
  apply scaledLocalizer_eq_one_of_norm_le
  calc
    ‖x‖ ≤ (N : ℝ) := hN.le
    _ ≤ (n : ℝ) := by exact_mod_cast hn
    _ ≤ (n : ℝ) + 1 := le_add_of_nonneg_right zero_le_one

/-- Integration against a measure of temperate growth is continuous along the scaled compact
cutoffs of a Schwartz function. -/
theorem tendsto_integral_scaledCutoffTestFn (μ : Measure Plane)
    [μ.HasTemperateGrowth] (f : SchwartzMap Plane ℝ) :
    Tendsto (fun n : ℕ => ∫ x : Plane, scaledCutoffTestFn n f x ∂μ) atTop
      (𝓝 (∫ x : Plane, f x ∂μ)) := by
  let F : ℕ → Plane → ℝ := fun n x => scaledCutoffTestFn n f x
  let bound : Plane → ℝ := fun x => ‖f x‖
  have hbound : Integrable bound μ := by
    simpa only [bound] using f.integrable.norm
  have hmeas (n : ℕ) : AEStronglyMeasurable (F n) μ := by
    exact (scaledCutoffTestFn n f).continuous.measurable.aestronglyMeasurable
  have hdom (n : ℕ) : ∀ᵐ x : Plane ∂μ, ‖F n x‖ ≤ bound x := by
    filter_upwards [] with x
    dsimp [F, bound]
    rw [abs_mul]
    have hχnonneg :
        0 ≤ Critical2DKPZ.localizer 0 (((n : ℝ) + 1)⁻¹ • x) :=
      Critical2DKPZ.localizer_nonneg 0 _
    have hχle :
        Critical2DKPZ.localizer 0 (((n : ℝ) + 1)⁻¹ • x) ≤ 1 :=
      Critical2DKPZ.localizer_le_one 0 _
    rw [abs_of_nonneg hχnonneg]
    calc
      scaledLocalizer n x * |f x| ≤ 1 * |f x| :=
        mul_le_mul_of_nonneg_right hχle (abs_nonneg _)
      _ = |f x| := by rw [one_mul]
  have hpoint (x : Plane) :
      Tendsto (fun n : ℕ => F n x) atTop (𝓝 (f x)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_scaledLocalizer_eq_one x] with n hn
    change f x = scaledLocalizer n x * f x
    rw [hn, one_mul]
  exact tendsto_integral_of_dominated_convergence bound hmeas hbound hdom
    (ae_of_all μ hpoint)

/-- For each Schwartz seminorm, scaled cutoffs of a fixed Schwartz function have a uniform bound.
The constants are uniform in the cutoff scale. -/
theorem exists_uniform_seminorm_bound_scaledCutoffSchwartz (f : SchwartzMap Plane ℝ)
    (k m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n,
      SchwartzMap.seminorm ℝ k m (scaledCutoffSchwartz n f) ≤ B := by
  obtain ⟨K, hK, hKbound⟩ := exists_uniform_derivative_bound_scaledLocalizer m
  let c : ℕ → ℝ := fun j => Classical.choose (f.decay k j)
  have hcpos (j : ℕ) : 0 < c j := (Classical.choose_spec (f.decay k j)).1
  have hc (j : ℕ) (x : Plane) :
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ j f x‖ ≤ c j :=
    (Classical.choose_spec (f.decay k j)).2 x
  let Cf : ℝ := ∑ j ∈ Finset.range (m + 1), c j
  have hCf : 0 ≤ Cf := by
    dsimp [Cf]
    exact Finset.sum_nonneg fun j hj => (hcpos j).le
  have hc_le (j : ℕ) (hj : j ≤ m) : c j ≤ Cf := by
    dsimp [Cf]
    exact Finset.single_le_sum (fun q hq => (hcpos q).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  let B : ℝ := (m + 1 : ℝ) * 2 ^ m * K * Cf
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, fun n => SchwartzMap.seminorm_le_bound ℝ k m
    (scaledCutoffSchwartz n f) hB ?_⟩
  intro x
  have hmul := norm_iteratedFDeriv_mul_le
    (N := m) (n := m) ((scaledLocalizer n).contDiff.of_le (by simp))
    (f.smooth'.of_le (by simp)) x (by simp)
  have hfun :
      (scaledCutoffSchwartz n f : Plane → ℝ) =
        fun y => scaledLocalizer n y * f y := by
    funext y
    simp [scaledCutoffSchwartz_apply]
  have hsum :
      ‖iteratedFDeriv ℝ m (fun y : Plane => scaledLocalizer n y * f y) x‖ ≤
        ∑ j ∈ Finset.range (m + 1),
          (m.choose j : ℝ) *
            ‖iteratedFDeriv ℝ j (scaledLocalizer n) x‖ *
            ‖iteratedFDeriv ℝ (m - j) f x‖ := hmul
  have hterm (j : ℕ) (hj : j ∈ Finset.range (m + 1)) :
      ‖x‖ ^ k * ((m.choose j : ℝ) *
          ‖iteratedFDeriv ℝ j (scaledLocalizer n) x‖ *
          ‖iteratedFDeriv ℝ (m - j) f x‖) ≤
        (m.choose j : ℝ) * K * Cf := by
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hderiv : ‖iteratedFDeriv ℝ j (scaledLocalizer n) x‖ ≤ K :=
      hKbound n j hjm x
    have hdecay : ‖x‖ ^ k * ‖iteratedFDeriv ℝ (m - j) f x‖ ≤ c (m - j) :=
      hc (m - j) x
    have hindex : m - j ≤ m := Nat.sub_le _ _
    calc
      _ = (m.choose j : ℝ) *
          ‖iteratedFDeriv ℝ j (scaledLocalizer n) x‖ *
          (‖x‖ ^ k * ‖iteratedFDeriv ℝ (m - j) f x‖) := by ring
      _ ≤ (m.choose j : ℝ) * K * c (m - j) := by
        gcongr
      _ ≤ (m.choose j : ℝ) * K * Cf := by
        gcongr
        exact hc_le (m - j) hindex
  have hmul' :
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ m
          (fun y : Plane => scaledLocalizer n y * f y) x‖ ≤ B := by
    dsimp [B]
    calc
      _ ≤ ‖x‖ ^ k *
          (∑ j ∈ Finset.range (m + 1),
            (m.choose j : ℝ) *
              ‖iteratedFDeriv ℝ j (scaledLocalizer n) x‖ *
              ‖iteratedFDeriv ℝ (m - j) f x‖) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = ∑ j ∈ Finset.range (m + 1),
          ‖x‖ ^ k * ((m.choose j : ℝ) *
            ‖iteratedFDeriv ℝ j (scaledLocalizer n) x‖ *
            ‖iteratedFDeriv ℝ (m - j) f x‖) := by rw [Finset.mul_sum]
      _ ≤ ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * K * Cf :=
        Finset.sum_le_sum fun j hj => hterm j hj
      _ ≤ ∑ j ∈ Finset.range (m + 1), (2 ^ m : ℝ) * K * Cf := by
        gcongr with j hj
        exact_mod_cast Nat.choose_le_two_pow m j
      _ = (m + 1 : ℝ) * 2 ^ m * K * Cf := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  rw [hfun]
  exact hmul'

/-- The family of all scaled cutoffs of a fixed Schwartz function is bounded in Schwartz space. -/
theorem scaledCutoffSchwartz_isVonNBounded (f : SchwartzMap Plane ℝ) :
    Bornology.IsVonNBounded ℝ (Set.range fun n => scaledCutoffSchwartz n f) := by
  apply (schwartz_withSeminorms ℝ Plane ℝ).isVonNBounded_iff_seminorm_bounded.mpr
  intro ij
  obtain ⟨B, hB, hbound⟩ :=
    exists_uniform_seminorm_bound_scaledCutoffSchwartz f ij.1 ij.2
  refine ⟨B + 1, by linarith, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact lt_of_le_of_lt (hbound n) (by linarith)

end Critical2DKPZ.Spectral

end
