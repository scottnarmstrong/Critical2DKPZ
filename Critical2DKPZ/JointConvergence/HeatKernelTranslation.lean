/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Heat.Moments
public import Critical2DKPZ.Analysis.Heat.Semigroup
import Mathlib.Tactic

/-! # Translation continuity of the planar heat kernel in `L¹` -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Critical2DKPZ.JointConvergence

private theorem integral_norm_mul_heatKernel_le_sqrt {u : ℝ} (hu : 0 < u) :
    ∫ x : Plane, ‖x‖ * heatKernel u x ≤ (9 / 2) * Real.sqrt u := by
  have hsqrt : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hsq : Real.sqrt u * Real.sqrt u = u := by nlinarith [Real.sq_sqrt hu.le]
  have hsecond : Integrable (fun x : Plane => ‖x‖ ^ 2 * heatKernel u x) := by
    simpa using Critical2DKPZ.integrable_norm_pow_mul_heatKernel_even hu 1
  have hsecondBound := Critical2DKPZ.integral_norm_pow_mul_heatKernel_even_le hu 1
  have hsecondBound' : ∫ x : Plane, ‖x‖ ^ 2 * heatKernel u x ≤ 8 * u := by
    norm_num [Nat.factorial] at hsecondBound
    nlinarith [hsecondBound]
  have hkernel := Critical2DKPZ.integrable_heatKernel hu
  have hsecondScaled : Integrable (fun x : Plane => u⁻¹ * (‖x‖ ^ 2 * heatKernel u x)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsecond.const_mul (u⁻¹)
  have hbaseEq : (fun x : Plane => (1 + ‖x‖ ^ 2 / u) * heatKernel u x) =
      (fun x => heatKernel u x) + (fun x => u⁻¹ * (‖x‖ ^ 2 * heatKernel u x)) := by
    funext x
    change (1 + ‖x‖ ^ 2 * u⁻¹) * heatKernel u x =
      heatKernel u x + u⁻¹ * (‖x‖ ^ 2 * heatKernel u x)
    ring
  have hbase : Integrable (fun x : Plane => (1 + ‖x‖ ^ 2 / u) * heatKernel u x) := by
    rw [hbaseEq]
    exact hkernel.add (by simpa [mul_comm, mul_left_comm, mul_assoc] using hsecond.const_mul u⁻¹)
  have hmajorant : Integrable (fun x : Plane =>
      (Real.sqrt u / 2) * ((1 + ‖x‖ ^ 2 / u) * heatKernel u x)) :=
    hbase.const_mul (Real.sqrt u / 2)
  have hleft : Integrable (fun x : Plane => ‖x‖ * heatKernel u x) := by
    simpa using Critical2DKPZ.integrable_norm_pow_mul_heatKernel hu 1
  have hpoint (x : Plane) : ‖x‖ * heatKernel u x ≤
      (Real.sqrt u / 2) * ((1 + ‖x‖ ^ 2 / u) * heatKernel u x) := by
    have hdiff : Real.sqrt u / 2 * (1 + ‖x‖ ^ 2 / u) - ‖x‖ =
        (‖x‖ - Real.sqrt u) ^ 2 / (2 * Real.sqrt u) := by
      field_simp [hu.ne', hsqrt.ne']
      nlinarith [hsq]
    have hscalar : ‖x‖ ≤ Real.sqrt u / 2 * (1 + ‖x‖ ^ 2 / u) := by
      rw [← sub_nonneg, hdiff]
      positivity
    calc
      ‖x‖ * heatKernel u x ≤
          (Real.sqrt u / 2 * (1 + ‖x‖ ^ 2 / u)) * heatKernel u x :=
        mul_le_mul_of_nonneg_right hscalar (Critical2DKPZ.heatKernel_nonneg hu.le x)
      _ = (Real.sqrt u / 2) * ((1 + ‖x‖ ^ 2 / u) * heatKernel u x) := by ring
  have hineq := integral_mono hleft hmajorant hpoint
  have hbaseIntegral :
      ∫ x : Plane, (1 + ‖x‖ ^ 2 / u) * heatKernel u x =
        1 + u⁻¹ * ∫ x : Plane, ‖x‖ ^ 2 * heatKernel u x := by
    calc
      _ = ∫ x : Plane, heatKernel u x + u⁻¹ * (‖x‖ ^ 2 * heatKernel u x) := by
        rw [hbaseEq]
        rfl
      _ = _ := by
        rw [integral_add hkernel hsecondScaled, Critical2DKPZ.integral_heatKernel hu,
          integral_const_mul]
  calc
    _ ≤ (Real.sqrt u / 2) * (1 + u⁻¹ * ∫ x : Plane, ‖x‖ ^ 2 * heatKernel u x) := by
      calc
        _ ≤ ∫ x : Plane, (Real.sqrt u / 2) *
            ((1 + ‖x‖ ^ 2 / u) * heatKernel u x) := hineq
        _ = (Real.sqrt u / 2) *
            ∫ x : Plane, (1 + ‖x‖ ^ 2 / u) * heatKernel u x := integral_const_mul _ _
        _ = _ := by rw [hbaseIntegral]
    _ ≤ (Real.sqrt u / 2) * 9 := by
      apply mul_le_mul_of_nonneg_left
      · have hterm : u⁻¹ * (∫ x : Plane, ‖x‖ ^ 2 * heatKernel u x) ≤ 8 := by
          calc
            _ = (∫ x : Plane, ‖x‖ ^ 2 * heatKernel u x) / u := by field_simp [hu.ne']
            _ ≤ 8 := (div_le_iff₀ hu).2 (by nlinarith [hsecondBound'])
        linarith
      · positivity
    _ = (9 / 2) * Real.sqrt u := by ring

private theorem abs_exp_neg_sub_le {a b : ℝ} :
    |Real.exp (-a) - Real.exp (-b)| ≤
      |a - b| * (Real.exp (-a) + Real.exp (-b)) := by
  have ordered {a b : ℝ} (hab : a ≤ b) :
      |Real.exp (-a) - Real.exp (-b)| ≤
        |a - b| * (Real.exp (-a) + Real.exp (-b)) := by
    have hmono : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
    have hsmall : 1 - Real.exp (-(b - a)) ≤ b - a := by
      have h := Real.add_one_le_exp (-(b - a))
      linarith
    have hexp : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
      rw [show -b = -a + -(b - a) by ring, Real.exp_add]
    have hrepr : |Real.exp (-a) - Real.exp (-b)| =
        Real.exp (-a) * (1 - Real.exp (-(b - a))) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hmono), hexp]
      ring
    calc
      |Real.exp (-a) - Real.exp (-b)| =
          Real.exp (-a) * (1 - Real.exp (-(b - a))) := hrepr
      _ ≤ Real.exp (-a) * (b - a) := by gcongr
      _ ≤ (b - a) * (Real.exp (-a) + Real.exp (-b)) := by
        nlinarith [Real.exp_pos (-a), Real.exp_pos (-b)]
      _ = |a - b| * (Real.exp (-a) + Real.exp (-b)) := by
        rw [abs_of_nonpos (sub_nonpos.mpr hab)]
        ring
  rcases le_total a b with hab | hba
  · exact ordered hab
  · have h := ordered hba
    simpa [abs_sub_comm, add_comm] using h

/-- The integrand in the heat-kernel translation estimate is integrable. -/
theorem integrable_abs_heatKernel_sub {δ : ℝ} (hδ : 0 < δ) (x x' : Plane) :
    Integrable (fun y : Plane => |heatKernel δ (y - x) - heatKernel δ (y - x')|) := by
  have h1 : Integrable (fun y : Plane => heatKernel δ (y - x)) :=
    (Critical2DKPZ.integrable_heatKernel hδ).comp_sub_right x
  have h2 : Integrable (fun y : Plane => heatKernel δ (y - x')) :=
    (Critical2DKPZ.integrable_heatKernel hδ).comp_sub_right x'
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using (h1.sub h2).norm

private theorem integrable_integral_norm_translated_heatKernel_le {δ : ℝ} (hδ : 0 < δ)
    (a b : Plane) : Integrable (fun y : Plane => ‖y - a‖ * heatKernel δ (y - b)) ∧
      ∫ y : Plane, ‖y - a‖ * heatKernel δ (y - b) ≤
        (9 / 2) * Real.sqrt δ + ‖a - b‖ := by
  let d : ℝ := ‖a - b‖
  let F : Plane → ℝ := fun z => ‖z + (b - a)‖ * heatKernel δ z
  have hkernel := Critical2DKPZ.integrable_heatKernel hδ
  have hfirst : Integrable (fun z : Plane => ‖z‖ * heatKernel δ z) := by
    simpa using Critical2DKPZ.integrable_norm_pow_mul_heatKernel hδ 1
  have hconst : Integrable (fun z : Plane => d * heatKernel δ z) := hkernel.const_mul d
  have hmajor : Integrable (fun z : Plane => ‖z‖ * heatKernel δ z + d * heatKernel δ z) :=
    hfirst.add hconst
  have hFint : Integrable F := by
    apply hmajor.mono_nonneg
    · dsimp [F]
      fun_prop
    · exact Filter.Eventually.of_forall fun z =>
        mul_nonneg (norm_nonneg _) (Critical2DKPZ.heatKernel_nonneg hδ.le z)
    · filter_upwards [] with z
      have hg : 0 ≤ heatKernel δ z := Critical2DKPZ.heatKernel_nonneg hδ.le z
      have hnorm : ‖z + (b - a)‖ ≤ ‖z‖ + d := by
        dsimp [d]
        calc
          ‖z + (b - a)‖ ≤ ‖z‖ + ‖b - a‖ := norm_add_le _ _
          _ = ‖z‖ + ‖a - b‖ := by rw [norm_sub_rev]
      calc
        ‖z + (b - a)‖ * heatKernel δ z ≤ (‖z‖ + d) * heatKernel δ z :=
          mul_le_mul_of_nonneg_right hnorm hg
        _ = ‖z‖ * heatKernel δ z + d * heatKernel δ z := by ring
  have hshift : (fun y : Plane => ‖y - a‖ * heatKernel δ (y - b)) = fun y => F (y - b) := by
    funext y
    dsimp [F]
    congr 1
    congr 1
    abel
  have horiginal : Integrable (fun y : Plane => ‖y - a‖ * heatKernel δ (y - b)) := by
    rw [hshift]
    exact hFint.comp_sub_right b
  have hshiftIntegral :
      ∫ y : Plane, ‖y - a‖ * heatKernel δ (y - b) = ∫ z : Plane, F z := by
    rw [hshift]
    exact integral_sub_right_eq_self F b
  have hFbound : ∫ z : Plane, F z ≤ (9 / 2) * Real.sqrt δ + d := by
    have hpoint (z : Plane) : F z ≤ ‖z‖ * heatKernel δ z + d * heatKernel δ z := by
      dsimp [F]
      have hg := Critical2DKPZ.heatKernel_nonneg hδ.le z
      have hnorm : ‖z + (b - a)‖ ≤ ‖z‖ + d := by
        dsimp [d]
        calc
          ‖z + (b - a)‖ ≤ ‖z‖ + ‖b - a‖ := norm_add_le _ _
          _ = ‖z‖ + ‖a - b‖ := by rw [norm_sub_rev]
      calc
        _ ≤ (‖z‖ + d) * heatKernel δ z := mul_le_mul_of_nonneg_right hnorm hg
        _ = _ := by ring
    have hmajorInt := integral_mono hFint hmajor hpoint
    calc
      _ ≤ ∫ z : Plane, ‖z‖ * heatKernel δ z + d * heatKernel δ z := hmajorInt
      _ = (∫ z : Plane, ‖z‖ * heatKernel δ z) + d * (∫ z : Plane, heatKernel δ z) := by
        rw [integral_add hfirst hconst, integral_const_mul]
      _ ≤ (9 / 2) * Real.sqrt δ + d := by
        rw [Critical2DKPZ.integral_heatKernel hδ]
        linarith [integral_norm_mul_heatKernel_le_sqrt hδ]
  refine ⟨horiginal, ?_⟩
  rw [hshiftIntegral]
  simpa [d] using hFbound

private theorem abs_heatExponent_sub_le {δ : ℝ} (hδ : 0 < δ) (u v : Plane) :
    |(2 * δ)⁻¹ * ‖u‖ ^ 2 - (2 * δ)⁻¹ * ‖v‖ ^ 2| ≤
      ‖u - v‖ * (‖u‖ + ‖v‖) / (2 * δ) := by
  have hnormdiff : |‖u‖ - ‖v‖| ≤ ‖u - v‖ := abs_norm_sub_norm_le u v
  have hsum : 0 ≤ ‖u‖ + ‖v‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsq : ‖u‖ ^ 2 - ‖v‖ ^ 2 = (‖u‖ - ‖v‖) * (‖u‖ + ‖v‖) := by ring
  have hfactor : |‖u‖ ^ 2 - ‖v‖ ^ 2| = |‖u‖ - ‖v‖| * (‖u‖ + ‖v‖) := by
    rw [hsq, abs_mul, abs_of_nonneg hsum]
  calc
    |(2 * δ)⁻¹ * ‖u‖ ^ 2 - (2 * δ)⁻¹ * ‖v‖ ^ 2| =
        (2 * δ)⁻¹ * |‖u‖ ^ 2 - ‖v‖ ^ 2| := by
          rw [← mul_sub, abs_mul, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
    _ = (2 * δ)⁻¹ * (|‖u‖ - ‖v‖| * (‖u‖ + ‖v‖)) := by rw [hfactor]
    _ ≤ (2 * δ)⁻¹ * (‖u - v‖ * (‖u‖ + ‖v‖)) := by
      gcongr
    _ = ‖u - v‖ * (‖u‖ + ‖v‖) / (2 * δ) := by ring

/-- The planar heat kernel satisfies an `L¹` spatial-translation bound proportional to distance divided by the square root of time. -/
theorem integral_abs_heatKernel_sub_le : ∃ C : ℝ, ∀ δ : ℝ, 0 < δ → ∀ x x' : Plane,
    ∫ y, |heatKernel δ (y - x) - heatKernel δ (y - x')| ≤
      C * ‖x - x'‖ / Real.sqrt δ := by
  refine ⟨10, fun δ hδ x x' => ?_⟩
  let d : ℝ := ‖x - x'‖
  let K₁ : Plane → ℝ := fun y => heatKernel δ (y - x)
  let K₂ : Plane → ℝ := fun y => heatKernel δ (y - x')
  let R : Plane → ℝ := fun y => ‖y - x‖
  let S : Plane → ℝ := fun y => ‖y - x'‖
  let q : Plane → ℝ := fun y => (R y + S y) * (K₁ y + K₂ y)
  have hsqrtpos : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hsqrtsq : Real.sqrt δ * Real.sqrt δ = δ := by
    nlinarith [Real.sq_sqrt hδ.le]
  have h11 := integrable_integral_norm_translated_heatKernel_le hδ x x
  have h12 := integrable_integral_norm_translated_heatKernel_le hδ x x'
  have h21 := integrable_integral_norm_translated_heatKernel_le hδ x' x
  have h22 := integrable_integral_norm_translated_heatKernel_le hδ x' x'
  have h11bound : ∫ y : Plane, R y * K₁ y ≤ (9 / 2) * Real.sqrt δ := by
    simpa [R, K₁] using h11.2
  have h12bound : ∫ y : Plane, R y * K₂ y ≤ (9 / 2) * Real.sqrt δ + d := by
    simpa [R, K₂, d] using h12.2
  have h21bound : ∫ y : Plane, S y * K₁ y ≤ (9 / 2) * Real.sqrt δ + d := by
    simpa [S, K₁, d, norm_sub_rev] using h21.2
  have h22bound : ∫ y : Plane, S y * K₂ y ≤ (9 / 2) * Real.sqrt δ := by
    simpa [S, K₂] using h22.2
  have hqeq : q = fun y => R y * K₁ y + (R y * K₂ y + (S y * K₁ y + S y * K₂ y)) := by
    funext y
    dsimp [q]
    ring
  have hqint : Integrable q := by
    rw [hqeq]
    exact h11.1.add (h12.1.add (h21.1.add h22.1))
  have hqbound : ∫ y : Plane, q y ≤ 18 * Real.sqrt δ + 2 * d := by
    have hqIntegral₁ := integral_add h11.1 (h12.1.add (h21.1.add h22.1))
    have hqIntegral₂ := integral_add h12.1 (h21.1.add h22.1)
    have hqIntegral₃ := integral_add h21.1 h22.1
    calc
      ∫ y : Plane, q y = (∫ y, R y * K₁ y) +
          (∫ y, R y * K₂ y + (S y * K₁ y + S y * K₂ y)) := by
        rw [hqeq]
        simpa [R, K₁, K₂, S] using hqIntegral₁
      _ = (∫ y, R y * K₁ y) +
          ((∫ y, R y * K₂ y) + (∫ y, S y * K₁ y + S y * K₂ y)) := by
        simpa [R, K₁, K₂, S] using
          congrArg (fun z : ℝ => (∫ y, R y * K₁ y) + z) hqIntegral₂
      _ = (∫ y, R y * K₁ y) +
          ((∫ y, R y * K₂ y) + ((∫ y, S y * K₁ y) + ∫ y, S y * K₂ y)) := by
        simpa [R, K₁, K₂, S] using
          congrArg (fun z : ℝ => (∫ y, R y * K₁ y) + ((∫ y, R y * K₂ y) + z)) hqIntegral₃
      _ ≤ 18 * Real.sqrt δ + 2 * d := by linarith [h11bound, h12bound, h21bound, h22bound]
  have hdiffint := integrable_abs_heatKernel_sub hδ x x'
  have hmass₁ : ∫ y : Plane, K₁ y = 1 := by
    simpa [K₁] using Critical2DKPZ.integral_heatKernel_sub hδ x
  have hmass₂ : ∫ y : Plane, K₂ y = 1 := by
    simpa [K₂] using Critical2DKPZ.integral_heatKernel_sub hδ x'
  have hsumint : Integrable (fun y : Plane => K₁ y + K₂ y) := by
    exact ((Critical2DKPZ.integrable_heatKernel hδ).comp_sub_right x).add
      ((Critical2DKPZ.integrable_heatKernel hδ).comp_sub_right x')
  have hk₁ (y : Plane) : 0 ≤ K₁ y := by
    dsimp [K₁]
    exact Critical2DKPZ.heatKernel_nonneg hδ.le _
  have hk₂ (y : Plane) : 0 ≤ K₂ y := by
    dsimp [K₂]
    exact Critical2DKPZ.heatKernel_nonneg hδ.le _
  have htrivial : ∫ y : Plane, |K₁ y - K₂ y| ≤ 2 := by
    calc
      _ ≤ ∫ y : Plane, K₁ y + K₂ y := integral_mono hdiffint hsumint (fun y => by
        rw [abs_le]
        constructor <;> linarith [hk₁ y, hk₂ y])
      _ = 2 := by rw [integral_add ((Critical2DKPZ.integrable_heatKernel hδ).comp_sub_right x)
        ((Critical2DKPZ.integrable_heatKernel hδ).comp_sub_right x'), hmass₁, hmass₂]; norm_num
  have hpoint (y : Plane) : |K₁ y - K₂ y| ≤ d / (2 * δ) * q y := by
      let a : ℝ := (2 * δ)⁻¹ * ‖y - x‖ ^ 2
      let b : ℝ := (2 * δ)⁻¹ * ‖y - x'‖ ^ 2
      let c : ℝ := (2 * Real.pi * δ)⁻¹
      have hc : 0 ≤ c := by dsimp [c]; positivity
      have ha : 0 ≤ a := by dsimp [a]; positivity
      have hb : 0 ≤ b := by dsimp [b]; positivity
      have hKa : K₁ y = c * Real.exp (-a) := by
        dsimp [K₁, c, a]
        rw [Critical2DKPZ.heatKernel_eq_exp δ (y - x)]
        congr 1
        ring_nf
      have hKb : K₂ y = c * Real.exp (-b) := by
        dsimp [K₂, c, b]
        rw [Critical2DKPZ.heatKernel_eq_exp δ (y - x')]
        congr 1
        ring_nf
      have hAB : |a - b| ≤ d * (R y + S y) / (2 * δ) := by
        have hxy : (y - x) - (y - x') = x' - x := by abel
        calc
          |a - b| ≤ ‖(y - x) - (y - x')‖ *
              (‖y - x‖ + ‖y - x'‖) / (2 * δ) := by
                dsimp [a, b]
                exact abs_heatExponent_sub_le hδ (y - x) (y - x')
          _ = d * (R y + S y) / (2 * δ) := by
                dsimp [a, b, R, S, d]
                rw [hxy, norm_sub_rev]
      calc
        |K₁ y - K₂ y| = c * |Real.exp (-a) - Real.exp (-b)| := by
          rw [hKa, hKb, ← mul_sub, abs_mul, abs_of_nonneg hc]
        _ ≤ c * (|a - b| * (Real.exp (-a) + Real.exp (-b))) := by
          exact mul_le_mul_of_nonneg_left (abs_exp_neg_sub_le) hc
        _ ≤ c * ((d * (R y + S y) / (2 * δ)) *
            (Real.exp (-a) + Real.exp (-b))) := by gcongr
        _ = d / (2 * δ) * q y := by
          calc
            _ = d / (2 * δ) * ((R y + S y) *
                (c * Real.exp (-a) + c * Real.exp (-b))) := by ring
            _ = d / (2 * δ) * q y := by rw [← hKa, ← hKb]
  have hbound : ∫ y : Plane, |K₁ y - K₂ y| ≤ 10 * d / Real.sqrt δ := by
    by_cases hsmall : d ≤ Real.sqrt δ
    · have hmajorint : Integrable (fun y : Plane => d / (2 * δ) * q y) :=
        hqint.const_mul (d / (2 * δ))
      have hint := integral_mono hdiffint hmajorint hpoint
      have hcoef : 0 ≤ d / (2 * δ) := by positivity
      calc
        _ ≤ ∫ y : Plane, d / (2 * δ) * q y := hint
        _ = d / (2 * δ) * ∫ y : Plane, q y := integral_const_mul _ _
        _ ≤ d / (2 * δ) * (18 * Real.sqrt δ + 2 * d) :=
          mul_le_mul_of_nonneg_left hqbound hcoef
        _ ≤ d / (2 * δ) * (20 * Real.sqrt δ) := by
          apply mul_le_mul_of_nonneg_left _ hcoef
          nlinarith [hsmall]
        _ = 10 * d / Real.sqrt δ := by
          field_simp [hδ.ne', hsqrtpos.ne']
          nlinarith [hsqrtsq]
    · have hlarge : Real.sqrt δ ≤ d := le_of_not_ge hsmall
      calc
        _ ≤ 2 := htrivial
        _ ≤ 10 * d / Real.sqrt δ := by
          rw [le_div_iff₀ hsqrtpos]
          nlinarith
  simpa [d] using hbound

end Critical2DKPZ.JointConvergence

end
