/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.HeatKernel
public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.Definitions.ShfPairing
import Critical2DKPZ.Analysis.Heat.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Moments.Variance
import Critical2DKPZ.Extensions.GffTangent.Locality
import Critical2DKPZ.Extensions.GffTangent.FlowMartingale
import Critical2DKPZ.Extensions.GffTangent.ProfileIdentities
import Critical2DKPZ.SHF.Positivity.HeatStartLimit
import Critical2DKPZ.JointConvergence.HeatStartLogFieldConvergence
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic

/-!
# Semiconvexity of logarithmic heat convolutions

Normalizing two exponential integrals and applying convexity of the
exponential proves the log-Laplace interpolation inequality. The Gaussian
factor then gives the heat-convolution semiconvexity constant.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter ProbabilityTheory
open scoped InnerProductSpace
open scoped Topology BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.GffTangent

/-- Integral log-sum-exp interpolation, including zero convex weights.
Integrability and positivity are stated for each of the three integrals. -/
theorem profile_log_integral_exp_interpolate {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (u v : α → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hu : Integrable (fun y => Real.exp (u y)) μ)
    (hv : Integrable (fun y => Real.exp (v y)) μ)
    (hc : Integrable (fun y => Real.exp (a * u y + b * v y)) μ)
    (hU : 0 < ∫ y, Real.exp (u y) ∂μ) (hV : 0 < ∫ y, Real.exp (v y) ∂μ)
    (hC : 0 < ∫ y, Real.exp (a * u y + b * v y) ∂μ) :
    Real.log (∫ y, Real.exp (a * u y + b * v y) ∂μ) ≤
      a * Real.log (∫ y, Real.exp (u y) ∂μ) + b * Real.log (∫ y, Real.exp (v y) ∂μ) := by
  let U := ∫ y, Real.exp (u y) ∂μ
  let V := ∫ y, Real.exp (v y) ∂μ
  let L := a * Real.log U + b * Real.log V
  have hUp : 0 < U := hU
  have hVp : 0 < V := hV
  have hterm (y : α) : Real.exp (a * u y + b * v y - L) ≤
      a * (Real.exp (u y) / U) + b * (Real.exp (v y) / V) := by
    have h := convexOn_exp.2 (mem_univ (u y - Real.log U))
      (mem_univ (v y - Real.log V)) ha hb hab
    simp only [smul_eq_mul, Real.exp_sub, Real.exp_log hUp, Real.exp_log hVp] at h
    convert h using 1
    congr 1
    dsimp only [L]
    ring
  have hright : Integrable (fun y => a * (Real.exp (u y) / U) + b * (Real.exp (v y) / V)) μ :=
    ((hu.div_const U).const_mul a).add ((hv.div_const V).const_mul b)
  have hleft : Integrable (fun y => Real.exp (a * u y + b * v y - L)) μ := by
    simpa only [Real.exp_sub] using hc.div_const (Real.exp L)
  have hnorm : (∫ y, a * (Real.exp (u y) / U) + b * (Real.exp (v y) / V) ∂μ) = 1 := by
    rw [integral_add ((hu.div_const U).const_mul a) ((hv.div_const V).const_mul b),
      integral_const_mul, integral_const_mul, integral_div, integral_div]
    change a * (U / U) + b * (V / V) = 1
    rw [div_self hU.ne', div_self hV.ne', mul_one, mul_one, hab]
  have hbound := integral_mono hleft hright hterm
  rw [hnorm] at hbound
  simp_rw [Real.exp_sub] at hbound
  rw [integral_div, div_le_one (Real.exp_pos L)] at hbound
  have hlog := Real.log_le_log hC hbound
  rwa [Real.log_exp] at hlog

/-- Multiplication by the Gaussian quadratic factor turns the heat kernel
into the exponential of an affine function of its center. -/
theorem profile_heatKernel_affine_exp {s : ℝ} (hs : 0 < s) (x y : Plane) :
    Real.exp (⟪x, y⟫_ℝ / s - (‖y‖ ^ 2 / (2 * s) + Real.log (2 * Real.pi * s))) =
      Real.exp (‖x‖ ^ 2 / (2 * s)) * heatKernel s (x - y) := by
  have hden : 0 < 2 * Real.pi * s := by positivity
  have hinv : (2 * Real.pi * s)⁻¹ = Real.exp (-Real.log (2 * Real.pi * s)) := by
    rw [Real.exp_neg, Real.exp_log hden]
  rw [heatKernel, hinv]
  simp only [← Real.exp_add]
  congr 1
  rw [norm_sub_sq_real]
  field_simp
  ring

/-- Logarithmic heat convolutions are semiconvex with constant `s⁻¹`.
The measure need not be finite; heat integrability and positivity suffice. -/
theorem convexOn_log_heatConv_add_sq (μ : Measure Plane) {s : ℝ} (hs : 0 < s)
    (hint : ∀ x : Plane, Integrable (fun y => heatKernel s (x - y)) μ)
    (hpos : ∀ x : Plane, 0 < ∫ y, heatKernel s (x - y) ∂μ) :
    ConvexOn ℝ univ (fun x : Plane =>
      Real.log (∫ y, heatKernel s (x - y) ∂μ) + ‖x‖ ^ 2 / (2 * s)) := by
  let F := fun (x y : Plane) => ⟪x, y⟫_ℝ / s -
    (‖y‖ ^ 2 / (2 * s) + Real.log (2 * Real.pi * s))
  have hrepr (x : Plane) : (fun y => Real.exp (F x y)) =
      fun y => Real.exp (‖x‖ ^ 2 / (2 * s)) * heatKernel s (x - y) := by
    funext y
    exact profile_heatKernel_affine_exp hs x y
  have hInt (x : Plane) : Integrable (fun y => Real.exp (F x y)) μ := by
    rw [hrepr x]
    exact (hint x).const_mul _
  have hIntegral (x : Plane) : (∫ y, Real.exp (F x y) ∂μ) =
      Real.exp (‖x‖ ^ 2 / (2 * s)) * ∫ y, heatKernel s (x - y) ∂μ := by
    rw [hrepr x, integral_const_mul]
  have hPos (x : Plane) : 0 < ∫ y, Real.exp (F x y) ∂μ := by
    rw [hIntegral x]
    exact mul_pos (Real.exp_pos _) (hpos x)
  have hLog (x : Plane) : Real.log (∫ y, Real.exp (F x y) ∂μ) =
      Real.log (∫ y, heatKernel s (x - y) ∂μ) + ‖x‖ ^ 2 / (2 * s) := by
    rw [hIntegral x, Real.log_mul (Real.exp_pos _).ne' (hpos x).ne', Real.log_exp]
    ring
  refine ⟨convex_univ, ?_⟩
  intro x _ z _ a b ha hb hab
  have haffine (y : Plane) : F (a • x + b • z) y = a * F x y + b * F z y := by
    dsimp only [F]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    calc
      _ = (a * ⟪x, y⟫_ℝ + b * ⟪z, y⟫_ℝ) / s -
          (a + b) * (‖y‖ ^ 2 / (2 * s) + Real.log (2 * Real.pi * s)) := by rw [hab]; ring
      _ = _ := by ring
  have heq : (fun y => Real.exp (a * F x y + b * F z y)) =
      fun y => Real.exp (F (a • x + b • z) y) := by
    funext y
    rw [haffine]
  have hi : Integrable (fun y => Real.exp (a * F x y + b * F z y)) μ := heq.symm ▸ hInt _
  have hp : 0 < ∫ y, Real.exp (a * F x y + b * F z y) ∂μ := by rw [heq]; exact hPos _
  have h := profile_log_integral_exp_interpolate μ (F x) (F z) ha hb hab
    (hInt x) (hInt z) hi (hPos x) (hPos z) hp
  rw [heq] at h
  simp_rw [hLog] at h
  exact h



/-- Two variables within `σ` of a common center in `L²` differ by at most
`2σ`. -/
theorem profile_l2_difference_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : Ω → ℝ) (m : ℝ) {σ : ℝ} (hσ : 0 ≤ σ)
    (hX : eLpNorm (fun ω => X ω - m) 2 P ≤ ENNReal.ofReal σ)
    (hY : eLpNorm (fun ω => Y ω - m) 2 P ≤ ENNReal.ofReal σ) :
    eLpNorm (fun ω => X ω - Y ω) 2 P ≤ ENNReal.ofReal (2 * σ) := by
  have heq : (fun ω => X ω - Y ω) = (fun ω => X ω - m) - (fun ω => Y ω - m) := by
    funext ω
    change X ω - Y ω = (X ω - m) - (Y ω - m)
    ring
  rw [heq]
  calc
    _ ≤ eLpNorm (fun ω => X ω - m) 2 P + eLpNorm (fun ω => Y ω - m) 2 P :=
      eLpNorm_sub_le (by norm_num)
    _ ≤ ENNReal.ofReal σ + ENNReal.ofReal σ := add_le_add hX hY
    _ = _ := by rw [← ENNReal.ofReal_add hσ hσ]; congr 1; ring

/-- An `L²` bound from a majorant by two centered secants and a constant. -/
theorem profile_l2_secant_majorant {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : ℝ → Ω → ℝ) (D : Ω → ℝ)
    {h σ m d : ℝ} (hh : 0 < h) (hσ : 0 ≤ σ) (hd : 0 ≤ d)
    (hF : ∀ t, AEMeasurable (F t) P) (hD : AEMeasurable D P)
    (hcenter : ∀ t, eLpNorm (fun ω => F t ω - m) 2 P ≤ ENNReal.ofReal σ)
    (hpoint : ∀ᵐ ω ∂P, ‖D ω‖ ≤
      h⁻¹ * (|F h ω - F 0 ω| + |F (-h) ω - F 0 ω|) + d) :
    eLpNorm D 2 P ≤ ENNReal.ofReal (4 * σ / h + d) := by
  let U := fun ω => F h ω - F 0 ω
  let V := fun ω => F (-h) ω - F 0 ω
  have hU := profile_l2_difference_le P (F h) (F 0) m hσ (hcenter h) (hcenter 0)
  have hV := profile_l2_difference_le P (F (-h)) (F 0) m hσ (hcenter (-h)) (hcenter 0)
  have hUabs : eLpNorm (fun ω => |U ω|) 2 P = eLpNorm U 2 P := by
    simpa only [Real.norm_eq_abs] using eLpNorm_norm U ((hF h).sub (hF 0)).aestronglyMeasurable
  have hVabs : eLpNorm (fun ω => |V ω|) 2 P = eLpNorm V 2 P := by
    simpa only [Real.norm_eq_abs] using eLpNorm_norm V ((hF (-h)).sub (hF 0)).aestronglyMeasurable
  have hsum : eLpNorm ((fun ω => |U ω|) + (fun ω => |V ω|)) 2 P ≤ ENNReal.ofReal (4 * σ) := by
    calc
      _ ≤ eLpNorm (fun ω => |U ω|) 2 P + eLpNorm (fun ω => |V ω|) 2 P := eLpNorm_add_le (by norm_num)
      _ ≤ ENNReal.ofReal (2 * σ) + ENNReal.ofReal (2 * σ) := by
        rw [hUabs, hVabs]
        exact add_le_add hU hV
      _ = _ := by rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 2 * σ) (by positivity : 0 ≤ 2 * σ)]; congr 1; ring
  have hpoint' : ∀ᵐ ω ∂P, ‖D ω‖ ≤ h⁻¹ * (|U ω| + |V ω|) + d := hpoint
  have hnorm := eLpNorm_mono_ae_real hD.aestronglyMeasurable hpoint' (p := 2)
  have heq : (fun ω => h⁻¹ * (|U ω| + |V ω|) + d) =
      h⁻¹ • ((fun ω => |U ω|) + (fun ω => |V ω|)) + (fun _ => d) := by
    funext ω
    rfl
  rw [heq] at hnorm
  apply hnorm.trans
  calc
    _ ≤ eLpNorm (h⁻¹ • ((fun ω => |U ω|) + (fun ω => |V ω|))) 2 P +
        eLpNorm (fun _ : Ω => d) 2 P := eLpNorm_add_le (by norm_num)
    _ = ENNReal.ofReal h⁻¹ * eLpNorm ((fun ω => |U ω|) + (fun ω => |V ω|)) 2 P +
        ENNReal.ofReal d := by
      rw [eLpNorm_const_smul, eLpNorm_const' d (by norm_num) (by norm_num)]
      simp only [measure_univ, ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal_abs,
        abs_of_nonneg (inv_nonneg.mpr hh.le), abs_of_nonneg hd]
    _ ≤ ENNReal.ofReal h⁻¹ * ENNReal.ofReal (4 * σ) + ENNReal.ofReal d :=
      add_le_add (mul_le_mul_of_nonneg_left hsum (by positivity)) le_rfl
    _ = _ := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hh.le),
        ← ENNReal.ofReal_add (by positivity : 0 ≤ h⁻¹ * (4 * σ)) hd]
      congr 1
      ring


/-- The deterministic optimization of the secant estimate. -/
theorem profile_secant_optimisation {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    4 * a ^ 2 / (2 * a * b) + (2 * a * b) / (2 * b ^ 2) ≤ 4 * a / b := by
  calc
    _ = 3 * a / b := by field_simp; ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hb.le



/-- A variance bound supplies the `L²` norm of the centered variable. -/
theorem profile_centered_l2_le_of_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P)
    {σ : ℝ} (hσ : 0 ≤ σ) (hvar : ProbabilityTheory.variance X P ≤ σ ^ 2) :
    eLpNorm (fun ω => X ω - ∫ ω, X ω ∂P) 2 P ≤ ENNReal.ofReal σ := by
  have hm : MemLp (fun ω => X ω - ∫ ω, X ω ∂P) 2 P := hX.sub (memLp_const _)
  have heq : eLpNorm (fun ω => X ω - ∫ ω, X ω ∂P) 2 P =
      ENNReal.ofReal (Real.sqrt (∫ ω, (X ω - ∫ ω, X ω ∂P) ^ 2 ∂P)) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
      Real.sqrt_eq_rpow, one_div] using
      (MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hm)
  rw [heq]
  apply ENNReal.ofReal_le_ofReal
  apply Real.sqrt_le_iff.mpr
  exact ⟨hσ, by simpa only [ProbabilityTheory.variance_eq_integral hX.aemeasurable] using hvar⟩


/-- Translation preserves the semiconvexity constant. -/
theorem profile_semiconvex_translate {f : ℝ → ℝ} {s : ℝ}
    (hc : ConvexOn ℝ univ (fun t => f t + t ^ 2 / (2 * s))) (a : ℝ) :
    ConvexOn ℝ univ (fun t => f (t + a) + t ^ 2 / (2 * s)) := by
  have ht : ConvexOn ℝ univ (fun t => f (t + a) + (t + a) ^ 2 / (2 * s)) := by
    simpa only [preimage_univ, Function.comp_def] using hc.translate_left a
  have hl : ConvexOn ℝ univ (fun t => -(a / s) * t - a ^ 2 / (2 * s)) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ c d _ _ hcd
    simp only [smul_eq_mul]
    apply le_of_eq
    linear_combination (a ^ 2 / (2 * s)) * hcd
  convert ht.add hl using 1
  funext t
  change f (t + a) + t ^ 2 / (2 * s) =
    (f (t + a) + (t + a) ^ 2 / (2 * s)) + (-(a / s) * t - a ^ 2 / (2 * s))
  ring

/-- Finite secants satisfy the derivative majorant with an error proportional
to the increment size. No differentiability is needed. -/
theorem profile_semiconvex_increment_quotient_le {f : ℝ → ℝ} {s h δ : ℝ}
    (hs : 0 < s) (hh : 0 < h) (hδ : 0 < δ) (hδh : δ ≤ h)
    (hc : ConvexOn ℝ univ (fun t => f t + t ^ 2 / (2 * s))) :
    |(f δ - f 0) / δ| ≤
      h⁻¹ * (|f h - f 0| + |f (-h) - f 0|) + (h / (2 * s) + δ / (2 * s)) := by
  let D := (f δ - f 0) / δ + δ / (2 * s)
  have hu := (hc.monotoneOn_slope_gt (mem_univ 0))
    ⟨mem_univ δ, hδ⟩ ⟨mem_univ h, hh⟩ hδh
  have hl := hc.slope_mono_adjacent (mem_univ (-h)) (mem_univ δ) (by linarith) hδ
  have hU : D ≤ (f h - f 0) / h + h / (2 * s) := by
    convert hu using 1 <;>
      (simp only [D, slope, smul_eq_mul, vsub_eq_sub, zero_pow (by norm_num : 2 ≠ 0),
        zero_div, add_zero, sub_zero]; field_simp [hs.ne', hh.ne', hδ.ne']; ring)
  have hL : (f 0 - f (-h)) / h - h / (2 * s) ≤ D := by
    convert hl using 1 <;>
      (simp only [D, zero_pow (by norm_num : 2 ≠ 0), zero_div, add_zero,
        sub_zero, zero_sub, neg_neg, neg_sq]; field_simp [hs.ne', hh.ne', hδ.ne']; ring)
  have hP : (f h - f 0) / h ≤ |f h - f 0| / h :=
    div_le_div_of_nonneg_right (le_abs_self _) hh.le
  have hN : -(|f (-h) - f 0| / h) ≤ (f 0 - f (-h)) / h := by
    convert neg_le_neg (div_le_div_of_nonneg_right (le_abs_self (f (-h) - f 0)) hh.le) using 1
    ring
  have hP0 : 0 ≤ |f h - f 0| / h := by positivity
  have hN0 : 0 ≤ |f (-h) - f 0| / h := by positivity
  have hAbs : |D| ≤ h⁻¹ * (|f h - f 0| + |f (-h) - f 0|) + h / (2 * s) := by
    rw [inv_mul_eq_div, add_div, abs_le]
    constructor <;> linarith only [hL, hU, hP, hN, hP0, hN0]
  calc
    _ = |D - δ / (2 * s)| := by congr 1; dsimp only [D]; ring
    _ ≤ |D| + |δ / (2 * s)| := abs_sub _ _
    _ ≤ _ := by
      rw [abs_of_nonneg (by positivity : 0 ≤ δ / (2 * s))]
      linarith only [hAbs]

/-- The finite-increment version of the random secant estimate. -/
theorem profile_semiconvex_increment_l2_step {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : ℝ → Ω → ℝ)
    {s h δ σ m : ℝ} (hs : 0 < s) (hh : 0 < h) (hδ : 0 < δ) (hδh : δ ≤ h) (hσ : 0 ≤ σ)
    (hF : ∀ t, AEMeasurable (F t) P)
    (hcenter : ∀ t, eLpNorm (fun ω => F t ω - m) 2 P ≤ ENNReal.ofReal σ)
    (hconv : ∀ᵐ ω ∂P, ConvexOn ℝ univ (fun t => F t ω + t ^ 2 / (2 * s))) :
    eLpNorm (fun ω => F δ ω - F 0 ω) 2 P ≤
      ENNReal.ofReal (δ * (4 * σ / h + h / (2 * s) + δ / (2 * s))) := by
  let D := fun ω => (F δ ω - F 0 ω) / δ
  have hD : AEMeasurable D P := ((hF δ).sub (hF 0)).div_const δ
  have hb := profile_l2_secant_majorant P F D hh hσ
    (show 0 ≤ h / (2 * s) + δ / (2 * s) by positivity) hF hD hcenter
    (hconv.mono fun ω hc => profile_semiconvex_increment_quotient_le hs hh hδ hδh hc)
  have heq : (fun ω => F δ ω - F 0 ω) = δ • D := by
    funext ω
    change _ = δ * ((F δ ω - F 0 ω) / δ)
    field_simp
  rw [heq, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_pos hδ]
  calc
    _ ≤ ENNReal.ofReal δ * ENNReal.ofReal (4 * σ / h + (h / (2 * s) + δ / (2 * s))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [← ENNReal.ofReal_mul hδ.le]; congr 1; ring

/-- Subdivision removes the quadratic increment error, giving a global
`L²` increment estimate at any fixed secant length. -/
theorem profile_semiconvex_increment_l2_fixed_step {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : ℝ → Ω → ℝ)
    {s h r σ m : ℝ} (hs : 0 < s) (hh : 0 < h) (hr : 0 < r) (hσ : 0 ≤ σ)
    (hF : ∀ t, AEMeasurable (F t) P)
    (hcenter : ∀ t, eLpNorm (fun ω => F t ω - m) 2 P ≤ ENNReal.ofReal σ)
    (hconv : ∀ᵐ ω ∂P, ConvexOn ℝ univ (fun t => F t ω + t ^ 2 / (2 * s))) :
    eLpNorm (fun ω => F r ω - F 0 ω) 2 P ≤
      ENNReal.ofReal (r * (4 * σ / h + h / (2 * s))) := by
  let δ := fun n : ℕ => r * (1 / ((n : ℝ) + 1))
  let B := 4 * σ / h + h / (2 * s)
  have hδ (n : ℕ) : 0 < δ n := by dsimp only [δ]; positivity
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlim : Tendsto (fun n => ENNReal.ofReal (r * (B + δ n / (2 * s))))
      atTop (𝓝 (ENNReal.ofReal (r * B))) := by
    have ht : Tendsto (fun n => ENNReal.ofReal (r * (B + δ n / (2 * s))))
        atTop (𝓝 (ENNReal.ofReal (r * (B + 0 / (2 * s))))) :=
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_const_nhds.mul (tendsto_const_nhds.add (hδlim.div_const (2 * s))))
    simpa only [zero_div, add_zero] using ht
  apply ge_of_tendsto hlim
  filter_upwards [hδlim.eventually (eventually_lt_nhds hh)] with n hn
  have hNδ : ((n + 1 : ℕ) : ℝ) * δ n = r := by
    dsimp only [δ]
    rw [Nat.cast_add, Nat.cast_one]
    field_simp
  have hstep (k : ℕ) :
      eLpNorm (F (((k + 1 : ℕ) : ℝ) * δ n) - F ((k : ℝ) * δ n)) 2 P ≤
        ENNReal.ofReal (δ n * (B + δ n / (2 * s))) := by
    have hk := profile_semiconvex_increment_l2_step P (fun t => F (t + (k : ℝ) * δ n))
      hs hh (hδ n) hn.le hσ (fun t => hF _) (fun t => hcenter _)
      (hconv.mono fun ω hc => profile_semiconvex_translate hc ((k : ℝ) * δ n))
    have harg : δ n + (k : ℝ) * δ n = ((k : ℝ) + 1) * δ n := by ring
    change eLpNorm (fun ω => F (((k + 1 : ℕ) : ℝ) * δ n) ω - F ((k : ℝ) * δ n) ω) 2 P ≤
      ENNReal.ofReal (δ n * (4 * σ / h + h / (2 * s) + δ n / (2 * s)))
    simpa only [zero_add, harg, Nat.cast_add, Nat.cast_one] using hk
  have htel : (∑ k ∈ Finset.range (n + 1),
      (F (((k + 1 : ℕ) : ℝ) * δ n) - F ((k : ℝ) * δ n))) = F r - F 0 := by
    simpa only [Nat.cast_zero, zero_mul, hNδ] using
      Finset.sum_range_sub (fun k : ℕ => F ((k : ℝ) * δ n)) (n + 1)
  change eLpNorm (F r - F 0) 2 P ≤ _
  rw [← htel]
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        eLpNorm (F (((k + 1 : ℕ) : ℝ) * δ n) - F ((k : ℝ) * δ n)) 2 P :=
      eLpNorm_sum_le (by norm_num)
    _ ≤ ∑ _k ∈ Finset.range (n + 1), ENNReal.ofReal (δ n * (B + δ n / (2 * s))) :=
      Finset.sum_le_sum fun k _ => hstep k
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by dsimp only [B]; positivity),
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      congr 1
      rw [← mul_assoc, hNδ]

/-- A stationary-size semiconvex process is Lipschitz as an `L²`-valued
function, without a pathwise differentiability assumption. -/
theorem profile_semiconvex_increment_l2_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : ℝ → Ω → ℝ)
    {s r σ m : ℝ} (hs : 0 < s) (hr : 0 ≤ r) (hσ : 0 ≤ σ)
    (hF : ∀ t, AEMeasurable (F t) P)
    (hcenter : ∀ t, eLpNorm (fun ω => F t ω - m) 2 P ≤ ENNReal.ofReal σ)
    (hconv : ∀ᵐ ω ∂P, ConvexOn ℝ univ (fun t => F t ω + t ^ 2 / (2 * s))) :
    eLpNorm (fun ω => F r ω - F 0 ω) 2 P ≤ ENNReal.ofReal (4 * r * Real.sqrt σ / Real.sqrt s) := by
  rcases hr.eq_or_lt with hr0 | hrpos
  · subst r
    simp
  let σn := fun n : ℕ => σ + 1 / ((n : ℝ) + 1)
  have hσn (n : ℕ) : 0 < σn n := by dsimp only [σn]; positivity
  have hσle (n : ℕ) : σ ≤ σn n := le_add_of_nonneg_right (by positivity)
  have hlim : Tendsto σn atTop (𝓝 σ) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hnormlim : Tendsto (fun n => ENNReal.ofReal (4 * r * Real.sqrt (σn n) / Real.sqrt s))
      atTop (𝓝 (ENNReal.ofReal (4 * r * Real.sqrt σ / Real.sqrt s))) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((tendsto_const_nhds.mul (Real.continuous_sqrt.continuousAt.tendsto.comp hlim)).div_const _)
  apply ge_of_tendsto hnormlim
  apply Eventually.of_forall
  intro n
  have ha := Real.sqrt_pos.mpr (hσn n)
  have hb := Real.sqrt_pos.mpr hs
  have hstep := profile_semiconvex_increment_l2_fixed_step P F hs
    (show 0 < 2 * Real.sqrt (σn n) * Real.sqrt s by positivity) hrpos (hσn n).le hF
    (fun t => (hcenter t).trans (ENNReal.ofReal_le_ofReal (hσle n))) hconv
  apply hstep.trans
  apply ENNReal.ofReal_le_ofReal
  have hopt := mul_le_mul_of_nonneg_left (profile_secant_optimisation ha hb) hr
  simpa only [Real.sq_sqrt (hσn n).le, Real.sq_sqrt hs.le, mul_div_assoc, mul_comm,
    mul_left_comm, mul_assoc] using hopt

/-- Restriction to a line scales the semiconvexity parameter by the squared
length of its direction. -/
theorem profile_semiconvex_on_line {f : Plane → ℝ} {s : ℝ}
    (hc : ConvexOn ℝ univ (fun y => f y + ‖y‖ ^ 2 / (2 * s)))
    {x : Plane} (hx : x ≠ 0) :
    ConvexOn ℝ univ (fun t : ℝ => f (t • x) + t ^ 2 / (2 * (s / ‖x‖ ^ 2))) := by
  have h := hc.comp_linearMap (LinearMap.toSpanSingleton ℝ Plane x)
  simp only [preimage_univ, Function.comp_def, LinearMap.toSpanSingleton_apply] at h
  convert h using 1
  funext t
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  congr 1
  field_simp [norm_ne_zero_iff.mpr hx]

/-- Uniform centered `L²` control and planar semiconvexity give the spatial
increment bound needed by mean-zero testing. -/
theorem profile_semiconvex_spatial_increment_l2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Plane → Ω → ℝ)
    {s σ m : ℝ} (hs : 0 < s) (hσ : 0 ≤ σ)
    (hF : ∀ x, AEMeasurable (F x) P)
    (hcenter : ∀ x, eLpNorm (fun ω => F x ω - m) 2 P ≤ ENNReal.ofReal σ)
    (hconv : ∀ᵐ ω ∂P, ConvexOn ℝ univ (fun x => F x ω + ‖x‖ ^ 2 / (2 * s))) (x : Plane) :
    eLpNorm (fun ω => F x ω - F 0 ω) 2 P ≤
      ENNReal.ofReal ((4 * Real.sqrt σ / Real.sqrt s) * ‖x‖) := by
  by_cases hx : x = 0
  · subst x
    simp
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hseff : 0 < s / ‖x‖ ^ 2 := by positivity
  have h := profile_semiconvex_increment_l2_bound P (fun t => F (t • x))
    hseff (r := 1) zero_le_one hσ (fun t => hF _) (fun t => hcenter _)
    (hconv.mono fun ω hc => profile_semiconvex_on_line hc hx)
  simp only [one_smul, zero_smul, mul_one] at h
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  rw [Real.sqrt_div hs.le, Real.sqrt_sq (norm_nonneg x)]
  field_simp
  exact le_rfl

/-- The real `L²` norm is the square root of its square integral. -/
theorem profile_l2_norm_eq_sqrt_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (hX : MemLp X 2 P) :
    eLpNorm X 2 P = ENNReal.ofReal (Real.sqrt (∫ ω, X ω ^ 2 ∂P)) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
    Real.sqrt_eq_rpow, one_div] using
    (MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hX)

/-- A real `L²` norm bound controls its square integral. -/
theorem profile_sq_integral_le_of_l2_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (hX : MemLp X 2 P) {C : ℝ} (hC : 0 ≤ C)
    (hbound : eLpNorm X 2 P ≤ ENNReal.ofReal C) : (∫ ω, X ω ^ 2 ∂P) ≤ C ^ 2 := by
  rw [profile_l2_norm_eq_sqrt_integral hX] at hbound
  have hroot := (ENNReal.ofReal_le_ofReal_iff hC).mp hbound
  rw [← Real.sq_sqrt (integral_nonneg fun ω => sq_nonneg (X ω))]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 2

/-- Cauchy–Schwarz bounds a mixed moment by the common square-moment bound. -/
theorem profile_abs_mixed_moment_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    {C : ℝ} (hC : 0 ≤ C) (hXsq : (∫ ω, X ω ^ 2 ∂P) ≤ C ^ 2)
    (hYsq : (∫ ω, Y ω ^ 2 ∂P) ≤ C ^ 2) :
    |∫ ω, X ω * Y ω ∂P| ≤ C ^ 2 := by
  have hx : MemLp (fun ω => |X ω|) (ENNReal.ofReal (2 : ℝ)) P := by
    simpa only [ENNReal.ofReal_ofNat, Real.norm_eq_abs] using hX.norm
  have hy : MemLp (fun ω => |Y ω|) (ENNReal.ofReal (2 : ℝ)) P := by
    simpa only [ENNReal.ofReal_ofNat, Real.norm_eq_abs] using hY.norm
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := P) (p := (2 : ℝ)) (q := 2)
    Real.HolderConjugate.two_two (Eventually.of_forall fun ω => abs_nonneg (X ω))
      (Eventually.of_forall fun ω => abs_nonneg (Y ω)) hx hy
  have hcs' : (∫ ω, |X ω| * |Y ω| ∂P) ≤
      Real.sqrt (∫ ω, X ω ^ 2 ∂P) * Real.sqrt (∫ ω, Y ω ^ 2 ∂P) := by
    simpa only [Real.rpow_two, sq_abs, Real.sqrt_eq_rpow, one_div] using hcs
  calc
    _ ≤ ∫ ω, |X ω * Y ω| ∂P := abs_integral_le_integral_abs
    _ = ∫ ω, |X ω| * |Y ω| ∂P := by simp only [abs_mul]
    _ ≤ _ := hcs'.trans (by
      have hxroot := Real.sqrt_le_iff.mpr ⟨hC, hXsq⟩
      have hyroot := Real.sqrt_le_iff.mpr ⟨hC, hYsq⟩
      simpa only [pow_two] using mul_le_mul hxroot hyroot (Real.sqrt_nonneg _) hC)

/-- A weighted integral of a jointly measurable field has `L²` norm bounded
by the integral of the uniform norm majorant. Spatial and probabilistic
integrability are proved before applying Fubini. -/
theorem profile_uniform_l2_integral_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → Plane → ℝ}
    (hX : AEStronglyMeasurable (fun p : Ω × Plane => X p.1 p.2) (P.prod volume))
    (hmem : ∀ x, MemLp (fun ω => X ω x) 2 P) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, (∫ ω, X ω x ^ 2 ∂P) ≤ C ^ 2)
    {f : Plane → ℝ} (hf : Measurable f) (hfi : Integrable f) :
    (∀ᵐ ω ∂P, Integrable (fun x => f x * X ω x)) ∧
    MemLp (fun ω => ∫ x, f x * X ω x) 2 P ∧
    eLpNorm (fun ω => ∫ x, f x * X ω x) 2 P ≤ ENNReal.ofReal (C * ∫ x, |f x|) := by
  let L := fun ω => ∫ x, f x * X ω x
  let R := fun p : Plane × Plane => f p.1 * f p.2 * ∫ ω, X ω p.1 * X ω p.2 ∂P
  have hF := integrable_weighted_field P hX hmem hbound hf hfi
  have hFF := integrable_weighted_field_pair P hX hmem hbound hf hfi
  have hLs : AEStronglyMeasurable L P := hF.aestronglyMeasurable.integral_prod_right'
  have hL2 : MemLp L 2 P := by
    apply (memLp_two_iff_integrable_sq hLs).mpr
    apply hFF.integral_prod_left.congr
    filter_upwards [] with ω
    change (∫ p : Plane × Plane, (f p.1 * X ω p.1) * (f p.2 * X ω p.2)
      ∂(volume.prod volume)) = L ω ^ 2
    simpa only [L, pow_two] using integral_prod_mul (μ := volume) (ν := volume)
      (fun x => f x * X ω x) (fun x => f x * X ω x)
  have hR : Integrable R (volume.prod volume) := by
    apply hFF.integral_prod_right.congr
    filter_upwards [] with p
    change (∫ ω, (f p.1 * X ω p.1) * (f p.2 * X ω p.2) ∂P) = R p
    dsimp only [R]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with ω
    ring
  have hsq : (∫ ω, L ω ^ 2 ∂P) = ∫ p : Plane × Plane, R p ∂(volume.prod volume) := by
    calc
      _ = ∫ ω, (∫ p : Plane × Plane, (f p.1 * X ω p.1) * (f p.2 * X ω p.2)
          ∂(volume.prod volume)) ∂P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        simpa only [L, pow_two] using (integral_prod_mul (μ := volume) (ν := volume)
          (fun x => f x * X ω x) (fun x => f x * X ω x)).symm
      _ = _ := (integral_integral_swap hFF).trans (by
        apply integral_congr_ae
        filter_upwards [] with p
        dsimp only [R]
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with ω
        ring)
  have hmoment : (∫ ω, L ω ^ 2 ∂P) ≤ (C * ∫ x, |f x|) ^ 2 := by
    rw [hsq]
    calc
      _ ≤ ∫ p : Plane × Plane, (|f p.1| * |f p.2|) * C ^ 2 ∂(volume.prod volume) := by
        apply integral_mono hR ((hfi.abs.mul_prod hfi.abs).mul_const _)
        intro p
        dsimp only [R]
        calc
          _ ≤ |f p.1 * f p.2 * ∫ ω, X ω p.1 * X ω p.2 ∂P| := le_abs_self _
          _ = (|f p.1| * |f p.2|) * |∫ ω, X ω p.1 * X ω p.2 ∂P| := by rw [abs_mul, abs_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (profile_abs_mixed_moment_le P (hmem p.1) (hmem p.2) hC (hbound p.1) (hbound p.2))
            (by positivity)
      _ = _ := by
        rw [integral_mul_const, integral_prod_mul (μ := volume) (ν := volume)
          (fun x : Plane => |f x|) (fun x : Plane => |f x|)]
        ring
  refine ⟨hF.prod_right_ae, hL2, ?_⟩
  rw [profile_l2_norm_eq_sqrt_integral hL2]
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_iff.mpr
    ⟨mul_nonneg hC (integral_nonneg fun _ => abs_nonneg _), hmoment⟩)

/-- Mean-zero testing removes the random spatial constant. Stationarity,
semiconvexity and the one-point variance bound then control the tested field
by the first absolute spatial moment of the test function. -/
theorem l2_integral_bound_of_integral_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Plane → Ω → ℝ)
    {s σ : ℝ} (hs : 0 < s) (hσ : 0 ≤ σ)
    (hFjoint : AEStronglyMeasurable (fun p : Ω × Plane => F p.2 p.1) (P.prod volume))
    (hstationary : ∀ x, ProbabilityTheory.IdentDistrib (F x) (F 0) P P)
    (hF0 : MemLp (F 0) 2 P) (hvar : ProbabilityTheory.variance (F 0) P ≤ σ ^ 2)
    (hconv : ∀ᵐ ω ∂P, ConvexOn ℝ univ (fun x => F x ω + ‖x‖ ^ 2 / (2 * s)))
    {f : Plane → ℝ} (hf : Measurable f) (hfi : Integrable f)
    (hfw : Integrable (fun x => ‖x‖ * |f x|)) (hfzero : ∫ x, f x = 0) :
    eLpNorm (fun ω => ∫ x, f x * F x ω) 2 P ≤
      ENNReal.ofReal ((4 * Real.sqrt σ / Real.sqrt s) * ∫ x, ‖x‖ * |f x|) := by
  let C := 4 * Real.sqrt σ / Real.sqrt s
  let X := fun (ω : Ω) (x : Plane) => (F x ω - F 0 ω) / ‖x‖
  let g := fun x : Plane => f x * ‖x‖
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hmem (x : Plane) : MemLp (F x) 2 P := (hstationary x).memLp_iff.mpr hF0
  have hcenter (x : Plane) : eLpNorm (fun ω => F x ω - ∫ ω, F 0 ω ∂P) 2 P ≤ ENNReal.ofReal σ := by
    have heq := ((hstationary x).comp (measurable_id.sub_const (∫ ω, F 0 ω ∂P))).eLpNorm_eq 2
    simp only [Function.comp_def, id_eq] at heq
    rw [heq]
    exact profile_centered_l2_le_of_variance P hF0 hσ hvar
  have hinc (x : Plane) : eLpNorm (fun ω => F x ω - F 0 ω) 2 P ≤ ENNReal.ofReal (C * ‖x‖) :=
    profile_semiconvex_spatial_increment_l2 P F hs hσ (fun x => (hmem x).aemeasurable) hcenter hconv x
  have hXmem (x : Plane) : MemLp (fun ω => X ω x) 2 P := by
    convert ((hmem x).sub hF0).const_mul ‖x‖⁻¹ using 1
    funext ω
    change (F x ω - F 0 ω) / ‖x‖ = ‖x‖⁻¹ * (F x ω - F 0 ω)
    ring
  have hXnorm (x : Plane) : eLpNorm (fun ω => X ω x) 2 P ≤ ENNReal.ofReal C := by
    by_cases hx : x = 0
    · subst x
      simp [X]
    have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have heq : (fun ω => X ω x) = ‖x‖⁻¹ • (fun ω => F x ω - F 0 ω) := by
      funext ω
      change (F x ω - F 0 ω) / ‖x‖ = ‖x‖⁻¹ * (F x ω - F 0 ω)
      ring
    rw [heq, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
    calc
      _ ≤ ENNReal.ofReal ‖x‖⁻¹ * ENNReal.ofReal (C * ‖x‖) :=
        mul_le_mul_of_nonneg_left (hinc x) (by positivity)
      _ = _ := by rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg x))]; congr 1; field_simp
  have hXsq (x : Plane) : (∫ ω, X ω x ^ 2 ∂P) ≤ C ^ 2 :=
    profile_sq_integral_le_of_l2_bound (hXmem x) hC (hXnorm x)
  have hF0joint : AEStronglyMeasurable (fun p : Ω × Plane => F 0 p.1) (P.prod volume) :=
    hF0.aestronglyMeasurable.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_fst (μ := P) (ν := volume))
  have hXjoint : AEStronglyMeasurable (fun p : Ω × Plane => X p.1 p.2) (P.prod volume) := by
    convert (hFjoint.sub hF0joint).mul (measurable_snd.norm.aestronglyMeasurable.inv₀) using 1
    funext p
    change (F p.2 p.1 - F 0 p.1) / ‖p.2‖ = (F p.2 p.1 - F 0 p.1) * ‖p.2‖⁻¹
    rw [div_eq_mul_inv]
  have hg : Measurable g := hf.mul measurable_id.norm
  have hgiabs : Integrable (fun x => |g x|) := by
    convert hfw using 1
    funext x
    dsimp only [g]
    rw [abs_mul, abs_of_nonneg (norm_nonneg x), mul_comm]
  have hgi : Integrable g := hgiabs.mono' hg.aestronglyMeasurable
    (Eventually.of_forall fun x => le_of_eq (Real.norm_eq_abs _))
  obtain ⟨hpath, hLmem, hLnorm⟩ := profile_uniform_l2_integral_bound P hXjoint hXmem hC hXsq hg hgi
  have hproduct (ω : Ω) (x : Plane) : g x * X ω x = f x * (F x ω - F 0 ω) := by
    dsimp only [g, X]
    by_cases hx : x = 0
    · subst x
      simp
    · field_simp [norm_ne_zero_iff.mpr hx]
  have heq : (fun ω => ∫ x, f x * F x ω) =ᵐ[P] (fun ω => ∫ x, g x * X ω x) := by
    filter_upwards [hpath] with ω hω
    have hY : Integrable (fun x => f x * (F x ω - F 0 ω)) :=
      hω.congr (Eventually.of_forall fun x => hproduct ω x)
    calc
      _ = ∫ x, (f x * (F x ω - F 0 ω) + f x * F 0 ω) := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = (∫ x, f x * (F x ω - F 0 ω)) + (∫ x, f x) * F 0 ω := by
        rw [integral_add hY (hfi.mul_const (F 0 ω)), integral_mul_const]
      _ = ∫ x, f x * (F x ω - F 0 ω) := by rw [hfzero, zero_mul, add_zero]
      _ = _ := integral_congr_ae (Eventually.of_forall fun x => (hproduct ω x).symm)
  have hgint : (∫ x, |g x|) = ∫ x, ‖x‖ * |f x| := by
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp only [g]
    rw [abs_mul, abs_of_nonneg (norm_nonneg x), mul_comm]
  rw [eLpNorm_congr_ae heq]
  simpa only [hgint] using hLnorm

/-- A broader centered Gaussian dominates every translate of a narrower one. -/
theorem profile_heatKernel_shift_le {s : ℝ} (hs : 0 < s) (x y : Plane) :
    heatKernel s (y - x) ≤
      (2 * Real.exp (‖x‖ ^ 2 / (2 * s))) * heatKernel (2 * s) y := by
  have hn : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
    simpa only [sub_add_cancel] using norm_add_le (y - x) x
  have hsq : ‖y‖ ^ 2 ≤ 2 * ‖y - x‖ ^ 2 + 2 * ‖x‖ ^ 2 := by
    nlinarith only [hn, norm_nonneg y, norm_nonneg (y - x), norm_nonneg x,
      sq_nonneg (‖y - x‖ - ‖x‖)]
  have he : -‖y - x‖ ^ 2 / (2 * s) ≤ ‖x‖ ^ 2 / (2 * s) - ‖y‖ ^ 2 / (4 * s) := by
    apply (mul_le_mul_iff_of_pos_right (by positivity : 0 < 4 * s)).mp
    have h1 : (-‖y - x‖ ^ 2 / (2 * s)) * (4 * s) = -2 * ‖y - x‖ ^ 2 := by
      field_simp; ring
    have h2 : (‖x‖ ^ 2 / (2 * s) - ‖y‖ ^ 2 / (4 * s)) * (4 * s) =
        2 * ‖x‖ ^ 2 - ‖y‖ ^ 2 := by field_simp; ring
    rw [h1, h2]
    linarith only [hsq]
  calc
    _ ≤ (2 * Real.pi * s)⁻¹ *
        Real.exp (‖x‖ ^ 2 / (2 * s) - ‖y‖ ^ 2 / (4 * s)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)
    _ = _ := by
      rw [heatKernel, sub_eq_add_neg, Real.exp_add]
      have hexp : -(‖y‖ ^ 2 / (4 * s)) = -‖y‖ ^ 2 / (2 * (2 * s)) := by ring
      rw [hexp]
      field_simp

/-- One broader Gaussian integrability bound gives finite, positive heat
convolutions at every spatial center on the same measure. -/
theorem profile_heatConv_regular (μ : Measure Plane) {s : ℝ} (hs : 0 < s)
    (hwide : Integrable (heatKernel (2 * s)) μ)
    (hzero : 0 < ∫ y, heatKernel s (-y) ∂μ) :
    (∀ x : Plane, Integrable (fun y => heatKernel s (x - y)) μ) ∧
    (∀ x : Plane, 0 < ∫ y, heatKernel s (x - y) ∂μ) := by
  have hi (x : Plane) : Integrable (fun y => heatKernel s (x - y)) μ := by
    apply (hwide.const_mul (2 * Real.exp (‖x‖ ^ 2 / (2 * s)))).mono'
      (((continuous_heatKernel s).comp (continuous_const.sub continuous_id)).measurable.aestronglyMeasurable)
    filter_upwards [] with y
    change ‖heatKernel s (x - y)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg hs.le _)]
    simpa only [← neg_sub x y, heatKernel_neg] using profile_heatKernel_shift_le hs x y
  have hsupp (x : Plane) : Function.support (fun y => heatKernel s (x - y)) = univ := by
    ext y
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (heatKernel_pos hs _).ne'
  have hμ : 0 < μ univ := by
    have h0 : 0 < ∫ y, heatKernel s ((0 : Plane) - y) ∂μ := by simpa only [zero_sub] using hzero
    have := (integral_pos_iff_support_of_nonneg (fun y => heatKernel_nonneg hs.le _) (hi 0)).mp h0
    simpa only [hsupp] using this
  refine ⟨hi, fun x => ?_⟩
  apply (integral_pos_iff_support_of_nonneg (fun y => heatKernel_nonneg hs.le _) (hi x)).mpr
  simpa only [hsupp] using hμ

/-- Heat-start log fields are semiconvex simultaneously at every spatial center. -/
theorem profile_heatMass_ae_pos_semiconvex (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {a T : ℝ} (ha : 0 < a) (haT : a < T) :
    ∀ᵐ ω ∂P, (∀ x : Plane, 0 < shfPairing Z a T
      (fun y => heatKernel a (y - x)) (fun _ => 1) ω) ∧ ConvexOn ℝ univ (fun x : Plane =>
      Real.log (shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1) ω) +
        ‖x‖ ^ 2 / (2 * a)) := by
  have hwide := SHF.Positivity.isCriticalSHF_ae_integrable_heat_start ϑ P Z hZ
    ha.le haT (by positivity : 0 < 2 * a) (0 : Plane)
  have hp := heatMass_pos ϑ P Z hZ ha haT (0 : Plane)
  filter_upwards [hwide, hp] with ω hwide hp
  let μ := (Z a T ω).map Prod.fst
  have hmap (x : Plane) : (∫ y, heatKernel a (x - y) ∂μ) =
      shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1) ω := by
    change (∫ y, heatKernel a (x - y) ∂((Z a T ω).map Prod.fst)) = _
    have hf : Measurable (fun y : Plane => heatKernel a (x - y)) :=
      (measurable_heatKernel a).comp (measurable_const.sub measurable_id)
    rw [integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable]
    unfold shfPairing
    apply integral_congr_ae
    filter_upwards [] with p
    simp only [mul_one, ← neg_sub x p.1, heatKernel_neg]
  have hwide' : Integrable (heatKernel (2 * a)) μ := by
    apply (integrable_map_measure (measurable_heatKernel (2 * a)).aestronglyMeasurable
      measurable_fst.aemeasurable).mpr
    simpa only [sub_zero, Function.comp_def] using hwide
  have hp' : 0 < ∫ y, heatKernel a (-y) ∂μ := by
    simpa only [zero_sub] using (show 0 < ∫ y, heatKernel a ((0 : Plane) - y) ∂μ by rw [hmap]; exact hp)
  obtain ⟨hint, hpos⟩ := profile_heatConv_regular μ ha hwide' hp'
  refine ⟨fun x => ?_, ?_⟩
  · rw [← hmap x]
    exact hpos x
  · simpa only [hmap] using convexOn_log_heatConv_add_sq μ ha hint hpos

/-- Heat-start log fields are semiconvex simultaneously at every spatial center. -/
theorem profile_heatMass_ae_semiconvex (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {a T : ℝ} (ha : 0 < a) (haT : a < T) :
    ∀ᵐ ω ∂P, ConvexOn ℝ univ (fun x : Plane =>
      Real.log (shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1) ω) +
        ‖x‖ ^ 2 / (2 * a)) :=
  (profile_heatMass_ae_pos_semiconvex ϑ P Z hZ ha haT).mono (fun _ h => h.2)

/-- Spatial stationarity of each heat-start log field, obtained from the
SHF translation symmetry and uniqueness of its finite-dimensional laws. -/
theorem profile_heatMass_log_identDistrib (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {a T : ℝ} (ha : 0 < a) (haT : a < T) (x : Plane) :
    ProbabilityTheory.IdentDistrib
      (fun ω => Real.log (shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1) ω))
      (fun ω => Real.log (shfPairing Z a T (fun y => heatKernel a (y - 0)) (fun _ => 1) ω)) P P := by
  let Z' := fun s t ω => (Z s t ω).map (fun p => (p.1 + -x, p.2 + -x))
  have hZ' : IsCriticalSHF ϑ P Z' := (Provider.shf_symmetries ϑ P Z hZ).1 (-x)
  have hlaw := SHF.Symmetries.isCriticalSHF_fdd_eq ϑ P P Z Z' hZ hZ' 1
    (fun _ => a) (fun _ => T) (fun _ => ⟨ha.le, haT⟩)
  let Φ := fun μ : Fin 1 → Measure (Plane × Plane) =>
    Real.log (∫ p, heatKernel a p.1 ∂(μ 0))
  have hΦ : Measurable Φ :=
    ((measurable_integral_measure_real ((measurable_heatKernel a).comp measurable_fst)).log).comp
      (measurable_pi_apply 0)
  have hZm : Measurable (fun ω (_ : Fin 1) => Z a T ω) :=
    Measurable.of_eval (fun _ => hZ.1 a T ha.le haT)
  have hZ'm : Measurable (fun ω (_ : Fin 1) => Z' a T ω) :=
    Measurable.of_eval (fun _ => hZ'.1 a T ha.le haT)
  have hpush := congrArg (fun μ : Measure (Fin 1 → Measure (Plane × Plane)) => μ.map Φ) hlaw
  rw [Measure.map_map hΦ hZm, Measure.map_map hΦ hZ'm] at hpush
  have h0 (ω : Ω) : Φ (fun _ => Z a T ω) =
      Real.log (shfPairing Z a T (fun y => heatKernel a (y - 0)) (fun _ => 1) ω) := by
    simp only [Φ, shfPairing, sub_zero, mul_one]
  have hx (ω : Ω) : Φ (fun _ => Z' a T ω) =
      Real.log (shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1) ω) := by
    dsimp only [Φ, Z']
    have hf : Measurable (fun p : Plane × Plane => heatKernel a p.1) :=
      (measurable_heatKernel a).comp measurable_fst
    rw [integral_map (by fun_prop) hf.aestronglyMeasurable]
    simp only [shfPairing, sub_eq_add_neg, mul_one]
  refine ⟨?_, ?_, ?_⟩
  · exact Real.measurable_log.comp_aemeasurable (aemeasurable_profileHeatMass P Z hZ ha haT x)
  · exact Real.measurable_log.comp_aemeasurable (aemeasurable_profileHeatMass P Z hZ ha haT 0)
  · simpa only [Function.comp_def, h0, hx] using hpush.symm

/-- The mean-zero spatial testing estimate applied to the actual SHF log
field, with stationarity and simultaneous semiconvexity discharged. -/
theorem profile_heatMass_l2_integral_bound (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {a T σ : ℝ} (ha : 0 < a) (haT : a < T) (hσ : 0 ≤ σ)
    (hvar : variance (fun ω => Real.log
      (shfPairing Z a T (fun y => heatKernel a (y - 0)) (fun _ => 1) ω)) P ≤ σ ^ 2)
    {f : Plane → ℝ} (hf : Measurable f) (hfi : Integrable f)
    (hfw : Integrable (fun x => ‖x‖ * |f x|)) (hfzero : ∫ x, f x = 0) :
    eLpNorm (fun ω => ∫ x, f x * Real.log
      (shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1) ω)) 2 P ≤
      ENNReal.ofReal ((4 * Real.sqrt σ / Real.sqrt a) * ∫ x, ‖x‖ * |f x|) := by
  have hJ := JointConvergence.aemeasurable_shfLogField_joint ϑ P Z hZ a T a ha.le haT ha
    (0 : Plane →ᵇ ℝ)
  simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] at hJ
  have hswap := hJ.comp_quasiMeasurePreserving (Measure.measurePreserving_swap (μ := P) (ν := volume)).quasiMeasurePreserving
  have hJoint : AEStronglyMeasurable (fun p : Ω × Plane => Real.log
      (shfPairing Z a T (fun y => heatKernel a (y - p.2)) (fun _ => 1) p.1)) (P.prod volume) :=
    hswap.aestronglyMeasurable
  exact l2_integral_bound_of_integral_zero P _ ha hσ hJoint
    (profile_heatMass_log_identDistrib ϑ P Z hZ ha haT)
    (heatStartMass_convexity_moments ϑ P Z hZ ha haT 0).2.2.1 hvar
    (profile_heatMass_ae_semiconvex ϑ P Z hZ ha haT) hf hfi hfw hfzero

/-- Spatially tested heat-start log fields are pathwise integrable and
square integrable as random variables. -/
theorem profile_heatMass_test_integrable (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {a T : ℝ} (ha : 0 < a) (haT : a < T)
    {f : Plane → ℝ} (hf : Measurable f) (hfi : Integrable f) :
    (∀ᵐ ω ∂P, Integrable (fun x => f x * Real.log
      (shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1) ω))) ∧
    MemLp (fun ω => ∫ x, f x * Real.log
      (shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1) ω)) 2 P := by
  let F := fun (x : Plane) (ω : Ω) => Real.log
    (shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1) ω)
  have hJ := JointConvergence.aemeasurable_shfLogField_joint ϑ P Z hZ a T a ha.le haT ha
    (0 : Plane →ᵇ ℝ)
  simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] at hJ
  have hswap := hJ.comp_quasiMeasurePreserving
    (Measure.measurePreserving_swap (μ := P) (ν := volume)).quasiMeasurePreserving
  have hJoint : AEStronglyMeasurable (fun p : Ω × Plane => F p.2 p.1) (P.prod volume) :=
    hswap.aestronglyMeasurable
  have h0 : MemLp (F 0) 2 P :=
    (heatStartMass_convexity_moments ϑ P Z hZ ha haT 0).2.2.1
  have hLaw (x : Plane) : IdentDistrib (F x) (F 0) P P :=
    profile_heatMass_log_identDistrib ϑ P Z hZ ha haT x
  have hmem (x : Plane) : MemLp (F x) 2 P := (hLaw x).memLp_iff.mpr h0
  let C := Real.sqrt (∫ ω, F 0 ω ^ 2 ∂P)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hsq (x : Plane) : (∫ ω, F x ω ^ 2 ∂P) ≤ C ^ 2 := by
    rw [show C ^ 2 = ∫ ω, F 0 ω ^ 2 ∂P from Real.sq_sqrt (integral_nonneg fun ω => sq_nonneg _)]
    exact le_of_eq ((hLaw x).comp (measurable_id.pow_const 2)).integral_eq
  obtain ⟨hpath, hLp, hnorm⟩ := profile_uniform_l2_integral_bound P hJoint hmem hC hsq hf hfi
  exact ⟨hpath, hLp⟩

/-- The four vertices of a centered coordinate square. -/
def profileCubeVertices (R : ℝ) : Set Plane :=
  (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm ''
    Set.pi univ (fun _ : Fin 2 => {-R, R})


/-- Every point of a coordinate square lies in the hull of its four vertices. -/
theorem profile_mem_convexHull_cubeVertices {R : ℝ} (hR : 0 ≤ R) {x : Plane}
    (hx : ∀ i : Fin 2, |x i| ≤ R) : x ∈ convexHull ℝ (profileCubeVertices R) := by
  let e := (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm
  have hpi : (fun i => x i) ∈ convexHull ℝ (Set.pi univ (fun _ : Fin 2 => {-R, R})) := by
    rw [convexHull_pi]
    intro i _
    rw [convexHull_pair, segment_eq_Icc (by linarith : -R ≤ R)]
    exact abs_le.mp (hx i)
  have himage := Set.mem_image_of_mem e.toLinearMap hpi
  rw [LinearMap.image_convexHull] at himage
  exact himage

/-- The squared norm of any point of the coordinate square is at most `2R²`. -/
theorem profile_cube_norm_sq_le {R : ℝ} {x : Plane} (hx : ∀ i : Fin 2, |x i| ≤ R) :
    ‖x‖ ^ 2 ≤ 2 * R ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have h0 := sq_le_sq₀ (abs_nonneg (x 0)) (abs_nonneg (x 0) |>.trans (hx 0)) |>.mpr (hx 0)
  have h1 := sq_le_sq₀ (abs_nonneg (x 1)) (abs_nonneg (x 1) |>.trans (hx 1)) |>.mpr (hx 1)
  nlinarith only [h0, h1, sq_abs (x 0), sq_abs (x 1)]

theorem profileCubeVertices_norm_sq {R : ℝ} {v : Plane} (hv : v ∈ profileCubeVertices R) :
    ‖v‖ ^ 2 = 2 * R ^ 2 := by
  obtain ⟨y, hy, rfl⟩ := hv
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have h0 := hy 0 (mem_univ _)
  have h1 := hy 1 (mem_univ _)
  simp only [mem_insert_iff, mem_singleton_iff] at h0 h1
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    simp only [WithLp.coe_symm_linearEquiv, PiLp.toLp_apply, h0, h1] <;> ring

/-- Convexity bounds a semiconvex field on a square by one of four vertex values. -/
theorem profile_semiconvex_upper_cube {F : Plane → ℝ} {s R : ℝ} (hs : 0 < s) (hR : 0 ≤ R)
    (hconv : ConvexOn ℝ univ (fun x => F x + ‖x‖ ^ 2 / (2 * s)))
    {x : Plane} (hx : ∀ i : Fin 2, |x i| ≤ R) :
    ∃ v ∈ profileCubeVertices R, F x ≤ F v + R ^ 2 / s := by
  obtain ⟨v, hv, hle⟩ := hconv.exists_ge_of_mem_convexHull (subset_univ _)
    (profile_mem_convexHull_cubeVertices hR hx)
  refine ⟨v, hv, ?_⟩
  rw [profileCubeVertices_norm_sq hv] at hle
  have hnonneg : 0 ≤ ‖x‖ ^ 2 / (2 * s) := by positivity
  have heq : 2 * R ^ 2 / (2 * s) = R ^ 2 / s := by ring
  rw [heq] at hle
  linarith only [hle, hnonneg]

/-- A backwards secant gives a quantitative lower bound for a semiconvex field. -/
theorem profile_semiconvex_lower_secant {F : Plane → ℝ} {s h : ℝ} (hs : 0 < s) (hh : 0 < h)
    (hconv : ConvexOn ℝ univ (fun x => F x + ‖x‖ ^ 2 / (2 * s))) (x : Plane) :
    F 0 - F x ≤ (F (-h • x) - F 0) / h + (h + 1) * ‖x‖ ^ 2 / (2 * s) := by
  have hh1 : 0 < h + 1 := by linarith
  have hsum : h / (h + 1) + 1 / (h + 1) = 1 := by field_simp
  have hcomb : (h / (h + 1)) • x + (1 / (h + 1)) • (-h • x) = 0 := by
    rw [smul_smul, ← add_smul]
    have heq : h / (h + 1) + 1 / (h + 1) * -h = 0 := by ring
    rw [heq, zero_smul]
  have hc := hconv.2 (mem_univ x) (mem_univ (-h • x))
    (div_nonneg hh.le hh1.le) (div_nonneg zero_le_one hh1.le) hsum
  rw [hcomb] at hc
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero,
    norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hh, mul_pow, smul_eq_mul] at hc
  have heq : h / (h + 1) * (F x + ‖x‖ ^ 2 / (2 * s)) +
      1 / (h + 1) * (F (-h • x) + h ^ 2 * ‖x‖ ^ 2 / (2 * s)) =
      (h * F x + F (-h • x) + h * (h + 1) * ‖x‖ ^ 2 / (2 * s)) / (h + 1) := by
    field_simp
    ring
  rw [heq] at hc
  have hc' := (le_div_iff₀ hh1).mp hc
  calc
    _ ≤ (F (-h • x) - F 0 + h * (h + 1) * ‖x‖ ^ 2 / (2 * s)) / h := by
      apply (le_div_iff₀ hh).mpr
      nlinarith only [hc']
    _ = _ := by field_simp

/-- Uniform lower bounds on a square reduce to the origin and four far
vertices. This avoids any pathwise differentiability requirement. -/
theorem profile_semiconvex_lower_cube {F : Plane → ℝ} {s h R : ℝ}
    (hs : 0 < s) (hh : 0 < h) (hR : 0 ≤ R)
    (hconv : ConvexOn ℝ univ (fun x => F x + ‖x‖ ^ 2 / (2 * s)))
    {x : Plane} (hx : ∀ i : Fin 2, |x i| ≤ R) :
    ∃ v ∈ profileCubeVertices (h * R),
      F 0 - F x ≤ (F v - F 0) / h + (2 * h + 1) * R ^ 2 / s := by
  have houter (i : Fin 2) : |(-h • x) i| ≤ h * R := by
    change |(-h) * x i| ≤ _
    rw [abs_mul, abs_neg, abs_of_pos hh]
    exact mul_le_mul_of_nonneg_left (hx i) hh.le
  obtain ⟨v, hv, hupper⟩ := profile_semiconvex_upper_cube hs (mul_nonneg hh.le hR) hconv houter
  refine ⟨v, hv, ?_⟩
  have hsec := profile_semiconvex_lower_secant hs hh hconv x
  have hnorm := profile_cube_norm_sq_le hx
  have hq : (h + 1) * ‖x‖ ^ 2 / (2 * s) ≤ (h + 1) * R ^ 2 / s := by
    have h := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ (h + 1) / (2 * s) by positivity)
    convert h using 1 <;> ring
  calc
    _ ≤ (F (-h • x) - F 0) / h + (h + 1) * ‖x‖ ^ 2 / (2 * s) := hsec
    _ ≤ (F v + (h * R) ^ 2 / s - F 0) / h + (h + 1) * R ^ 2 / s :=
      add_le_add (div_le_div_of_nonneg_right (sub_le_sub_right hupper _) hh.le) hq
    _ = _ := by field_simp; ring

/-- A fixed four-element indexing of the square vertices, useful in probability bounds. -/
def profileCubeVertex (R : ℝ) (b : Fin 2 → Bool) : Plane :=
  WithLp.toLp 2 (fun i => if b i then R else -R)

theorem profileCubeVertices_eq_range (R : ℝ) :
    profileCubeVertices R = range (profileCubeVertex R) := by
  ext v
  constructor
  · rintro ⟨y, hy, rfl⟩
    let b : Fin 2 → Bool := fun i => decide (y i = R)
    refine ⟨b, ?_⟩
    ext i
    have hi := hy i (mem_univ _)
    simp only [mem_insert_iff, mem_singleton_iff] at hi
    change (if b i then R else -R) = y i
    dsimp only [b]
    by_cases heq : y i = R
    · simp [heq]
    · simp only [decide_eq_false heq, Bool.false_eq_true, ↓reduceIte]
      exact (hi.resolve_right heq).symm
  · rintro ⟨b, rfl⟩
    refine ⟨(fun i => if b i then R else -R), ?_, rfl⟩
    intro i _
    by_cases hi : b i = true <;> simp [hi]

/-- The source exponents `17/32` and `5/8` leave room for the semiconvex
oscillation errors on every fixed square. -/
theorem profile_semiconvex_ratio_cube_bound {F G : Plane → ℝ} {s l R : ℝ}
    (hs : 0 < s) (hl : 1 ≤ l) (hls : l ^ 2 ≤ s) (hR : 0 ≤ R)
    (hroom : 4 * R ^ 2 + Real.log 2 ≤ Real.log l / 16)
    (hF : ConvexOn ℝ univ (fun x => F x + ‖x‖ ^ 2 / (2 * s)))
    (hG : ConvexOn ℝ univ (fun x => G x + ‖x‖ ^ 2 / (2 * s)))
    (hF0 : -(17 / 32 : ℝ) * Real.log l ≤ F 0)
    (hFv : ∀ b : Fin 2 → Bool, F (profileCubeVertex (l * R) b) - F 0 ≤ Real.log l / 32)
    (hGv : ∀ b : Fin 2 → Bool, G (profileCubeVertex R b) ≤ Real.log 2)
    {x : Plane} (hx : ∀ i : Fin 2, |x i| ≤ R) :
    G x - F x ≤ (5 / 8 : ℝ) * Real.log l := by
  have hl0 : 0 < l := by linarith
  obtain ⟨v, hv, hlow⟩ := profile_semiconvex_lower_cube hs hl0 hR hF hx
  rw [profileCubeVertices_eq_range] at hv
  obtain ⟨b, rfl⟩ := hv
  have hfar := div_le_div_of_nonneg_right (hFv b) hl0.le
  obtain ⟨v, hv, hupp⟩ := profile_semiconvex_upper_cube hs hR hG hx
  rw [profileCubeVertices_eq_range] at hv
  obtain ⟨b', rfl⟩ := hv
  have hnear := hGv b'
  have hfrac : (Real.log l / 32) / l ≤ Real.log l / 32 :=
    (div_le_iff₀ hl0).mpr (le_mul_of_one_le_right (div_nonneg (Real.log_nonneg hl) (by norm_num) : 0 ≤ Real.log l / 32) hl)
  have hpoly : 2 * l + 2 ≤ 4 * s := by nlinarith only [hl, hls, sq_nonneg (l - 1)]
  have hpen : (2 * l + 2) * R ^ 2 / s ≤ 4 * R ^ 2 := by
    apply (div_le_iff₀ hs).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hpoly (sq_nonneg R)]
  have heq : (2 * l + 1) * R ^ 2 / s + R ^ 2 / s = (2 * l + 2) * R ^ 2 / s := by ring
  nlinarith only [hlow, hfar, hupp, hnear, hfrac, hpen, hroom, hF0, heq]

/-- A uniform first-moment bound for a nonnegative jointly measurable
field may be integrated against an integrable spatial weight. -/
theorem profile_weighted_nonneg_integral_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → Plane → ℝ}
    (hX : AEStronglyMeasurable (fun p : Ω × Plane => X p.1 p.2) (P.prod volume))
    (hX0 : ∀ ω x, 0 ≤ X ω x) (hXi : ∀ x, Integrable (fun ω => X ω x) P)
    {B : ℝ} (_hB : 0 ≤ B) (hbound : ∀ x, (∫ ω, X ω x ∂P) ≤ B)
    {f : Plane → ℝ} (hf : Measurable f) (hfi : Integrable f) :
    (∀ᵐ ω ∂P, Integrable (fun x => |f x| * X ω x)) ∧
      Integrable (fun ω => ∫ x, |f x| * X ω x) P ∧
      (∫ ω, (∫ x, |f x| * X ω x) ∂P) ≤ B * ∫ x, |f x| := by
  have hm : AEStronglyMeasurable (fun p : Ω × Plane => |f p.2| * X p.1 p.2) (P.prod volume) :=
    (hf.abs.comp measurable_snd).aestronglyMeasurable.mul hX
  have hJoint : Integrable (fun p : Ω × Plane => |f p.2| * X p.1 p.2) (P.prod volume) := by
    apply (integrable_prod_iff' hm).mpr
    refine ⟨Eventually.of_forall (fun x => (hXi x).const_mul |f x|), ?_⟩
    apply (hfi.abs.mul_const B).mono' hm.norm.prod_swap.integral_prod_right'
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (integral_nonneg fun ω => norm_nonneg _)]
    have heq : (fun ω => ‖|f x| * X ω x‖) = fun ω => |f x| * X ω x := by
      funext ω
      exact Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (hX0 ω x))
    change (∫ ω, ‖|f x| * X ω x‖ ∂P) ≤ |f x| * B
    rw [heq, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hbound x) (abs_nonneg _)
  refine ⟨hJoint.prod_right_ae, hJoint.integral_prod_left, ?_⟩
  rw [integral_integral_swap hJoint]
  calc
    _ ≤ ∫ x, |f x| * B := integral_mono hJoint.integral_prod_right (hfi.abs.mul_const B)
      (fun x => by
        change (∫ ω, |f x| * X ω x ∂P) ≤ |f x| * B
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (hbound x) (abs_nonneg _))
    _ = _ := by rw [integral_mul_const]; ring

end Critical2DKPZ.Extensions.GffTangent

end
