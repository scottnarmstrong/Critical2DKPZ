/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.LinearCovariance
public import Critical2DKPZ.Extensions.GffTangent.HeatMassMoments
public import Critical2DKPZ.Extensions.GffTangent.HeatMassAssociation
public import Critical2DKPZ.Extensions.GffTangent.AssociatedLog
import Critical2DKPZ.Analysis.Heat.Semigroup
import Critical2DKPZ.SHF.Positivity.HeatPairingEhrhard
import Critical2DKPZ.JointConvergence.HeatStartLogFieldConvergence
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # Covariance decay and locality of the entrance logarithmic field -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open MeasureTheory.Measure
open scoped Topology ENNReal BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.GffTangent

/-- Smoothing a translated heat kernel adds its time parameter. -/
theorem heatSmooth_heatKernel_sub {s a : ℝ} (hs : 0 < s) (ha : 0 < a)
    (x y : Plane) :
    heatSmooth s (fun z => heatKernel a (z - y)) x = heatKernel (a + s) (x - y) := by
  unfold heatSmooth
  rw [← integral_add_right_eq_self _ y]
  calc
    _ = ∫ z, heatKernel a z * heatKernel s ((x - y) - z) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [add_sub_cancel_right, show x - (z + y) = (x - y) - z by abel, mul_comm]
    _ = _ := integral_heatKernel_mul_sub ha hs _

/-- The overlap of two translated heat kernels is another heat kernel. -/
theorem integral_heatKernel_sub_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (x y : Plane) :
    (∫ z, heatKernel a (z - x) * heatKernel b (z - y)) = heatKernel (a + b) (x - y) := by
  rw [← integral_add_right_eq_self _ x]
  calc
    _ = ∫ z, heatKernel a z * heatKernel b ((y - x) - z) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [add_sub_cancel_right, ← heatKernel_neg b (z + x - y)]
      congr 2
      abel
    _ = heatKernel (a + b) (y - x) := integral_heatKernel_mul_sub ha hb _
    _ = _ := by rw [← neg_sub x y, heatKernel_neg]

/-- The covariance density after convolving the entrance kernels. -/
theorem entrance_heat_overlap {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (x y : Plane) :
    4 * Real.pi * (∫ z, heatKernel a (z - x) *
      heatSmooth (2 * r) (fun w => heatKernel a (w - y)) z) =
      (a + r)⁻¹ * Real.exp (-(‖x - y‖ ^ 2) / (4 * (a + r))) := by
  simp_rw [heatSmooth_heatKernel_sub (mul_pos two_pos hr) ha]
  rw [integral_heatKernel_sub_mul ha (by linarith)]
  rw [show a + (a + 2 * r) = 2 * (a + r) by ring, heatKernel]
  have he : -(‖x - y‖ ^ 2) / (2 * (2 * (a + r))) =
      -(‖x - y‖ ^ 2) / (4 * (a + r)) := by ring
  rw [he]
  have hc : 4 * Real.pi * (2 * Real.pi * (2 * (a + r)))⁻¹ = (a + r)⁻¹ := by
    field_simp
    ring
  rw [← mul_assoc, hc]

/-- Exact heat-mass covariance formula, with the entrance time included in the
Gaussian factor and in the lower integration endpoint. -/
theorem heatMass_covariance_formula (l : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF (-l) P Z)
    {a n : ℝ} (ha : 0 < a) (han : a < n) (x y : Plane) :
    covariance (shfPairing Z a n (fun z => heatKernel a (z - x)) (fun _ => 1))
      (shfPairing Z a n (fun z => heatKernel a (z - y)) (fun _ => 1)) P =
      ∫ u in Ioc a n, (u⁻¹ * Real.exp (-(‖x - y‖ ^ 2) / (4 * u))) * uFun l (n - u) := by
  have hm (z : Plane) : Measurable (fun w => heatKernel a (w - z)) := (measurable_heatKernel a).comp (measurable_id.sub_const z)
  have hi (z : Plane) : Integrable (fun w => heatKernel a (w - z)) := by
    simpa only [sub_eq_add_neg] using (integrable_heatKernel ha).comp_add_right (-z)
  have hb (z w : Plane) : |heatKernel a (w - z)| ≤ (2 * Real.pi * a)⁻¹ := by
    rw [abs_of_nonneg (heatKernel_nonneg ha.le _)]
    exact heatKernel_le_at_zero ha.le _
  rw [covariance_shfPairing_start l P Z hZ ha.le han (hm x) (hm y) (hi x) (hi y) (hb x) (hb y),
    ← integral_const_mul]
  have he : (∫ r in Ioc 0 (n - a), 4 * Real.pi *
      ((∫ z, heatKernel a (z - x) * heatSmooth (2 * r) (fun w => heatKernel a (w - y)) z) *
        uFun l (n - a - r))) =
      ∫ r in Ioc 0 (n - a), ((a + r)⁻¹ * Real.exp (-(‖x - y‖ ^ 2) / (4 * (a + r)))) *
        uFun l (n - (a + r)) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    dsimp only
    rw [← mul_assoc, entrance_heat_overlap ha hr.1, show n - a - r = n - (a + r) by ring]
  rw [he, ← intervalIntegral.integral_of_le (sub_nonneg.mpr han.le),
    ← intervalIntegral.integral_of_le han.le]
  simpa only [add_comm a, zero_add, sub_add_cancel] using
    (intervalIntegral.integral_comp_add_right
      (fun u => (u⁻¹ * Real.exp (-(‖x - y‖ ^ 2) / (4 * u))) * uFun l (n - u)) a
      (a := 0) (b := n - a))

/-- The time density is bounded by an integrable inverse-time Gaussian envelope. -/
theorem entrance_covariance_density_le {l a n u d : ℝ}
    (ha : 0 < a) (han : a < n) (hl : 0 < l - Real.log n)
    (hu : u ∈ Ioo a n) (hd : 0 ≤ d) :
    (u⁻¹ * Real.exp (-d / (4 * u))) * uFun l (n - u) ≤
      u⁻¹ * Real.exp (-d / (4 * n)) / (l - Real.log n) := by
  have hn : 0 < n := ha.trans han
  have hu0 : 0 < u := ha.trans hu.1
  have hnu : 0 < n - u := sub_pos.mpr hu.2
  have hlog : Real.log (n - u) ≤ Real.log n :=
    Real.log_le_log hnu (by linarith only [hu0])
  have hlu : Real.log (n - u) < l := by linarith only [hl, hlog]
  have hU := (uFun_pos_le hnu hlu).2
  have hU' : uFun l (n - u) ≤ 1 / (l - Real.log n) :=
    hU.trans (one_div_le_one_div_of_le hl (by linarith only [hlog]))
  have he : Real.exp (-d / (4 * u)) ≤ Real.exp (-d / (4 * n)) := by
    apply Real.exp_le_exp.mpr
    have hh := div_le_div_of_nonneg_left hd (mul_pos (by norm_num) hu0)
      (mul_le_mul_of_nonneg_left hu.2.le (by norm_num : 0 ≤ (4 : ℝ)))
    simpa only [neg_div] using neg_le_neg hh
  calc
    _ ≤ (u⁻¹ * Real.exp (-d / (4 * n))) * (1 / (l - Real.log n)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hu0.le)) hU'
        (uFun_nonneg _ _) (mul_nonneg (inv_nonneg.mpr hu0.le) (Real.exp_pos _).le)
    _ = _ := by ring

/-- Integrability accompanies the Gaussian covariance bound. -/
theorem integral_entrance_covariance_density_le {l a n : ℝ}
    (ha : 0 < a) (han : a < n) (hl : 0 < l - Real.log n) (x y : Plane) :
    IntegrableOn (fun u => (u⁻¹ * Real.exp (-(‖x - y‖ ^ 2) / (4 * u))) *
      uFun l (n - u)) (Ioc a n) ∧
    (∫ u in Ioc a n, (u⁻¹ * Real.exp (-(‖x - y‖ ^ 2) / (4 * u))) * uFun l (n - u)) ≤
      (Real.log (n / a) / (l - Real.log n)) * Real.exp (-(‖x - y‖ ^ 2) / (4 * n)) := by
  let F : ℝ → ℝ := fun u => (u⁻¹ * Real.exp (-(‖x - y‖ ^ 2) / (4 * u))) * uFun l (n - u)
  let H : ℝ → ℝ := fun u => u⁻¹ * Real.exp (-(‖x - y‖ ^ 2) / (4 * n)) / (l - Real.log n)
  have hn : 0 < n := ha.trans han
  have hi : IntegrableOn (fun u : ℝ => u⁻¹) (Icc a n) :=
    (continuousOn_id.inv₀ (fun u hu => (ha.trans_le hu.1).ne')).integrableOn_Icc
  have hHi : IntegrableOn H (Ioc a n) :=
    ((hi.mono_set Ioc_subset_Icc_self).mul_const _).div_const _
  have hFm : Measurable F := by
    apply Measurable.mul
    · fun_prop
    · exact measurable_uFun.comp (measurable_const.prodMk (measurable_const.sub measurable_id))
  have hF0 (u : ℝ) (hu : u ∈ Ioo a n) : 0 ≤ F u :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr (ha.trans hu.1).le) (Real.exp_pos _).le) (uFun_nonneg _ _)
  have hFH (u : ℝ) (hu : u ∈ Ioo a n) : F u ≤ H u :=
    entrance_covariance_density_le ha han hl hu (sq_nonneg _)
  have hFi : IntegrableOn F (Ioo a n) := by
    apply (hHi.mono_set Ioo_subset_Ioc_self).mono' hFm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 u hu)]
    exact hFH u hu
  refine ⟨(integrableOn_Ioc_iff_integrableOn_Ioo).mpr hFi, ?_⟩
  rw [integral_Ioc_eq_integral_Ioo]
  calc
    _ ≤ ∫ u in Ioo a n, H u := integral_mono_ae hFi (hHi.mono_set Ioo_subset_Ioc_self)
      ((ae_restrict_mem measurableSet_Ioo).mono fun u hu => hFH u hu)
    _ = _ := by
      dsimp only [H]
      rw [integral_div, integral_mul_const, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le han.le, integral_inv_of_pos ha hn]
      ring

/-- Exact mass covariance, its Gaussian upper bound, and the second-moment
bound used in the logarithmic estimate. -/
theorem massCovariance_formula_and_bound (l : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF (-l) P Z)
    {a n : ℝ} (ha : 0 < a) (han : a < n) (hl : 0 < l - Real.log n) (x y : Plane) :
    let A := fun z => shfPairing Z a n (fun w => heatKernel a (w - z)) (fun _ => 1)
    let v := Real.log (n / a) / (l - Real.log n)
    covariance (A x) (A y) P =
      (∫ u in Ioc a n, (u⁻¹ * Real.exp (-(‖x - y‖ ^ 2) / (4 * u))) * uFun l (n - u)) ∧
    covariance (A x) (A y) P ≤ v * Real.exp (-(‖x - y‖ ^ 2) / (4 * n)) ∧
    (∫ ω, A x ω ^ 2 ∂P) ≤ 1 + v := by
  dsimp only
  have hxy := heatMass_covariance_formula l P Z hZ ha han x y
  have hbd := (integral_entrance_covariance_density_le ha han hl x y).2
  have hxx := (heatMass_covariance_formula l P Z hZ ha han x x).trans_le
    (integral_entrance_covariance_density_le ha han hl x x).2
  have hX := heatStartMass_memLp_two (-l) P Z hZ ha han x
  rw [covariance_eq_sub hX hX] at hxx
  simp only [Pi.mul_apply, ← pow_two, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    neg_zero, zero_div, Real.exp_zero, mul_one] at hxx
  rw [(heatStartMass_integral_eq_one (-l) P Z hZ ha han x).2] at hxx
  exact ⟨hxy, hxy.trans_le hbd, by linarith only [hxx]⟩

/-- Positivity of the entrance mass, with the zero terminal profile simplified. -/
theorem heatMass_pos (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {a n : ℝ} (ha : 0 < a) (han : a < n) (x : Plane) :
    ∀ᵐ ω ∂P, 0 < shfPairing Z a n (fun z => heatKernel a (z - x)) (fun _ => 1) ω := by
  have hp := (SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType
    ϑ P Z hZ a n a x (0 : Plane →ᵇ ℝ) ha.le han ha).1
  simpa only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] using hp

/-- All numerical moments needed by Lemma 6.5 of the note hold with the source value of V. -/
theorem heatMass_log_moments {l a n : ℝ} (ha : 0 < a) (han : a < n)
    (hl : 0 < l - Real.log n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF (-l) P Z) (x : Plane) :
    let A := shfPairing Z a n (fun z => heatKernel a (z - x)) (fun _ => 1)
    let V := 1 + Real.log (n / a) / (l - Real.log n)
    MemLp (fun ω => Real.log (A ω)) 2 P ∧
    Integrable (fun ω => (A ω)⁻¹ ^ 4) P ∧
    (∫ ω, (A ω)⁻¹ ^ 4 ∂P) ≤ V ^ 10 ∧
    (∫ ω, Real.log (A ω) ^ 2 ∂P) ≤ 4 * (1 + Real.log V) ^ 2 := by
  dsimp only
  have hm := heatStartMass_convexity_moments (-l) P Z hZ ha han x
  have hX := heatStartMass_memLp_two (-l) P Z hZ ha han x
  have hmean := (heatStartMass_integral_eq_one (-l) P Z hZ ha han x).2
  have hQ := (massCovariance_formula_and_bound l P Z hZ ha han hl x x).2.2
  have hv : 0 ≤ Real.log (n / a) / (l - Real.log n) :=
    div_nonneg (Real.log_nonneg ((one_le_div ha).mpr han.le)) hl.le
  have hV : 1 ≤ 1 + Real.log (n / a) / (l - Real.log n) := le_add_of_nonneg_right hv
  exact ⟨hm.2.2.1, hm.1, hm.2.1.trans
    (pow_le_pow_left₀ (integral_nonneg fun ω => sq_nonneg _) hQ 10),
    integral_log_sq_le_of_convexity_bounds P hX (heatMass_pos (-l) P Z hZ ha han x)
      hmean hV hQ hm.2.2.1 hm.2.2.2.1 hm.2.2.2.2⟩

/-- Taking a square root halves the exponent of the covariance envelope. -/
theorem sqrt_gaussian_covariance_bound {c v d n : ℝ} (hv : 0 ≤ v)
    (hc : c ≤ v * Real.exp (-d / (4 * n))) :
    Real.sqrt c ≤ Real.sqrt v * Real.exp (-d / (8 * n)) := by
  have he : Real.sqrt (Real.exp (-d / (4 * n))) = Real.exp (-d / (8 * n)) := by
    rw [show -d / (4 * n) = -d / (8 * n) + -d / (8 * n) by ring,
      Real.exp_add, ← pow_two, Real.sqrt_sq (Real.exp_pos _).le]
  calc
    _ ≤ Real.sqrt (v * Real.exp (-d / (4 * n))) := Real.sqrt_le_sqrt hc
    _ = _ := by rw [Real.sqrt_mul hv, he]

/-- Heat-mass logarithmic covariance decays with a Gaussian spatial envelope.
The universal numerical constant is 4. -/
theorem covariance_log_heatMasses_le {l a n : ℝ} (ha : 0 < a) (han : a < n)
    (hl : 0 < l - Real.log n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF (-l) P Z)
    (x y : Plane) :
    let A := fun z => shfPairing Z a n (fun w => heatKernel a (w - z)) (fun _ => 1)
    let v := Real.log (n / a) / (l - Real.log n)
    let V := 1 + v
    0 ≤ covariance (fun ω => Real.log (A x ω)) (fun ω => Real.log (A y ω)) P ∧
    covariance (fun ω => Real.log (A x ω)) (fun ω => Real.log (A y ω)) P ≤
      4 * V ^ (5 / 2 : ℝ) * Real.sqrt (1 + Real.log V) * Real.sqrt v *
        Real.exp (-(‖x - y‖ ^ 2) / (8 * n)) := by
  let A := fun z => shfPairing Z a n (fun w => heatKernel a (w - z)) (fun _ => 1)
  let v := Real.log (n / a) / (l - Real.log n)
  let V := 1 + v
  have hv : 0 ≤ v := div_nonneg (Real.log_nonneg ((one_le_div ha).mpr han.le)) hl.le
  have hV : 1 ≤ V := le_add_of_nonneg_right hv
  have hX := heatStartMass_memLp_two (-l) P Z hZ ha han x
  have hY := heatStartMass_memLp_two (-l) P Z hZ ha han y
  have hx := heatMass_log_moments ha han hl P Z hZ x
  have hy := heatMass_log_moments ha han hl P Z hZ y
  have hp : ∀ᵐ ω ∂P, 0 < A x ω ∧ 0 < A y ω :=
    (heatMass_pos (-l) P Z hZ ha han x).and (heatMass_pos (-l) P Z hZ ha han y)
  have hxy := massCovariance_formula_and_bound l P Z hZ ha han hl x y
  have hyy := massCovariance_formula_and_bound l P Z hZ ha han hl y y
  have hbound := covariance_log_le_moment_bound P hp hX hY hx.1 hy.1 hV hxy.2.2 hyy.2.2
    hx.2.1 hy.2.1 hx.2.2.1 hy.2.2.1 hx.2.2.2 hy.2.2.2
    (posQuadrantDependent_of_real P (heatMasses_posQuadrantDependent (-l) P Z hZ ha han x y))
  refine ⟨hbound.1, hbound.2.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_left (sqrt_gaussian_covariance_bound hv hxy.2.1)
    (show 0 ≤ 4 * V ^ (5 / 2 : ℝ) * Real.sqrt (1 + Real.log V) by positivity)
  simpa only [mul_assoc] using hh

/-- Uniform pointwise second moments justify spatial testing on the product
space, including for fields that are only jointly measurable almost everywhere. -/
theorem integrable_weighted_field {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → Plane → ℝ}
    (hX : AEStronglyMeasurable (fun p : Ω × Plane => X p.1 p.2) (P.prod volume))
    (hmem : ∀ x, MemLp (fun ω => X ω x) 2 P) {M : ℝ}
    (hbound : ∀ x, (∫ ω, X ω x ^ 2 ∂P) ≤ M)
    {f : Plane → ℝ} (hf : Measurable f) (hfi : Integrable f) :
    Integrable (fun p : Ω × Plane => f p.2 * X p.1 p.2) (P.prod volume) := by
  have hm := (hf.comp measurable_snd).aestronglyMeasurable.mul hX
  apply (integrable_prod_iff' hm).mpr
  refine ⟨Eventually.of_forall (fun x => (hmem x).integrable (by norm_num) |>.const_mul (f x)), ?_⟩
  apply (hfi.abs.mul_const (M + 1)).mono' hm.norm.prod_swap.integral_prod_right'
  filter_upwards [] with x
  change ‖∫ ω, ‖f x * X ω x‖ ∂P‖ ≤ |f x| * (M + 1)
  rw [Real.norm_of_nonneg (integral_nonneg fun ω => norm_nonneg _)]
  have hb : (∫ ω, |X ω x| ∂P) ≤ M + 1 := by
    calc
      _ ≤ ∫ ω, X ω x ^ 2 + 1 ∂P := integral_mono ((hmem x).integrable (by norm_num)).abs
        ((hmem x).integrable_sq.add (integrable_const 1)) (fun ω => by
          nlinarith only [sq_nonneg (|X ω x| - 1 / 2), sq_abs (X ω x)])
      _ = (∫ ω, X ω x ^ 2 ∂P) + 1 := by rw [integral_add (hmem x).integrable_sq (integrable_const 1)]; simp
      _ ≤ M + 1 := add_le_add (hbound x) le_rfl
  simpa only [Real.norm_eq_abs, abs_mul, integral_const_mul] using
    mul_le_mul_of_nonneg_left hb (abs_nonneg (f x))

/-- Product integrability for two spatial evaluations, prior to Fubini. -/
theorem integrable_weighted_field_pair {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → Plane → ℝ}
    (hX : AEStronglyMeasurable (fun p : Ω × Plane => X p.1 p.2) (P.prod volume))
    (hmem : ∀ x, MemLp (fun ω => X ω x) 2 P) {M : ℝ}
    (hbound : ∀ x, (∫ ω, X ω x ^ 2 ∂P) ≤ M)
    {f : Plane → ℝ} (hf : Measurable f) (hfi : Integrable f) :
    Integrable (fun p : Ω × (Plane × Plane) =>
      (f p.2.1 * X p.1 p.2.1) * (f p.2.2 * X p.1 p.2.2)) (P.prod (volume.prod volume)) := by
  have hπ₁ : QuasiMeasurePreserving (fun p : Ω × (Plane × Plane) => (p.1, p.2.1))
      (P.prod (volume.prod volume)) (P.prod volume) :=
    QuasiMeasurePreserving.prodMap (QuasiMeasurePreserving.id P)
      (quasiMeasurePreserving_fst (μ := volume) (ν := volume))
  have hπ₂ : QuasiMeasurePreserving (fun p : Ω × (Plane × Plane) => (p.1, p.2.2))
      (P.prod (volume.prod volume)) (P.prod volume) :=
    QuasiMeasurePreserving.prodMap (QuasiMeasurePreserving.id P)
      (quasiMeasurePreserving_snd (μ := volume) (ν := volume))
  have hm : AEStronglyMeasurable (fun p : Ω × (Plane × Plane) =>
      (f p.2.1 * X p.1 p.2.1) * (f p.2.2 * X p.1 p.2.2)) (P.prod (volume.prod volume)) :=
    (((hf.comp measurable_snd.fst).aestronglyMeasurable.mul
      (hX.comp_quasiMeasurePreserving hπ₁)).mul
      ((hf.comp measurable_snd.snd).aestronglyMeasurable.mul (hX.comp_quasiMeasurePreserving hπ₂)))
  apply (integrable_prod_iff' hm).mpr
  refine ⟨Eventually.of_forall (fun p => ((hmem p.1).const_mul (f p.1)).integrable_mul
    ((hmem p.2).const_mul (f p.2))), ?_⟩
  apply ((hfi.abs.mul_prod hfi.abs).mul_const (2 * M)).mono' hm.norm.prod_swap.integral_prod_right'
  filter_upwards [] with p
  change ‖∫ ω, ‖(f p.1 * X ω p.1) * (f p.2 * X ω p.2)‖ ∂P‖ ≤ |f p.1| * |f p.2| * (2 * M)
  rw [Real.norm_of_nonneg (integral_nonneg fun ω => norm_nonneg _)]
  have hb : (∫ ω, |X ω p.1 * X ω p.2| ∂P) ≤ 2 * M := by
    calc
      _ ≤ ∫ ω, X ω p.1 ^ 2 + X ω p.2 ^ 2 ∂P :=
        integral_mono ((hmem p.1).integrable_mul (hmem p.2)).abs
          ((hmem p.1).integrable_sq.add (hmem p.2).integrable_sq) (fun ω => by
            change |X ω p.1 * X ω p.2| ≤ _
            rw [abs_mul]
            nlinarith only [sq_nonneg (|X ω p.1| - |X ω p.2|), sq_abs (X ω p.1), sq_abs (X ω p.2)])
      _ ≤ 2 * M := by
        rw [integral_add (hmem p.1).integrable_sq (hmem p.2).integrable_sq]
        linarith only [hbound p.1, hbound p.2]
  have he : (fun ω => ‖(f p.1 * X ω p.1) * (f p.2 * X ω p.2)‖) =
      (fun ω => (|f p.1| * |f p.2|) * |X ω p.1 * X ω p.2|) := by
    funext ω
    simp only [Real.norm_eq_abs, abs_mul]
    ring
  rw [he, integral_const_mul]
  exact mul_le_mul_of_nonneg_left hb (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- Fubini's covariance formula for an almost-everywhere jointly measurable
field. Spatial integrability and square integrability precede the variance. -/
theorem variance_weighted_field_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → Plane → ℝ}
    (hX : AEStronglyMeasurable (fun p : Ω × Plane => X p.1 p.2) (P.prod volume))
    (hmem : ∀ x, MemLp (fun ω => X ω x) 2 P) {M : ℝ}
    (hbound : ∀ x, (∫ ω, X ω x ^ 2 ∂P) ≤ M)
    {f : Plane → ℝ} (hf : Measurable f) (hfi : Integrable f) :
    (∀ᵐ ω ∂P, Integrable (fun x => f x * X ω x)) ∧
    MemLp (fun ω => ∫ x, f x * X ω x) 2 P ∧
    Integrable (fun p : Plane × Plane => f p.1 * f p.2 *
      covariance (fun ω => X ω p.1) (fun ω => X ω p.2) P) (volume.prod volume) ∧
    variance (fun ω => ∫ x, f x * X ω x) P =
      ∫ p : Plane × Plane, f p.1 * f p.2 *
        covariance (fun ω => X ω p.1) (fun ω => X ω p.2) P ∂(volume.prod volume) := by
  let L : Ω → ℝ := fun ω => ∫ x, f x * X ω x
  let R : Plane × Plane → ℝ := fun p => f p.1 * f p.2 * ∫ ω, X ω p.1 * X ω p.2 ∂P
  let m : Plane → ℝ := fun x => f x * ∫ ω, X ω x ∂P
  have hF := integrable_weighted_field P hX hmem hbound hf hfi
  have hFF := integrable_weighted_field_pair P hX hmem hbound hf hfi
  have hLs : AEStronglyMeasurable L P := hF.aestronglyMeasurable.integral_prod_right'
  have hL2 : MemLp L 2 P := by
    apply (memLp_two_iff_integrable_sq hLs).mpr
    apply hFF.integral_prod_left.congr
    filter_upwards [] with ω
    change (∫ p : Plane × Plane, (f p.1 * X ω p.1) * (f p.2 * X ω p.2) ∂(volume.prod volume)) = L ω ^ 2
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
  have hm : Integrable m := by
    apply hF.integral_prod_right.congr
    filter_upwards [] with x
    exact integral_const_mul _ _
  have hmm : Integrable (fun p : Plane × Plane => m p.1 * m p.2) (volume.prod volume) := hm.mul_prod hm
  have he (p : Plane × Plane) : f p.1 * f p.2 *
      covariance (fun ω => X ω p.1) (fun ω => X ω p.2) P = R p - m p.1 * m p.2 := by
    rw [covariance_eq_sub (hmem p.1) (hmem p.2)]
    change f p.1 * f p.2 * ((∫ ω, X ω p.1 * X ω p.2 ∂P) -
      (∫ ω, X ω p.1 ∂P) * (∫ ω, X ω p.2 ∂P)) = _
    dsimp only [R, m]
    ring
  have hC : Integrable (fun p : Plane × Plane => f p.1 * f p.2 *
      covariance (fun ω => X ω p.1) (fun ω => X ω p.2) P) (volume.prod volume) :=
    (hR.sub hmm).congr (Eventually.of_forall fun p => (he p).symm)
  have hsq : (∫ ω, L ω ^ 2 ∂P) = ∫ p : Plane × Plane, R p ∂(volume.prod volume) := by
    calc
      _ = ∫ ω, (∫ p : Plane × Plane, (f p.1 * X ω p.1) * (f p.2 * X ω p.2) ∂(volume.prod volume)) ∂P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        simpa only [L, pow_two] using (integral_prod_mul (μ := volume) (ν := volume)
          (fun x => f x * X ω x) (fun x => f x * X ω x)).symm
      _ = ∫ p : Plane × Plane, (∫ ω, (f p.1 * X ω p.1) * (f p.2 * X ω p.2) ∂P) ∂(volume.prod volume) :=
        integral_integral_swap hFF
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with p
        dsimp only [R]
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with ω
        ring
  have hmean : (∫ ω, L ω ∂P) = ∫ x, m x := by
    rw [show (∫ ω, L ω ∂P) = ∫ x, ∫ ω, f x * X ω x ∂P from integral_integral_swap hF]
    apply integral_congr_ae
    filter_upwards [] with x
    exact integral_const_mul _ _
  refine ⟨hF.prod_right_ae, hL2, hC, ?_⟩
  rw [variance_eq_sub hL2]
  change (∫ ω, L ω ^ 2 ∂P) - (∫ ω, L ω ∂P) ^ 2 = _
  rw [hsq, hmean]
  simp_rw [he]
  rw [integral_sub hR hmm, integral_prod_mul, pow_two]

/-- The unnormalized planar Gaussian has mass 8 pi n. -/
theorem integrable_gaussian_locality {n : ℝ} (hn : 0 < n) (x : Plane) :
    Integrable (fun y : Plane => Real.exp (-(‖x - y‖ ^ 2) / (8 * n))) ∧
    (∫ y : Plane, Real.exp (-(‖x - y‖ ^ 2) / (8 * n))) = 8 * Real.pi * n := by
  have he (y : Plane) : Real.exp (-(‖x - y‖ ^ 2) / (8 * n)) =
      (8 * Real.pi * n) * heatKernel (4 * n) (y - x) := by
    rw [heatKernel, norm_sub_rev x y]
    have hc : 8 * Real.pi * n * (2 * Real.pi * (4 * n))⁻¹ = 1 := by
      field_simp
      ring
    rw [← mul_assoc, hc, one_mul]
    congr 1
    ring
  have hi : Integrable (fun y => heatKernel (4 * n) (y - x)) := by
    simpa only [sub_eq_add_neg] using
      (integrable_heatKernel (mul_pos (by norm_num) hn)).comp_add_right (-x)
  simp_rw [he]
  exact ⟨hi.const_mul _, by rw [integral_const_mul,
    integral_heatKernel_sub (mul_pos (by norm_num) hn), mul_one]⟩

/-- Integrating the Gaussian covariance envelope uses one L1 norm and one
pointwise bound on the test function. -/
theorem integral_weighted_gaussian_le {n B : ℝ} (hn : 0 < n)
    {f : Plane → ℝ} (hf : Measurable f) (hfi : Integrable f) (hfB : ∀ x, |f x| ≤ B) :
    Integrable (fun p : Plane × Plane => |f p.1| * |f p.2| *
      Real.exp (-(‖p.1 - p.2‖ ^ 2) / (8 * n))) (volume.prod volume) ∧
    (∫ p : Plane × Plane, |f p.1| * |f p.2| *
      Real.exp (-(‖p.1 - p.2‖ ^ 2) / (8 * n)) ∂(volume.prod volume)) ≤
      (∫ x, |f x|) * B * (8 * Real.pi * n) := by
  let G : Plane × Plane → ℝ := fun p => |f p.1| * |f p.2| *
    Real.exp (-(‖p.1 - p.2‖ ^ 2) / (8 * n))
  have hG0 (p : Plane × Plane) : 0 ≤ G p := by dsimp only [G]; positivity
  have he (p : Plane × Plane) : Real.exp (-(‖p.1 - p.2‖ ^ 2) / (8 * n)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity))
  have hG : Integrable G (volume.prod volume) := by
    apply (hfi.abs.mul_prod hfi.abs).mono'
      (((hf.comp measurable_fst).abs.mul (hf.comp measurable_snd).abs).mul
        (by fun_prop : Measurable (fun p : Plane × Plane =>
          Real.exp (-(‖p.1 - p.2‖ ^ 2) / (8 * n))))).aestronglyMeasurable
    filter_upwards [] with p
    change ‖G p‖ ≤ |f p.1| * |f p.2|
    rw [Real.norm_of_nonneg (hG0 p)]
    exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (he p)
  refine ⟨hG, ?_⟩
  rw [integral_prod _ hG]
  have hb (x : Plane) : (∫ y, |f y| * Real.exp (-(‖x - y‖ ^ 2) / (8 * n))) ≤
      B * (8 * Real.pi * n) := by
    have hg := integrable_gaussian_locality hn x
    calc
      _ ≤ ∫ y, B * Real.exp (-(‖x - y‖ ^ 2) / (8 * n)) :=
        integral_mono_of_nonneg (Eventually.of_forall fun y => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
          (hg.1.const_mul B) (Eventually.of_forall fun y =>
            mul_le_mul_of_nonneg_right (hfB y) (Real.exp_pos _).le)
      _ = _ := by rw [integral_const_mul, hg.2]
  calc
    _ = ∫ x, |f x| * ∫ y, |f y| * Real.exp (-(‖x - y‖ ^ 2) / (8 * n)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp only [G]
      simp_rw [mul_assoc]
      exact integral_const_mul _ _
    _ ≤ ∫ x, |f x| * (B * (8 * Real.pi * n)) :=
      integral_mono_of_nonneg
        (Eventually.of_forall fun x => mul_nonneg (abs_nonneg _)
          (integral_nonneg fun y => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le))
        (hfi.abs.mul_const _) (Eventually.of_forall fun x =>
          mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _))
    _ = _ := by rw [integral_mul_const]; ring

/-- The spatial average has finite variance and satisfies Proposition 6.6 of the note
with the explicit universal constant 32 pi. -/
theorem variance_entrance_log_pairing_bound {l a n : ℝ} (ha : 0 < a) (han : a < n)
    (hl : 0 < l - Real.log n) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF (-l) P Z)
    (f : Plane → ℝ) (hf : Measurable f) (hfi : Integrable f) {B : ℝ} (hB : 0 ≤ B) (hfB : ∀ x, |f x| ≤ B) :
    let A := fun x => shfPairing Z a n (fun y => heatKernel a (y - x)) (fun _ => 1)
    let L := fun ω => ∫ x, f x * Real.log (A x ω)
    let V := 1 + Real.log (n / a) / (l - Real.log n)
    (∀ᵐ ω ∂P, Integrable (fun x => f x * Real.log (A x ω))) ∧ MemLp L 2 P ∧
    variance L P ≤ (32 * Real.pi) * (∫ x, |f x|) * B * n * V ^ 3 * Real.sqrt (1 + Real.log V) := by
  let X : Ω → Plane → ℝ := fun ω x => Real.log
    (shfPairing Z a n (fun y => heatKernel a (y - x)) (fun _ => 1) ω)
  let v := Real.log (n / a) / (l - Real.log n)
  let V := 1 + v
  let D := 4 * V ^ (5 / 2 : ℝ) * Real.sqrt (1 + Real.log V) * Real.sqrt v
  let G : Plane × Plane → ℝ := fun p => |f p.1| * |f p.2| * Real.exp (-(‖p.1 - p.2‖ ^ 2) / (8 * n))
  have hv : 0 ≤ v := div_nonneg (Real.log_nonneg ((one_le_div ha).mpr han.le)) hl.le
  have hV : 0 < V := add_pos_of_pos_of_nonneg zero_lt_one hv
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hn : 0 < n := ha.trans han
  have hfield : AEStronglyMeasurable (fun p : Ω × Plane => X p.1 p.2) (P.prod volume) := by
    have hh := (JointConvergence.aemeasurable_shfLogField_joint (-l) P Z hZ a n a ha.le han ha
      (0 : Plane →ᵇ ℝ)).aestronglyMeasurable.prod_swap
    simpa only [X, Prod.fst_swap, Prod.snd_swap, BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] using hh
  have hmem (x : Plane) : MemLp (fun ω => X ω x) 2 P := (heatMass_log_moments ha han hl P Z hZ x).1
  have hbound (x : Plane) : (∫ ω, X ω x ^ 2 ∂P) ≤ 4 * (1 + Real.log V) ^ 2 :=
    (heatMass_log_moments ha han hl P Z hZ x).2.2.2
  have hsp := variance_weighted_field_eq P hfield hmem hbound hf hfi
  have hgauss := integral_weighted_gaussian_le hn hf hfi hfB
  have htest (p : Plane × Plane) : f p.1 * f p.2 *
      covariance (fun ω => X ω p.1) (fun ω => X ω p.2) P ≤ D * G p := by
    have hc := covariance_log_heatMasses_le ha han hl P Z hZ p.1 p.2
    have hc0 : 0 ≤ covariance (fun ω => X ω p.1) (fun ω => X ω p.2) P := hc.1
    have hcbd : covariance (fun ω => X ω p.1) (fun ω => X ω p.2) P ≤
        D * Real.exp (-(‖p.1 - p.2‖ ^ 2) / (8 * n)) := hc.2
    calc
      _ ≤ (|f p.1| * |f p.2|) * covariance (fun ω => X ω p.1) (fun ω => X ω p.2) P :=
        mul_le_mul_of_nonneg_right (by rw [← abs_mul]; exact le_abs_self _) hc0
      _ ≤ (|f p.1| * |f p.2|) * (D * Real.exp (-(‖p.1 - p.2‖ ^ 2) / (8 * n))) :=
        mul_le_mul_of_nonneg_left hcbd (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = _ := by dsimp only [G]; ring
  have hvar : variance (fun ω => ∫ x, f x * X ω x) P ≤
      D * ((∫ x, |f x|) * B * (8 * Real.pi * n)) := by
    rw [hsp.2.2.2]
    calc
      _ ≤ ∫ p : Plane × Plane, D * G p ∂(volume.prod volume) :=
        integral_mono_ae hsp.2.2.1 (hgauss.1.const_mul D) (Eventually.of_forall htest)
      _ = D * ∫ p : Plane × Plane, G p ∂(volume.prod volume) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hgauss.2 hD
  have hpow : V ^ (5 / 2 : ℝ) * Real.sqrt V = V ^ 3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hV]
    norm_num only [show (5 / 2 : ℝ) + 1 / 2 = 3 by norm_num, Real.rpow_ofNat]
  have hDbd : D ≤ 4 * V ^ 3 * Real.sqrt (1 + Real.log V) := by
    calc
      _ ≤ 4 * V ^ (5 / 2 : ℝ) * Real.sqrt (1 + Real.log V) * Real.sqrt V :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (show v ≤ V from le_add_of_nonneg_left zero_le_one))
          (by positivity)
      _ = _ := by
        calc
          _ = 4 * (V ^ (5 / 2 : ℝ) * Real.sqrt V) * Real.sqrt (1 + Real.log V) := by ring
          _ = _ := by rw [hpow]
  refine ⟨hsp.1, hsp.2.1, hvar.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_right hDbd
    (show 0 ≤ (∫ x, |f x|) * B * (8 * Real.pi * n) from
      mul_nonneg (mul_nonneg (integral_nonneg fun x => abs_nonneg _) hB) (by positivity))
  convert hh using 1
  ring

universe u

/-- Proposition 6.6 of the note, with a universal constant quantified before the flow,
probability space, entrance times, and test function. -/
theorem variance_entrance_log_pairing_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (l a n : ℝ), 0 < a → a < n → 0 < l - Real.log n →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF (-l) P Z)
        (f : TestFn) (B : ℝ), 0 ≤ B → (∀ x, |f x| ≤ B) →
        let A := fun x => shfPairing Z a n (fun y => heatKernel a (y - x)) (fun _ => 1)
        let L := fun ω => ∫ x, f x * Real.log (A x ω)
        let V := 1 + Real.log (n / a) / (l - Real.log n)
        (∀ᵐ ω ∂P, Integrable (fun x => f x * Real.log (A x ω))) ∧ MemLp L 2 P ∧
          variance L P ≤ C * (∫ x, |f x|) * B * n * V ^ 3 * Real.sqrt (1 + Real.log V) := by
  refine ⟨32 * Real.pi, by positivity, ?_⟩
  intro l a n ha han hl Ω _ P _ Z hZ f B hB hfB
  exact variance_entrance_log_pairing_bound ha han hl P Z hZ f f.continuous.measurable
    (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport) hB hfB

end Critical2DKPZ.Extensions.GffTangent
