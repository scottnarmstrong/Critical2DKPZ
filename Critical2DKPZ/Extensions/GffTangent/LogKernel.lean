/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.Definitions.LogCovariance
public import Critical2DKPZ.Definitions.HeatKernel
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Absolute convergence of the planar logarithmic covariance

The logarithmic singularity is dominated on each ball by a multiple of the inverse
radius. In dimension two this is integrable. A measure-preserving shear then
handles the diagonal singularity in the product integral (note, Lemma A.1).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric intervalIntegral

namespace Critical2DKPZ.Extensions.GffTangent

/-- A bound for the logarithm useful at both zero and infinity. -/
theorem abs_log_le_add_inv {r : ℝ} (hr : 0 ≤ r) :
    |Real.log r| ≤ r + r⁻¹ := by
  rcases hr.eq_or_lt with hr | hr
  · subst r
    simp only [Real.log_zero, abs_zero, inv_zero, add_zero, le_refl]
  · apply abs_le.mpr
    constructor
    · have h := Real.one_sub_inv_le_log_of_pos hr
      linarith
    · have h := Real.log_le_sub_one_of_pos hr
      have hi := inv_nonneg.mpr hr.le
      linarith

/-- The logarithmic radial kernel is integrable on every ball of the plane. -/
theorem integrableOn_log_norm_ball (R : ℝ) :
    IntegrableOn (fun z : Plane => Real.log ‖z‖) (ball 0 R) := by
  refine integrableOn_ball_of_norm_le_rpow (C := R ^ 2 + 1) (α := 1) ?_ ?_ ?_ ?_
  · simp only [Plane, finrank_euclideanSpace, Fintype.card_fin]
    norm_num
  · simp only [Plane, finrank_euclideanSpace, Fintype.card_fin]
    norm_num
  · filter_upwards [self_mem_ae_restrict measurableSet_ball] with z hz
    rw [mem_ball_zero_iff] at hz
    rw [Real.rpow_neg_one]
    by_cases hzero : z = 0
    · subst z
      simp only [norm_zero, Real.log_zero, inv_zero, mul_zero, le_refl]
    · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hzero
      have hsq : ‖z‖ ^ 2 ≤ R ^ 2 := sq_le_sq₀ hn.le (hn.trans hz).le |>.mpr hz.le
      have hdiv : ‖z‖ ≤ R ^ 2 * ‖z‖⁻¹ := by
        apply (le_mul_inv_iff₀ hn).mpr
        simpa only [pow_two] using hsq
      calc
        ‖Real.log ‖z‖‖ = |Real.log ‖z‖| := Real.norm_eq_abs _
        _ ≤ ‖z‖ + ‖z‖⁻¹ := abs_log_le_add_inv (norm_nonneg z)
        _ ≤ (R ^ 2 + 1) * ‖z‖⁻¹ := by linarith only [hdiv]
  · exact (Real.measurable_log.comp measurable_norm).aestronglyMeasurable

/-- Absolute convergence of the double logarithmic integral, without a mean-zero assumption. -/
theorem integrable_log_kernel_mul (f g : TestFn) :
    Integrable (fun p : Plane × Plane =>
      f p.1 * g p.2 * Real.log ‖p.1 - p.2‖) (volume.prod volume) := by
  obtain ⟨R, hRpos, hR⟩ :=
    (f.hasCompactSupport.isCompact.union g.hasCompactSupport.isCompact).isBounded.exists_pos_norm_lt
  let k : Plane → ℝ := (ball 0 (2 * R)).indicator (fun z => Real.log ‖z‖)
  have hk : Integrable k :=
    (integrableOn_log_norm_ball (2 * R)).integrable_indicator measurableSet_ball
  have hf : Integrable (f : Plane → ℝ) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hbase := hf.mul_prod hk
  have hshear := (measurePreserving_prod_sub (volume : Measure Plane) volume).integrable_comp_of_integrable hbase
  obtain ⟨C, hC⟩ := g.hasCompactSupport.exists_bound_of_continuous g.continuous
  have hmul := hshear.mul_bdd (g.continuous.comp continuous_snd).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p : Plane × Plane => hC p.2)
  apply hmul.congr
  filter_upwards [] with p
  dsimp only [Function.comp_def] at *
  by_cases hfp : f p.1 = 0
  · simp only [hfp, zero_mul]
  by_cases hgp : g p.2 = 0
  · simp only [hgp, mul_zero, zero_mul]
  have h1 : ‖p.1‖ < R := hR p.1 (Or.inl (subset_tsupport _ (Function.mem_support.mpr hfp)))
  have h2 : ‖p.2‖ < R := hR p.2 (Or.inr (subset_tsupport _ (Function.mem_support.mpr hgp)))
  have hdiff : p.2 - p.1 ∈ ball (0 : Plane) (2 * R) := by
    rw [mem_ball_zero_iff]
    exact (norm_sub_le _ _).trans_lt (by linarith only [h1, h2])
  dsimp only [k]
  rw [indicator_of_mem hdiff, norm_sub_rev p.2 p.1]
  ring

/-- Symmetry of the absolutely convergent logarithmic covariance. -/
theorem logCovariance_symm (f g : TestFn) :
    logCovariance f g = logCovariance g f := by
  unfold logCovariance
  congr 1
  rw [integral_integral_swap (integrable_log_kernel_mul f g)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with v
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with u
  rw [norm_sub_rev u v, mul_comm (f u) (g v)]

/-- Additivity in the first test function. -/
theorem logCovariance_add_left (f g h : TestFn) :
    logCovariance (f + h) g = logCovariance f g + logCovariance h g := by
  unfold logCovariance
  simp only [add_apply, add_mul]
  rw [integral_integral_add (integrable_log_kernel_mul f g) (integrable_log_kernel_mul h g)]
  exact neg_add _ _

/-- Homogeneity in the first test function. -/
theorem logCovariance_smul_left (a : ℝ) (f g : TestFn) :
    logCovariance (a • f) g = a * logCovariance f g := by
  unfold logCovariance
  simp only [smul_apply, smul_eq_mul, mul_assoc,
    MeasureTheory.integral_const_mul, mul_neg]

/-- Additivity in the second test function. -/
theorem logCovariance_add_right (f g h : TestFn) :
    logCovariance f (g + h) = logCovariance f g + logCovariance f h := by
  rw [logCovariance_symm f (g + h), logCovariance_add_left,
    logCovariance_symm g f, logCovariance_symm h f]

/-- Homogeneity in the second test function. -/
theorem logCovariance_smul_right (a : ℝ) (f g : TestFn) :
    logCovariance f (a • g) = a * logCovariance f g := by
  rw [logCovariance_symm f (a • g), logCovariance_smul_left, logCovariance_symm g f]

/-- The exponential integral, used only with a positive lower endpoint. -/
def expIntegral (x : ℝ) : ℝ := ∫ w in Ioi x, Real.exp (-w) / w

/-- Integrability of the defining improper integral for a positive endpoint. -/
theorem integrableOn_exp_neg_div (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun w : ℝ => Real.exp (-w) / w) (Ioi x) := by
  apply ((integrableOn_exp_neg_Ioi x).div_const x).mono'
  · exact ((Real.measurable_exp.comp measurable_neg).div measurable_id).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with w hw
    have hwpos : 0 < w := hx.trans hw
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _) hwpos)]
    exact div_le_div_of_nonneg_left (Real.exp_nonneg _) hx hw.le

/-- The regular part of the exponential-integral kernel. Its value at zero is harmless. -/
def expIntegralRemainder (w : ℝ) : ℝ := (Real.exp (-w) - 1) / w

/-- The regular part stays between `-1` and `0` on the positive half-line. -/
theorem expIntegralRemainder_bounds {w : ℝ} (hw : 0 ≤ w) :
    -1 ≤ expIntegralRemainder w ∧ expIntegralRemainder w ≤ 0 := by
  rcases hw.eq_or_lt with h | h
  · subst w
    norm_num [expIntegralRemainder]
  · dsimp only [expIntegralRemainder]
    constructor
    · apply (le_div_iff₀ h).mpr
      have he := Real.add_one_le_exp (-w)
      linarith only [he]
    · exact div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr h.le))) h.le

/-- The regular kernel is integrable down to zero. -/
theorem intervalIntegrable_expIntegralRemainder {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable expIntegralRemainder volume a b := by
  apply (intervalIntegrable_iff).mpr
  apply Measure.integrableOn_of_bounded (measure_Ioc_lt_top.ne)
  · exact ((Real.measurable_exp.comp measurable_neg).sub measurable_const |>.div
      measurable_id).aestronglyMeasurable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with w hw
    have hw0 : 0 ≤ w := (le_min ha hb).trans hw.1.le
    exact (abs_le.mpr ⟨(expIntegralRemainder_bounds hw0).1,
      (expIntegralRemainder_bounds hw0).2.trans zero_le_one⟩ : |expIntegralRemainder w| ≤ 1)

/-- Removing the logarithmic singularity leaves a remainder bounded by the lower endpoint. -/
theorem expIntegral_add_log_bounded :
    ∃ c : ℝ, ∀ x ∈ Ioc (0 : ℝ) 1, |expIntegral x + Real.log x - c| ≤ x := by
  let c := expIntegral 1 + ∫ w in (0 : ℝ)..1, expIntegralRemainder w
  refine ⟨c, ?_⟩
  intro x hx
  have hrem0x := intervalIntegrable_expIntegralRemainder (a := 0) (b := x) (le_refl 0) hx.1.le
  have hremx1 := intervalIntegrable_expIntegralRemainder (a := x) (b := 1) hx.1.le zero_le_one
  have hinvx1 : IntervalIntegrable (fun w : ℝ => w⁻¹) volume x 1 :=
    (continuousOn_id.inv₀ fun w hw =>
      ne_of_gt (hx.1.trans_le ((uIcc_of_le hx.2) ▸ hw).1)).intervalIntegrable
  have heq : expIntegral x - expIntegral 1 =
      -Real.log x + ∫ w in x..1, expIntegralRemainder w := by
    rw [expIntegral, expIntegral, integral_Ioi_sub_Ioi (integrableOn_exp_neg_div x hx.1) hx.2]
    calc
      (∫ w in x..1, Real.exp (-w) / w) =
          ∫ w in x..1, w⁻¹ + expIntegralRemainder w := by
        apply intervalIntegral.integral_congr
        intro w hw
        have hwne : w ≠ 0 := ne_of_gt (hx.1.trans_le ((uIcc_of_le hx.2) ▸ hw).1)
        dsimp only [expIntegralRemainder]
        field_simp
        ring
      _ = -Real.log x + ∫ w in x..1, expIntegralRemainder w := by
        rw [intervalIntegral.integral_add hinvx1 hremx1,
          integral_inv_of_pos hx.1 zero_lt_one, one_div, Real.log_inv]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hrem0x hremx1
  have hbound : |∫ w in (0 : ℝ)..x, expIntegralRemainder w| ≤ x := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := expIntegralRemainder) (a := 0) (b := x) (C := 1) fun w hw => ?_
    · simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos hx.1, one_mul] using hb
    · have hw0 : 0 ≤ w := ((uIoc_of_le hx.1.le) ▸ hw).1.le
      exact abs_le.mpr ⟨(expIntegralRemainder_bounds hw0).1,
        (expIntegralRemainder_bounds hw0).2.trans zero_le_one⟩
  have heq' : expIntegral x + Real.log x - c =
      -(∫ w in (0 : ℝ)..x, expIntegralRemainder w) := by
    dsimp only [c]
    linarith only [heq, hsplit]
  rw [heq', abs_neg]
  exact hbound

/-- Reciprocal substitution for the truncated exponential kernel. -/
theorem integral_exp_neg_div_div (a T : ℝ) (ha : 0 < a) (hT : 0 < T) :
    IntegrableOn (fun s : ℝ => Real.exp (-(a / s)) / s) (Ioo 0 T) ∧
      (∫ s in Ioo (0 : ℝ) T, Real.exp (-(a / s)) / s) = expIntegral (a / T) := by
  have himage : (fun s : ℝ => a / s) '' Ioo 0 T = Ioi (a / T) := by
    ext w
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact (div_lt_div_iff_of_pos_left ha hT hs.1).mpr hs.2
    · intro hw
      have hwpos : 0 < w := (div_pos ha hT).trans hw
      refine ⟨a / w, ⟨div_pos ha hwpos, ?_⟩, ?_⟩
      · exact (div_lt_iff₀ hwpos).mpr ((div_lt_iff₀ hT).mp hw |>.trans_eq (mul_comm w T))
      · field_simp
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s : ℝ => a / s) (-a / s ^ 2) (Ioo 0 T) s := by
    intro s hs
    convert! ((hasDerivAt_const s a).div (hasDerivAt_id s) (ne_of_gt hs.1)).hasDerivWithinAt using 1
    simp only [id_eq, zero_mul, mul_one, zero_sub]
  have hinj : InjOn (fun s : ℝ => a / s) (Ioo 0 T) := by
    intro s hs t ht heq
    have heq' := congrArg (fun v : ℝ => v / a) heq
    have hsne := ne_of_gt hs.1
    have htne := ne_of_gt ht.1
    field_simp at heq'
    exact heq'.symm
  have hpoint : ∀ s ∈ Ioo (0 : ℝ) T,
      |-a / s ^ 2| • (Real.exp (-(a / s)) / (a / s)) = Real.exp (-(a / s)) / s := by
    intro s hs
    rw [smul_eq_mul, abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) (sq_nonneg _) : -a / s ^ 2 ≤ 0)]
    field_simp
  have hi := (integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioo hderiv hinj (fun w : ℝ => Real.exp (-w) / w)).mp
      (himage.symm ▸ integrableOn_exp_neg_div (a / T) (div_pos ha hT))
  have hi' := hi.congr_fun hpoint measurableSet_Ioo
  refine ⟨hi', ?_⟩
  have heq := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj
    (fun w : ℝ => Real.exp (-w) / w)
  rw [himage] at heq
  exact (setIntegral_congr_fun measurableSet_Ioo hpoint).symm.trans heq.symm

/-- The truncated planar heat kernel is an exponential integral, with its integrability. -/
theorem integral_heatKernel_two_mul (T : ℝ) (z : Plane) (hT : 0 < T) (hz : z ≠ 0) :
    IntegrableOn (fun s : ℝ => heatKernel (2 * s) z) (Ioc 0 T) ∧
      (∫ s in Ioc (0 : ℝ) T, heatKernel (2 * s) z) =
        (4 * Real.pi)⁻¹ * expIntegral (‖z‖ ^ 2 / (4 * T)) := by
  have ha : 0 < ‖z‖ ^ 2 / 4 := div_pos (sq_pos_of_pos (norm_pos_iff.mpr hz)) (by norm_num)
  obtain ⟨hi, heq⟩ := integral_exp_neg_div_div (‖z‖ ^ 2 / 4) T ha hT
  have hpoint (s : ℝ) : heatKernel (2 * s) z =
      (4 * Real.pi)⁻¹ * (Real.exp (-(‖z‖ ^ 2 / 4 / s)) / s) := by
    unfold heatKernel
    have hexp : -‖z‖ ^ 2 / (2 * (2 * s)) = -(‖z‖ ^ 2 / 4 / s) := by ring
    rw [hexp]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hi' : IntegrableOn (fun s : ℝ => heatKernel (2 * s) z) (Ioo 0 T) := by
    change Integrable _ (volume.restrict (Ioo 0 T))
    have heqfun : (fun s => heatKernel (2 * s) z) =
        (fun s => (4 * Real.pi)⁻¹ * (Real.exp (-(‖z‖ ^ 2 / 4 / s)) / s)) := funext hpoint
    rw [heqfun]
    exact hi.const_mul ((4 * Real.pi)⁻¹)
  refine ⟨(integrableOn_Ioc_iff_integrableOn_Ioo).mpr hi', ?_⟩
  rw [integral_Ioc_eq_integral_Ioo]
  simp_rw [hpoint]
  rw [MeasureTheory.integral_const_mul, heq, div_div]

/-- The exponential integral decreases with its positive lower endpoint. -/
theorem expIntegral_antitoneOn : AntitoneOn expIntegral (Ioi (0 : ℝ)) := by
  intro x hx y _ hxy
  apply setIntegral_mono_set (integrableOn_exp_neg_div x hx)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with w hw
    exact div_nonneg (Real.exp_nonneg _) (hx.trans hw).le
  · exact Filter.Eventually.of_forall (Ioi_subset_Ioi hxy)

/-- A global logarithmic upper bound on the exponential integral. -/
theorem expIntegral_le_abs_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x > 0, expIntegral x ≤ C + |Real.log x| := by
  obtain ⟨c, hc⟩ := expIntegral_add_log_bounded
  refine ⟨|c| + 1 + |expIntegral 1|, by positivity, ?_⟩
  intro x hx
  by_cases hx1 : x ≤ 1
  · have h := (le_abs_self _).trans (hc x ⟨hx, hx1⟩)
    have hc' := le_abs_self c
    have hx' := neg_le_abs (Real.log x)
    have htail := abs_nonneg (expIntegral 1)
    linarith only [h, hc', hx', hx1, htail]
  · have h := expIntegral_antitoneOn zero_lt_one hx (le_of_not_ge hx1)
    have htail := le_abs_self (expIntegral 1)
    have hc' := abs_nonneg c
    have hx' := abs_nonneg (Real.log x)
    linarith only [h, htail, hc', hx']

/-- A logarithmic bound for the truncated heat kernel, uniform for `0 < T ≤ B`.

This gives in particular local uniformity when time ranges in a compact subset of
`(0,∞)`. The companion `integral_heatKernel_two_mul` supplies integrability.
-/
theorem integral_heatKernel_two_mul_le (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ B → ∀ z : Plane, z ≠ 0 →
      (∫ s in Ioc (0 : ℝ) T, heatKernel (2 * s) z) ≤ C * (1 + |Real.log ‖z‖|) := by
  obtain ⟨A, hA, hAb⟩ := expIntegral_le_abs_log
  let D := A + |Real.log (4 * B)| + 2
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨(4 * Real.pi)⁻¹ * D, by positivity, ?_⟩
  intro T hT hTB z hz
  rw [(integral_heatKernel_two_mul T z hT hz).2]
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hxT : 0 < ‖z‖ ^ 2 / (4 * T) := by positivity
  have hxB : 0 < ‖z‖ ^ 2 / (4 * B) := by positivity
  have htime : ‖z‖ ^ 2 / (4 * B) ≤ ‖z‖ ^ 2 / (4 * T) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith only [hTB])
  have hE := (expIntegral_antitoneOn hxB hxT htime).trans (hAb _ hxB)
  have hlog : |Real.log (‖z‖ ^ 2 / (4 * B))| ≤
      2 * |Real.log ‖z‖| + |Real.log (4 * B)| := by
    rw [Real.log_div (ne_of_gt (sq_pos_of_pos hzpos)) (ne_of_gt (by positivity : 0 < 4 * B)),
      Real.log_pow]
    calc
      |(2 : ℝ) * Real.log ‖z‖ - Real.log (4 * B)| ≤
          |(2 : ℝ) * Real.log ‖z‖| + |Real.log (4 * B)| := abs_sub _ _
      _ = _ := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hplain : A + (2 * |Real.log ‖z‖| + |Real.log (4 * B)|) ≤
      D * (1 + |Real.log ‖z‖|) := by
    dsimp only [D]
    nlinarith only [hA, abs_nonneg (Real.log ‖z‖), abs_nonneg (Real.log (4 * B))]
  calc
    (4 * Real.pi)⁻¹ * expIntegral (‖z‖ ^ 2 / (4 * T)) ≤
        (4 * Real.pi)⁻¹ * (D * (1 + |Real.log ‖z‖|)) :=
      mul_le_mul_of_nonneg_left (hE.trans ((add_le_add (le_refl A) hlog).trans hplain)) (by positivity)
    _ = _ := (mul_assoc _ _ _).symm

/-- Uniform expansion of the truncated heat kernel on the range needed for
compactly supported tests. The additive constant will cancel against zero mass. -/
theorem integral_heatKernel_two_mul_expansion :
    ∃ c : ℝ, ∀ T : ℝ, 0 < T → ∀ z : Plane, z ≠ 0 → ‖z‖ ^ 2 ≤ 4 * T →
      |4 * Real.pi * (∫ s in Ioc (0 : ℝ) T, heatKernel (2 * s) z) -
        (c + Real.log (4 * T) - 2 * Real.log ‖z‖)| ≤ ‖z‖ ^ 2 / (4 * T) := by
  obtain ⟨c, hc⟩ := expIntegral_add_log_bounded
  refine ⟨c, ?_⟩
  intro T hT z hz hnorm
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h4T : 0 < 4 * T := by positivity
  have hx : ‖z‖ ^ 2 / (4 * T) ∈ Ioc (0 : ℝ) 1 :=
    ⟨div_pos (sq_pos_of_pos hn) h4T, (div_le_one h4T).mpr hnorm⟩
  rw [(integral_heatKernel_two_mul T z hT hz).2, ← mul_assoc,
    mul_inv_cancel₀ (ne_of_gt (by positivity : 0 < 4 * Real.pi)), one_mul]
  have hlog : Real.log (‖z‖ ^ 2 / (4 * T)) =
      2 * Real.log ‖z‖ - Real.log (4 * T) := by
    rw [Real.log_div (ne_of_gt (sq_pos_of_pos hn)) (ne_of_gt h4T), Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  convert hc _ hx using 1
  rw [hlog]
  congr 1
  ring

end Critical2DKPZ.Extensions.GffTangent

end

end
