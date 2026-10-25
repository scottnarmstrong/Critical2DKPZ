/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # Scalar estimates for logarithms of positively associated masses -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace Critical2DKPZ.Extensions.GffTangent

/-- The logarithm truncated from below at the positive mass threshold `β`. -/
noncomputable def truncatedLog (β z : ℝ) : ℝ := Real.log (max z β)

/-- The discarded lower logarithmic tail. -/
noncomputable def logRemainder (β z : ℝ) : ℝ := Real.log z - truncatedLog β z

/-- Both parts of the logarithm are dominated by the full logarithm when the
mass is positive and the truncation threshold is at most one. -/
theorem abs_truncatedLog_and_remainder_le {β z : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hz : 0 < z) : |truncatedLog β z| ≤ |Real.log z| ∧ |logRemainder β z| ≤ |Real.log z| := by
  by_cases h : β ≤ z
  · simp only [truncatedLog, logRemainder, max_eq_left h, sub_self, abs_zero, le_refl,
      abs_nonneg, and_self]
  · have hzb : z ≤ β := (lt_of_not_ge h).le
    have hlog : Real.log z ≤ Real.log β := Real.log_le_log hz hzb
    have hlogβ : Real.log β ≤ 0 := Real.log_nonpos hβ.le hβ1
    have hlogz : Real.log z ≤ 0 := hlog.trans hlogβ
    rw [truncatedLog, logRemainder, truncatedLog, max_eq_right hzb,
      abs_of_nonpos hlogβ, abs_of_nonpos hlogz,
      abs_of_nonpos (sub_nonpos.mpr hlog)]
    constructor <;> linarith only [hlog, hlogβ]

/-- A pure algebra estimate used after `log q ≤ q - 1`. It is stronger than
needed for the coefficient one eighth in the integral remainder bound. -/
theorem sq_le_fourth_div_sixteen {q L : ℝ} (hL : 0 ≤ L) (hLq : L ≤ q - 1) :
    L ^ 2 ≤ q ^ 4 / 16 := by
  have hb : L ≤ q ^ 2 / 4 := by
    have hs := sq_nonneg (q - 2)
    nlinarith only [hLq, hs]
  have hs := mul_self_le_mul_self hL hb
  calc
    L ^ 2 ≤ (q ^ 2 / 4) ^ 2 := by simpa only [pow_two] using hs
    _ = q ^ 4 / 16 := by ring

/-- The squared discarded logarithm is pointwise controlled by the fourth
inverse mass. Positivity is an essential domain condition. -/
theorem sq_logRemainder_le {β z : ℝ} (hβ : 0 < β) (hz : 0 < z) :
    logRemainder β z ^ 2 ≤ β ^ 4 * z⁻¹ ^ 4 / 8 := by
  by_cases h : β ≤ z
  · simp only [logRemainder, truncatedLog, max_eq_left h, sub_self, zero_pow (by decide : 2 ≠ 0)]
    positivity
  have hzβ : z < β := lt_of_not_ge h
  have hq : 0 < β / z := div_pos hβ hz
  have hq1 : 1 ≤ β / z := (one_le_div hz).mpr hzβ.le
  have hlogq : 0 ≤ Real.log (β / z) := Real.log_nonneg hq1
  have hb := sq_le_fourth_div_sixteen hlogq (Real.log_le_sub_one_of_pos hq)
  have hr : logRemainder β z = -Real.log (β / z) := by
    rw [logRemainder, truncatedLog, max_eq_right hzβ.le, Real.log_div hβ.ne' hz.ne']
    ring
  rw [hr, neg_sq]
  calc
    Real.log (β / z) ^ 2 ≤ (β / z) ^ 4 / 16 := hb
    _ ≤ (β / z) ^ 4 / 8 := by
      have hn : 0 ≤ (β / z) ^ 4 := pow_nonneg hq.le _
      linarith only [hn]
    _ = β ^ 4 * z⁻¹ ^ 4 / 8 := by simp only [div_eq_mul_inv, mul_pow, inv_pow]

/-- The remainder square is integrable and obeys the source's exact one-eighth
bound. This follows from a stronger pointwise one-sixteenth estimate. -/
theorem integral_sq_remainder_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X : Ω → ℝ} (hX : AEMeasurable X P) (hpos : ∀ᵐ ω ∂P, 0 < X ω)
    (hInv : Integrable (fun ω => (X ω)⁻¹ ^ 4) P) {β : ℝ} (hβ : 0 < β) :
    Integrable (fun ω => logRemainder β (X ω) ^ 2) P ∧
      (∫ ω, logRemainder β (X ω) ^ 2 ∂P) ≤ β ^ 4 * (∫ ω, (X ω)⁻¹ ^ 4 ∂P) / 8 := by
  have hm : AEMeasurable (fun ω => logRemainder β (X ω)) P :=
    (Real.measurable_log.comp_aemeasurable hX).sub
      (Real.measurable_log.comp_aemeasurable (hX.max aemeasurable_const))
  have hbound : ∀ᵐ ω ∂P, logRemainder β (X ω) ^ 2 ≤ (β ^ 4 / 8) * (X ω)⁻¹ ^ 4 := by
    filter_upwards [hpos] with ω hω
    have h := sq_logRemainder_le hβ hω
    linarith only [h]
  have hi : Integrable (fun ω => logRemainder β (X ω) ^ 2) P := by
    apply (hInv.const_mul (β ^ 4 / 8)).mono' (hm.pow_const 2).aestronglyMeasurable
    filter_upwards [hbound] with ω hω
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hω
  refine ⟨hi, ?_⟩
  have hb := integral_mono_ae hi (hInv.const_mul (β ^ 4 / 8)) hbound
  rw [integral_const_mul] at hb
  calc
    (∫ ω, logRemainder β (X ω) ^ 2 ∂P) ≤ (β ^ 4 / 8) * ∫ ω, (X ω)⁻¹ ^ 4 ∂P := hb
    _ = _ := by ring

/-- Weighted double layer cake for two nonnegative variables. The primitive
form makes the absolute-continuity content explicit without selecting derivatives.
This equality is valid before imposing any moment finiteness. -/
theorem lintegral_primitive_product_eq_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX0 : ∀ ω, 0 ≤ X ω) (hY0 : ∀ ω, 0 ≤ Y ω)
    (k l : ℝ → ℝ) (hl : Measurable l)
    (hki : ∀ t > 0, IntervalIntegrable k volume 0 t)
    (hli : ∀ t > 0, IntervalIntegrable l volume 0 t)
    (hkn : ∀ t > 0, 0 ≤ k t) (hln : ∀ t > 0, 0 ≤ l t)
    (hF : AEMeasurable (fun ω => ∫ t in 0..X ω, k t) P)
    (hG : AEMeasurable (fun ω => ∫ t in 0..Y ω, l t) P) :
    (∫⁻ ω, ENNReal.ofReal (∫ t in 0..X ω, k t) *
      ENNReal.ofReal (∫ t in 0..Y ω, l t) ∂P) =
    ∫⁻ u in Ioi 0, ∫⁻ v in Ioi 0,
      P {ω | u < X ω ∧ v < Y ω} * ENNReal.ofReal (k u) * ENNReal.ofReal (l v) := by
  let G : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (∫ t in 0..Y ω, l t)
  have hx := lintegral_comp_eq_lintegral_meas_lt_mul (P.withDensity G)
    (Filter.Eventually.of_forall hX0) hX.aemeasurable hki
    (ae_restrict_of_forall_mem measurableSet_Ioi hkn)
  rw [lintegral_withDensity_eq_lintegral_mul₀ hG.ennreal_ofReal hF.ennreal_ofReal] at hx
  change (∫⁻ ω, G ω * ENNReal.ofReal (∫ t in 0..X ω, k t) ∂P) = _ at hx
  have hleft : (∫⁻ ω, ENNReal.ofReal (∫ t in 0..X ω, k t) *
      ENNReal.ofReal (∫ t in 0..Y ω, l t) ∂P) =
      ∫⁻ ω, G ω * ENNReal.ofReal (∫ t in 0..X ω, k t) ∂P := by
    apply lintegral_congr
    intro ω
    exact mul_comm _ _
  rw [hleft, hx]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro u _
  change (P.withDensity G) {ω | u < X ω} * ENNReal.ofReal (k u) = _
  have hXu : MeasurableSet {ω | u < X ω} := measurableSet_lt measurable_const hX
  have hy := lintegral_comp_eq_lintegral_meas_lt_mul (P.restrict {ω | u < X ω})
    (Filter.Eventually.of_forall hY0) hY.aemeasurable hli
    (ae_restrict_of_forall_mem measurableSet_Ioi hln)
  have hevent (v : ℝ) : (P.restrict {ω | u < X ω}) {ω | v < Y ω} =
      P {ω | u < X ω ∧ v < Y ω} := by
    rw [Measure.restrict_apply (measurableSet_lt measurable_const hY)]
    congr 1
    ext ω
    exact and_comm
  simp_rw [hevent] at hy
  rw [withDensity_apply G hXu]
  change (∫⁻ ω in {ω | u < X ω}, ENNReal.ofReal (∫ t in 0..Y ω, l t) ∂P) *
    ENNReal.ofReal (k u) = _
  rw [hy]
  have ht : Measurable (fun v => P {ω | u < X ω ∧ v < Y ω}) :=
    Antitone.measurable (fun a b hab => measure_mono (fun ω hω => ⟨hω.1, hab.trans_lt hω.2⟩))
  have hmprod : Measurable (fun v => P {ω | u < X ω ∧ v < Y ω} * ENNReal.ofReal (l v)) :=
    ht.mul hl.ennreal_ofReal
  rw [← lintegral_mul_const (ENNReal.ofReal (k u)) hmprod]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro v _
  ac_rfl

/-- Positive quadrant dependence, in probability-measure form. -/
def PosQuadrantDependent {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : Ω → ℝ) : Prop :=
  ∀ u v : ℝ, P {ω | u < X ω} * P {ω | v < Y ω} ≤ P {ω | u < X ω ∧ v < Y ω}

/-- A primitive of a nonnegative kernel is nonnegative on the positive half-line. -/
theorem integral_primitive_nonneg {k : ℝ → ℝ} (hk : ∀ t > 0, 0 ≤ k t)
    {z : ℝ} (hz : 0 ≤ z) : 0 ≤ ∫ t in 0..z, k t := by
  rw [intervalIntegral.integral_of_le hz]
  exact integral_nonneg_of_ae
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => hk t ht.1))

/-- Hoeffding's covariance identity for nonnegative integral primitives of two
positively quadrant dependent variables. The ENNReal form records the nonnegative
covariance kernel and is finite because both primitive variables are in L². -/
theorem covariance_primitive_eq_lintegral_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hX0 : ∀ ω, 0 ≤ X ω) (hY0 : ∀ ω, 0 ≤ Y ω)
    (k l : ℝ → ℝ) (hk : Measurable k) (hl : Measurable l)
    (hki : ∀ t > 0, IntervalIntegrable k volume 0 t)
    (hli : ∀ t > 0, IntervalIntegrable l volume 0 t)
    (hkn : ∀ t > 0, 0 ≤ k t) (hln : ∀ t > 0, 0 ≤ l t)
    (hF : MemLp (fun ω => ∫ t in 0..X ω, k t) 2 P)
    (hG : MemLp (fun ω => ∫ t in 0..Y ω, l t) 2 P)
    (hQ : PosQuadrantDependent P X Y) :
    0 ≤ covariance (fun ω => ∫ t in 0..X ω, k t) (fun ω => ∫ t in 0..Y ω, l t) P ∧
    ENNReal.ofReal (covariance (fun ω => ∫ t in 0..X ω, k t)
      (fun ω => ∫ t in 0..Y ω, l t) P) =
      ∫⁻ u in Ioi 0, ∫⁻ v in Ioi 0,
        (P {ω | u < X ω ∧ v < Y ω} - P {ω | u < X ω} * P {ω | v < Y ω}) *
          ENNReal.ofReal (k u) * ENNReal.ofReal (l v) := by
  let F : Ω → ℝ := fun ω => ∫ t in 0..X ω, k t
  let G : Ω → ℝ := fun ω => ∫ t in 0..Y ω, l t
  let TX : ℝ → ℝ≥0∞ := fun u => P {ω | u < X ω}
  let TY : ℝ → ℝ≥0∞ := fun v => P {ω | v < Y ω}
  let A : ℝ → ℝ → ℝ≥0∞ := fun u v =>
    P {ω | u < X ω ∧ v < Y ω} * ENNReal.ofReal (k u) * ENNReal.ofReal (l v)
  let B : ℝ → ℝ → ℝ≥0∞ := fun u v =>
    TX u * TY v * ENNReal.ofReal (k u) * ENNReal.ofReal (l v)
  let bX := ∫⁻ u in Ioi 0, TX u * ENNReal.ofReal (k u)
  let bY := ∫⁻ v in Ioi 0, TY v * ENNReal.ofReal (l v)
  have hFn : ∀ ω, 0 ≤ F ω := fun ω => integral_primitive_nonneg hkn (hX0 ω)
  have hGn : ∀ ω, 0 ≤ G ω := fun ω => integral_primitive_nonneg hln (hY0 ω)
  have hFm : 0 ≤ ∫ ω, F ω ∂P := integral_nonneg hFn
  have hGm : 0 ≤ ∫ ω, G ω ∂P := integral_nonneg hGn
  have hFGi : Integrable (fun ω => F ω * G ω) P := hF.integrable_mul hG
  have hFGn : ∀ ω, 0 ≤ F ω * G ω := fun ω => mul_nonneg (hFn ω) (hGn ω)
  have hFGm : 0 ≤ ∫ ω, F ω * G ω ∂P := integral_nonneg hFGn
  have hTX : Measurable TX :=
    Antitone.measurable (fun a b hab => measure_mono (fun ω hω => hab.trans_lt hω))
  have hTY : Measurable TY :=
    Antitone.measurable (fun a b hab => measure_mono (fun ω hω => hab.trans_lt hω))
  have hKX : Measurable (fun u => TX u * ENNReal.ofReal (k u)) := hTX.mul hk.ennreal_ofReal
  have hKY : Measurable (fun v => TY v * ENNReal.ofReal (l v)) := hTY.mul hl.ennreal_ofReal
  have hbX : bX = ENNReal.ofReal (∫ ω, F ω ∂P) := by
    have h := lintegral_comp_eq_lintegral_meas_lt_mul P
      (Filter.Eventually.of_forall hX0) hX.aemeasurable hki
      (ae_restrict_of_forall_mem measurableSet_Ioi hkn)
    exact h.symm.trans (ofReal_integral_eq_lintegral_ofReal
      (hF.integrable (by norm_num)) (Filter.Eventually.of_forall hFn)).symm
  have hbY : bY = ENNReal.ofReal (∫ ω, G ω ∂P) := by
    have h := lintegral_comp_eq_lintegral_meas_lt_mul P
      (Filter.Eventually.of_forall hY0) hY.aemeasurable hli
      (ae_restrict_of_forall_mem measurableSet_Ioi hln)
    exact h.symm.trans (ofReal_integral_eq_lintegral_ofReal
      (hG.integrable (by norm_num)) (Filter.Eventually.of_forall hGn)).symm
  have hA : (∫⁻ u in Ioi 0, ∫⁻ v in Ioi 0, A u v) =
      ENNReal.ofReal (∫ ω, F ω * G ω ∂P) := by
    rw [← lintegral_primitive_product_eq_tail P hX hY hX0 hY0 k l hl hki hli hkn hln
      hF.aemeasurable hG.aemeasurable]
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (F ω * G ω) ∂P :=
        lintegral_congr (fun ω => (ENNReal.ofReal_mul (hFn ω)).symm)
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hFGi (Filter.Eventually.of_forall hFGn)).symm
  have hBI (u : ℝ) : (∫⁻ v in Ioi 0, B u v) = (TX u * ENNReal.ofReal (k u)) * bY := by
    have heq : (fun v => B u v) = fun v => (TX u * ENNReal.ofReal (k u)) *
        (TY v * ENNReal.ofReal (l v)) := by funext v; dsimp [B]; ac_rfl
    rw [heq, lintegral_const_mul _ hKY]
  have hB : (∫⁻ u in Ioi 0, ∫⁻ v in Ioi 0, B u v) =
      ENNReal.ofReal ((∫ ω, F ω ∂P) * (∫ ω, G ω ∂P)) := by
    simp_rw [hBI]
    rw [lintegral_mul_const bY hKX]
    change bX * bY = _
    rw [hbX, hbY, ENNReal.ofReal_mul hFm]
  have hBfin : (∫⁻ u in Ioi 0, ∫⁻ v in Ioi 0, B u v) ≠ ∞ := by rw [hB]; exact ENNReal.ofReal_ne_top
  have hBIfin (u : ℝ) : (∫⁻ v in Ioi 0, B u v) ≠ ∞ := by
    rw [hBI, hbY]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (measure_ne_top P _) ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  have hBm (u : ℝ) : Measurable (fun v => B u v) :=
    ((measurable_const.mul hTY).mul measurable_const).mul hl.ennreal_ofReal
  have hBIm : Measurable (fun u => ∫⁻ v in Ioi 0, B u v) := by
    have heq : (fun u => ∫⁻ v in Ioi 0, B u v) = fun u =>
        (TX u * ENNReal.ofReal (k u)) * bY := funext hBI
    rw [heq]
    exact hKX.mul_const bY
  have hBA (u v : ℝ) : B u v ≤ A u v :=
    mul_le_mul (mul_le_mul (hQ u v) le_rfl bot_le bot_le) le_rfl bot_le bot_le
  have hle : ENNReal.ofReal ((∫ ω, F ω ∂P) * (∫ ω, G ω ∂P)) ≤
      ENNReal.ofReal (∫ ω, F ω * G ω ∂P) := by
    rw [← hB, ← hA]
    exact lintegral_mono (fun u => lintegral_mono (hBA u))
  have hCov : 0 ≤ covariance F G P := by
    rw [covariance_eq_sub hF hG]
    exact sub_nonneg.mpr ((ENNReal.ofReal_le_ofReal_iff hFGm).mp hle)
  refine ⟨hCov, ?_⟩
  have hsplit (u v : ℝ) :
      (P {ω | u < X ω ∧ v < Y ω} - TX u * TY v) *
        ENNReal.ofReal (k u) * ENNReal.ofReal (l v) = A u v - B u v := by
    rw [ENNReal.sub_mul (fun _ _ => ENNReal.ofReal_ne_top),
      ENNReal.sub_mul (fun _ _ => ENNReal.ofReal_ne_top)]
  have hsubI (u : ℝ) : (∫⁻ v in Ioi 0, A u v - B u v) =
      (∫⁻ v in Ioi 0, A u v) - ∫⁻ v in Ioi 0, B u v :=
    lintegral_sub (hBm u) (hBIfin u) (Filter.Eventually.of_forall (hBA u))
  have hgap : (∫⁻ u in Ioi 0, ∫⁻ v in Ioi 0,
      (P {ω | u < X ω ∧ v < Y ω} - TX u * TY v) *
        ENNReal.ofReal (k u) * ENNReal.ofReal (l v)) =
      (∫⁻ u in Ioi 0, ∫⁻ v in Ioi 0, A u v) - ∫⁻ u in Ioi 0, ∫⁻ v in Ioi 0, B u v := by
    simp_rw [hsplit, hsubI]
    exact lintegral_sub hBIm hBfin (Filter.Eventually.of_forall fun u => lintegral_mono (hBA u))
  rw [hA, hB] at hgap
  change ENNReal.ofReal (covariance F G P) = _
  rw [covariance_eq_sub hF hG, ENNReal.ofReal_sub _ (mul_nonneg hFm hGm)]
  exact hgap.symm

/-- Bounded nonnegative primitive kernels contract the covariance of a positive
quadrant dependent pair by the product of their bounds. -/
theorem covariance_primitives_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hX0 : ∀ ω, 0 ≤ X ω) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hX2 : MemLp X 2 P) (hY2 : MemLp Y 2 P)
    (k l : ℝ → ℝ) (hk : Measurable k) (hl : Measurable l)
    (hki : ∀ t > 0, IntervalIntegrable k volume 0 t)
    (hli : ∀ t > 0, IntervalIntegrable l volume 0 t)
    (hkn : ∀ t > 0, 0 ≤ k t) (hln : ∀ t > 0, 0 ≤ l t)
    (hF : MemLp (fun ω => ∫ t in 0..X ω, k t) 2 P)
    (hG : MemLp (fun ω => ∫ t in 0..Y ω, l t) 2 P)
    {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hkB : ∀ u, k u ≤ K) (hlB : ∀ v, l v ≤ L)
    (hQ : PosQuadrantDependent P X Y) :
    0 ≤ covariance (fun ω => ∫ t in 0..X ω, k t) (fun ω => ∫ t in 0..Y ω, l t) P ∧
    covariance (fun ω => ∫ t in 0..X ω, k t) (fun ω => ∫ t in 0..Y ω, l t) P ≤
      K * L * covariance X Y P := by
  obtain ⟨hpos, heq⟩ := covariance_primitive_eq_lintegral_tail P hX hY hX0 hY0
    k l hk hl hki hli hkn hln hF hG hQ
  have hid (z : ℝ) : (∫ t in 0..z, (1 : ℝ)) = z := by
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  obtain ⟨hmass, hmassEq⟩ := covariance_primitive_eq_lintegral_tail P hX hY hX0 hY0
    (fun _ => 1) (fun _ => 1) measurable_const measurable_const
    (fun _ _ => intervalIntegrable_const) (fun _ _ => intervalIntegrable_const)
    (fun _ _ => zero_le_one) (fun _ _ => zero_le_one)
    (by simpa only [hid] using hX2) (by simpa only [hid] using hY2) hQ
  simp only [hid, ENNReal.ofReal_one, mul_one] at hmass hmassEq
  let Q : ℝ → ℝ → ℝ≥0∞ := fun u v =>
    P {ω | u < X ω ∧ v < Y ω} - P {ω | u < X ω} * P {ω | v < Y ω}
  have hpoint (u v : ℝ) : Q u v * ENNReal.ofReal (k u) * ENNReal.ofReal (l v) ≤
      ENNReal.ofReal (K * L) * Q u v := by
    calc
      _ ≤ Q u v * ENNReal.ofReal K * ENNReal.ofReal L :=
        mul_le_mul (mul_le_mul le_rfl (ENNReal.ofReal_le_ofReal (hkB u)) bot_le bot_le)
          (ENNReal.ofReal_le_ofReal (hlB v)) bot_le bot_le
      _ = _ := by rw [ENNReal.ofReal_mul hK]; ac_rfl
  have hb := lintegral_mono (μ := volume.restrict (Ioi (0 : ℝ))) fun u =>
    lintegral_mono (μ := volume.restrict (Ioi (0 : ℝ))) (hpoint u)
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hb
  dsimp only [Q] at hb
  rw [← heq, ← hmassEq] at hb
  rw [← ENNReal.ofReal_mul (mul_nonneg hK hL)] at hb
  exact ⟨hpos, (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg hK hL) hmass)).mp hb⟩

/-- The nonnegative kernel of the lower-truncated logarithm. -/
noncomputable def logTruncationKernel (β u : ℝ) : ℝ := if β < u then u⁻¹ else 0

/-- The truncation kernel is measurable. -/
theorem measurable_logTruncationKernel (β : ℝ) : Measurable (logTruncationKernel β) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_inv measurable_const

/-- A positive truncation threshold bounds the kernel uniformly. -/
theorem logTruncationKernel_bounds {β : ℝ} (hβ : 0 < β) (u : ℝ) :
    0 ≤ logTruncationKernel β u ∧ logTruncationKernel β u ≤ β⁻¹ := by
  by_cases hu : β < u
  · rw [logTruncationKernel, ite_eq_left hu]
    exact ⟨inv_nonneg.mpr (hβ.trans hu).le, inv_anti₀ hβ hu.le⟩
  · rw [logTruncationKernel, ite_eq_right hu]
    exact ⟨le_rfl, inv_nonneg.mpr hβ.le⟩

/-- The bounded kernel is integrable on every interval from zero. -/
theorem intervalIntegrable_logTruncationKernel {β : ℝ} (hβ : 0 < β)
    (t : ℝ) (ht : 0 < t) : IntervalIntegrable (logTruncationKernel β) volume 0 t := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le ht.le).mpr
  apply (integrable_const (β⁻¹) : Integrable (fun _ : ℝ => β⁻¹) (volume.restrict (Icc 0 t))).mono'
    (measurable_logTruncationKernel β).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_of_nonneg (logTruncationKernel_bounds hβ u).1]
    exact (logTruncationKernel_bounds hβ u).2

/-- The truncated logarithm, shifted to vanish at zero, is the primitive of
its bounded nonnegative kernel. -/
theorem integral_logTruncationKernel {β z : ℝ} (hβ : 0 < β) (hz : 0 ≤ z) :
    (∫ u in 0..z, logTruncationKernel β u) = truncatedLog β z - Real.log β := by
  have hzero : ∀ r : ℝ, 0 ≤ r → r ≤ β → (∫ u in 0..r, logTruncationKernel β u) = 0 := by
    intro r hr hrβ
    rw [intervalIntegral.integral_of_le hr]
    calc
      _ = ∫ _ in Ioc (0 : ℝ) r, (0 : ℝ) :=
        setIntegral_congr_fun measurableSet_Ioc (fun u hu => by
          rw [logTruncationKernel, ite_eq_right (not_lt.mpr (hu.2.trans hrβ))])
      _ = 0 := integral_zero _ _
  by_cases hzβ : z ≤ β
  · rw [hzero z hz hzβ, truncatedLog, max_eq_right hzβ, sub_self]
  have hβz : β < z := lt_of_not_ge hzβ
  have h0β := intervalIntegrable_logTruncationKernel hβ β hβ
  have h0z := intervalIntegrable_logTruncationKernel hβ z (hβ.trans hβz)
  rw [← intervalIntegral.integral_add_adjacent_intervals h0β (h0β.symm.trans h0z),
    hzero β hβ.le le_rfl, zero_add]
  have heq : (∫ u in β..z, logTruncationKernel β u) = ∫ u in β..z, u⁻¹ := by
    rw [intervalIntegral.integral_of_le hβz.le, intervalIntegral.integral_of_le hβz.le]
    exact setIntegral_congr_fun measurableSet_Ioc (fun u hu => by rw [logTruncationKernel, ite_eq_left hu.1])
  rw [heq, integral_inv_of_pos hβ (hβ.trans hβz), Real.log_div (hβ.trans hβz).ne' hβ.ne',
    truncatedLog, max_eq_left hβz.le]

/-- Covariance is unchanged under almost everywhere equality of both variables. -/
theorem covariance_congr_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X X' Y Y' : Ω → ℝ} (hX : X =ᵐ[P] X') (hY : Y =ᵐ[P] Y') :
    covariance X Y P = covariance X' Y' P := by
  unfold covariance
  rw [integral_congr_ae hX, integral_congr_ae hY]
  apply integral_congr_ae
  filter_upwards [hX, hY] with ω hx hy
  rw [hx, hy]

/-- Positive quadrant dependence depends only on the almost everywhere classes. -/
theorem PosQuadrantDependent.congr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X X' Y Y' : Ω → ℝ} (hQ : PosQuadrantDependent P X Y)
    (hX : X =ᵐ[P] X') (hY : Y =ᵐ[P] Y') : PosQuadrantDependent P X' Y' := by
  intro u v
  have hx : P {ω | u < X ω} = P {ω | u < X' ω} :=
    measure_congr (hX.mono (fun ω hω => congrArg (fun z => u < z) hω))
  have hy : P {ω | v < Y ω} = P {ω | v < Y' ω} :=
    measure_congr (hY.mono (fun ω hω => congrArg (fun z => v < z) hω))
  have hxy : P {ω | u < X ω ∧ v < Y ω} = P {ω | u < X' ω ∧ v < Y' ω} := by
    apply measure_congr
    filter_upwards [hX, hY] with ω hx hy
    rw [hx, hy]
  rw [← hx, ← hy, ← hxy]
  exact hQ u v

/-- Truncated logarithms of measurable nonnegative masses satisfy the covariance
contraction. The L² log premises supply all needed integral linearity. -/
theorem covariance_le_truncation_of_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (hX0 : ∀ ω, 0 ≤ X ω) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hpos : ∀ᵐ ω ∂P, 0 < X ω ∧ 0 < Y ω)
    (hX2 : MemLp X 2 P) (hY2 : MemLp Y 2 P)
    (hLX2 : MemLp (fun ω => Real.log (X ω)) 2 P)
    (hLY2 : MemLp (fun ω => Real.log (Y ω)) 2 P)
    (hQ : PosQuadrantDependent P X Y) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    0 ≤ covariance (fun ω => truncatedLog β (X ω)) (fun ω => truncatedLog β (Y ω)) P ∧
      covariance (fun ω => truncatedLog β (X ω)) (fun ω => truncatedLog β (Y ω)) P ≤
        (β⁻¹) ^ 2 * covariance X Y P := by
  have hTXm : Measurable (fun ω => truncatedLog β (X ω)) :=
    Real.measurable_log.comp (hX.max measurable_const)
  have hTYm : Measurable (fun ω => truncatedLog β (Y ω)) :=
    Real.measurable_log.comp (hY.max measurable_const)
  have hTX2 : MemLp (fun ω => truncatedLog β (X ω)) 2 P := by
    apply hLX2.norm.mono' hTXm.aestronglyMeasurable
    filter_upwards [hpos] with ω hω
    simpa only [Real.norm_eq_abs] using (abs_truncatedLog_and_remainder_le hβ hβ1 hω.1).1
  have hTY2 : MemLp (fun ω => truncatedLog β (Y ω)) 2 P := by
    apply hLY2.norm.mono' hTYm.aestronglyMeasurable
    filter_upwards [hpos] with ω hω
    simpa only [Real.norm_eq_abs] using (abs_truncatedLog_and_remainder_le hβ hβ1 hω.2).1
  have hFX : (fun ω => ∫ u in 0..X ω, logTruncationKernel β u) =
      fun ω => truncatedLog β (X ω) - Real.log β :=
    funext (fun ω => integral_logTruncationKernel hβ (hX0 ω))
  have hFY : (fun ω => ∫ u in 0..Y ω, logTruncationKernel β u) =
      fun ω => truncatedLog β (Y ω) - Real.log β :=
    funext (fun ω => integral_logTruncationKernel hβ (hY0 ω))
  have hF2 : MemLp (fun ω => ∫ u in 0..X ω, logTruncationKernel β u) 2 P := by
    rw [hFX]
    exact hTX2.sub (memLp_const _)
  have hG2 : MemLp (fun ω => ∫ u in 0..Y ω, logTruncationKernel β u) 2 P := by
    rw [hFY]
    exact hTY2.sub (memLp_const _)
  have hc := covariance_primitives_le P hX hY hX0 hY0 hX2 hY2
    (logTruncationKernel β) (logTruncationKernel β)
    (measurable_logTruncationKernel β) (measurable_logTruncationKernel β)
    (intervalIntegrable_logTruncationKernel hβ) (intervalIntegrable_logTruncationKernel hβ)
    (fun u _ => (logTruncationKernel_bounds hβ u).1) (fun u _ => (logTruncationKernel_bounds hβ u).1)
    hF2 hG2 (inv_nonneg.mpr hβ.le) (inv_nonneg.mpr hβ.le)
    (fun u => (logTruncationKernel_bounds hβ u).2) (fun u => (logTruncationKernel_bounds hβ u).2) hQ
  have hcov : covariance (fun ω => ∫ u in 0..X ω, logTruncationKernel β u)
      (fun ω => ∫ u in 0..Y ω, logTruncationKernel β u) P =
      covariance (fun ω => truncatedLog β (X ω)) (fun ω => truncatedLog β (Y ω)) P := by
    rw [hFX, hFY, covariance_sub_const_left (hTX2.integrable (by norm_num)),
      covariance_sub_const_right (hTY2.integrable (by norm_num))]
  rw [hcov] at hc
  simpa only [pow_two] using hc

/-- The truncation covariance bound for a.e. measurable positive masses. No
measurable representative or pointwise positivity is imposed on the input. -/
theorem covariance_le_truncation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hpos : ∀ᵐ ω ∂P, 0 < X ω ∧ 0 < Y ω)
    (hX2 : MemLp X 2 P) (hY2 : MemLp Y 2 P)
    (hLX2 : MemLp (fun ω => Real.log (X ω)) 2 P)
    (hLY2 : MemLp (fun ω => Real.log (Y ω)) 2 P)
    (hQ : PosQuadrantDependent P X Y) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    0 ≤ covariance (fun ω => truncatedLog β (X ω)) (fun ω => truncatedLog β (Y ω)) P ∧
      covariance (fun ω => truncatedLog β (X ω)) (fun ω => truncatedLog β (Y ω)) P ≤
        (β⁻¹) ^ 2 * covariance X Y P := by
  let Xm := hX2.aemeasurable.mk X
  let Ym := hY2.aemeasurable.mk Y
  let Xp := fun ω => max (Xm ω) 0
  let Yp := fun ω => max (Ym ω) 0
  have hXm : Measurable Xp := hX2.aemeasurable.measurable_mk.max measurable_const
  have hYm : Measurable Yp := hY2.aemeasurable.measurable_mk.max measurable_const
  have heX : X =ᵐ[P] Xp := by
    filter_upwards [hX2.aemeasurable.ae_eq_mk, hpos] with ω hx hω
    dsimp [Xp, Xm]
    rw [← hx, max_eq_left hω.1.le]
  have heY : Y =ᵐ[P] Yp := by
    filter_upwards [hY2.aemeasurable.ae_eq_mk, hpos] with ω hy hω
    dsimp [Yp, Ym]
    rw [← hy, max_eq_left hω.2.le]
  have hposp : ∀ᵐ ω ∂P, 0 < Xp ω ∧ 0 < Yp ω := by
    filter_upwards [hpos, heX, heY] with ω hω hx hy
    rw [← hx, ← hy]
    exact hω
  have hp := covariance_le_truncation_of_measurable P hXm hYm
    (fun ω => le_max_right _ _) (fun ω => le_max_right _ _) hposp
    ((memLp_congr_ae heX).mp hX2) ((memLp_congr_ae heY).mp hY2)
    ((memLp_congr_ae (heX.mono (fun ω hx => congrArg Real.log hx))).mp hLX2)
    ((memLp_congr_ae (heY.mono (fun ω hy => congrArg Real.log hy))).mp hLY2) (hQ.congr heX heY) hβ hβ1
  have hc := covariance_congr_ae P
    (heX.mono (fun ω hx => congrArg (truncatedLog β) hx))
    (heY.mono (fun ω hy => congrArg (truncatedLog β) hy))
  rw [← hc, ← covariance_congr_ae P heX heY] at hp
  exact hp

/-- The real L² Cauchy--Schwarz estimate with ordinary square moments. -/
theorem abs_integral_mul_le_sqrt_sq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    |∫ ω, X ω * Y ω ∂P| ≤ Real.sqrt (∫ ω, X ω ^ 2 ∂P) * Real.sqrt (∫ ω, Y ω ^ 2 ∂P) := by
  have hholder := integral_mul_norm_le_Lp_mul_Lq (μ := P) (f := X) (g := Y)
    Real.HolderConjugate.two_two (by simpa only [ENNReal.ofReal_ofNat] using hX)
      (by simpa only [ENNReal.ofReal_ofNat] using hY)
  have hc : (∫ ω, |X ω| * |Y ω| ∂P) ≤
      Real.sqrt (∫ ω, X ω ^ 2 ∂P) * Real.sqrt (∫ ω, Y ω ^ 2 ∂P) := by
    simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] using hholder
  have hn : |∫ ω, X ω * Y ω ∂P| ≤ ∫ ω, |X ω| * |Y ω| ∂P := by
    simpa only [Real.norm_eq_abs, abs_mul] using norm_integral_le_integral_norm (fun ω => X ω * Y ω)
  exact hn.trans hc

/-- Cauchy--Schwarz for covariance, bounded using raw second moments. -/
theorem abs_covariance_le_of_sq_bounds {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hXA : (∫ ω, X ω ^ 2 ∂P) ≤ A ^ 2) (hYB : (∫ ω, Y ω ^ 2 ∂P) ≤ B ^ 2) :
    |covariance X Y P| ≤ A * B := by
  have hc := abs_integral_mul_le_sqrt_sq P
    (hX.sub (memLp_const (∫ ω, X ω ∂P))) (hY.sub (memLp_const (∫ ω, Y ω ∂P)))
  change |∫ ω, (X ω - ∫ z, X z ∂P) * (Y ω - ∫ z, Y z ∂P) ∂P| ≤
    Real.sqrt (∫ ω, (X ω - ∫ z, X z ∂P) ^ 2 ∂P) *
      Real.sqrt (∫ ω, (Y ω - ∫ z, Y z ∂P) ^ 2 ∂P) at hc
  rw [← variance_eq_integral hX.aemeasurable, ← variance_eq_integral hY.aemeasurable] at hc
  have hx := Real.sqrt_le_sqrt ((variance_le_expectation_sq hX.aestronglyMeasurable).trans hXA)
  have hy := Real.sqrt_le_sqrt ((variance_le_expectation_sq hY.aestronglyMeasurable).trans hYB)
  rw [Real.sqrt_sq hA] at hx
  rw [Real.sqrt_sq hB] at hy
  exact hc.trans (mul_le_mul hx hy (Real.sqrt_nonneg _) hA)

/-- Truncating below one preserves L² membership of the logarithm. -/
theorem memLp_truncatedLog {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : AEMeasurable X P) (hpos : ∀ᵐ ω ∂P, 0 < X ω)
    (hL : MemLp (fun ω => Real.log (X ω)) 2 P) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    MemLp (fun ω => truncatedLog β (X ω)) 2 P := by
  apply hL.norm.mono'
    (Real.measurable_log.comp_aemeasurable (hX.max aemeasurable_const)).aestronglyMeasurable
  filter_upwards [hpos] with ω hω
  change |truncatedLog β (X ω)| ≤ |Real.log (X ω)|
  exact (abs_truncatedLog_and_remainder_le hβ hβ1 hω).1

/-- A fourth inverse moment gives the square-moment bound needed for the
remainder in the covariance decomposition. -/
theorem integral_sq_logRemainder_le_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X : Ω → ℝ} (hX : AEMeasurable X P)
    (hpos : ∀ᵐ ω ∂P, 0 < X ω) {V : ℝ} (hV : 0 ≤ V)
    (hInv : Integrable (fun ω => (X ω)⁻¹ ^ 4) P)
    (hInvB : (∫ ω, (X ω)⁻¹ ^ 4 ∂P) ≤ V ^ 10) {β : ℝ} (hβ : 0 < β) :
    (∫ ω, logRemainder β (X ω) ^ 2 ∂P) ≤ (β ^ 2 * V ^ 5) ^ 2 := by
  have hi := (integral_sq_remainder_le P hX hpos hInv hβ).2
  calc
    _ ≤ β ^ 4 * (∫ ω, (X ω)⁻¹ ^ 4 ∂P) / 8 := hi
    _ ≤ β ^ 4 * V ^ 10 / 8 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hInvB (pow_nonneg hβ.le _)) (by norm_num)
    _ ≤ β ^ 4 * V ^ 10 := div_le_self (mul_nonneg (pow_nonneg hβ.le _) (pow_nonneg hV _)) (by norm_num)
    _ = (β ^ 2 * V ^ 5) ^ 2 := by ring

/-- The full logarithmic covariance differs from its lower-truncated version
by at most the source's `C V^5 (1 + log V) β²`, here with the concrete constant four. -/
theorem covariance_log_truncation_error_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hpos : ∀ᵐ ω ∂P, 0 < X ω ∧ 0 < Y ω)
    (hLX2 : MemLp (fun ω => Real.log (X ω)) 2 P)
    (hLY2 : MemLp (fun ω => Real.log (Y ω)) 2 P)
    {V : ℝ} (hV : 1 ≤ V)
    (hIX : Integrable (fun ω => (X ω)⁻¹ ^ 4) P)
    (hIY : Integrable (fun ω => (Y ω)⁻¹ ^ 4) P)
    (hIXB : (∫ ω, (X ω)⁻¹ ^ 4 ∂P) ≤ V ^ 10)
    (hIYB : (∫ ω, (Y ω)⁻¹ ^ 4 ∂P) ≤ V ^ 10)
    (hLXB : (∫ ω, Real.log (X ω) ^ 2 ∂P) ≤ 4 * (1 + Real.log V) ^ 2)
    (hLYB : (∫ ω, Real.log (Y ω) ^ 2 ∂P) ≤ 4 * (1 + Real.log V) ^ 2)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    |covariance (fun ω => Real.log (X ω)) (fun ω => Real.log (Y ω)) P -
      covariance (fun ω => truncatedLog β (X ω)) (fun ω => truncatedLog β (Y ω)) P| ≤
      4 * V ^ 5 * (1 + Real.log V) * β ^ 2 := by
  have hXP := hpos.mono (fun ω hω => hω.1)
  have hYP := hpos.mono (fun ω hω => hω.2)
  have hTX := memLp_truncatedLog hX hXP hLX2 hβ hβ1
  have hTY := memLp_truncatedLog hY hYP hLY2 hβ hβ1
  have hRX : MemLp (fun ω => logRemainder β (X ω)) 2 P := hLX2.sub hTX
  have hRY : MemLp (fun ω => logRemainder β (Y ω)) 2 P := hLY2.sub hTY
  have hV0 : 0 ≤ V := zero_le_one.trans hV
  have hS : 0 ≤ 1 + Real.log V := add_nonneg zero_le_one (Real.log_nonneg hV)
  have hA : 0 ≤ β ^ 2 * V ^ 5 := mul_nonneg (sq_nonneg _) (pow_nonneg hV0 _)
  have hB : 0 ≤ 2 * (1 + Real.log V) := mul_nonneg (by norm_num) hS
  have hRXB := integral_sq_logRemainder_le_moment_bound P hX hXP hV0 hIX hIXB hβ
  have hRYB := integral_sq_logRemainder_le_moment_bound P hY hYP hV0 hIY hIYB hβ
  have hLXBB : (∫ ω, Real.log (X ω) ^ 2 ∂P) ≤ (2 * (1 + Real.log V)) ^ 2 := by
    calc
      _ ≤ 4 * (1 + Real.log V) ^ 2 := hLXB
      _ = _ := by ring
  have hLYBB : (∫ ω, Real.log (Y ω) ^ 2 ∂P) ≤ (2 * (1 + Real.log V)) ^ 2 := by
    calc
      _ ≤ 4 * (1 + Real.log V) ^ 2 := hLYB
      _ = _ := by ring
  have hTXB : (∫ ω, truncatedLog β (X ω) ^ 2 ∂P) ≤ (2 * (1 + Real.log V)) ^ 2 := by
    apply le_trans (integral_mono_ae hTX.integrable_sq hLX2.integrable_sq ?_) hLXBB
    filter_upwards [hXP] with ω hω
    have hs := mul_self_le_mul_self (abs_nonneg (truncatedLog β (X ω)))
      (abs_truncatedLog_and_remainder_le hβ hβ1 hω).1
    simpa only [← pow_two, sq_abs] using hs
  have hc₁ := abs_covariance_le_of_sq_bounds P hRX hLY2 hA hB hRXB hLYBB
  have hc₂ := abs_covariance_le_of_sq_bounds P hTX hRY hB hA hTXB hRYB
  have he₁ := covariance_sub_left hLX2 hTX hLY2
  change covariance (fun ω => logRemainder β (X ω)) (fun ω => Real.log (Y ω)) P =
    covariance (fun ω => Real.log (X ω)) (fun ω => Real.log (Y ω)) P -
      covariance (fun ω => truncatedLog β (X ω)) (fun ω => Real.log (Y ω)) P at he₁
  have he₂ := covariance_sub_right hTX hLY2 hTY
  change covariance (fun ω => truncatedLog β (X ω)) (fun ω => logRemainder β (Y ω)) P =
    covariance (fun ω => truncatedLog β (X ω)) (fun ω => Real.log (Y ω)) P -
      covariance (fun ω => truncatedLog β (X ω)) (fun ω => truncatedLog β (Y ω)) P at he₂
  have heq : covariance (fun ω => Real.log (X ω)) (fun ω => Real.log (Y ω)) P -
      covariance (fun ω => truncatedLog β (X ω)) (fun ω => truncatedLog β (Y ω)) P =
      covariance (fun ω => logRemainder β (X ω)) (fun ω => Real.log (Y ω)) P +
        covariance (fun ω => truncatedLog β (X ω)) (fun ω => logRemainder β (Y ω)) P := by
    linarith only [he₁, he₂]
  rw [heq]
  calc
    _ ≤ |covariance (fun ω => logRemainder β (X ω)) (fun ω => Real.log (Y ω)) P| +
        |covariance (fun ω => truncatedLog β (X ω)) (fun ω => logRemainder β (Y ω)) P| := abs_add_le _ _
    _ ≤ (β ^ 2 * V ^ 5) * (2 * (1 + Real.log V)) +
        (2 * (1 + Real.log V)) * (β ^ 2 * V ^ 5) := add_le_add hc₁ hc₂
    _ = 4 * V ^ 5 * (1 + Real.log V) * β ^ 2 := by ring

/-- A uniform quadratic upper bound at every small positive scale forces a
nonpositive value. The positive-neighborhood filter handles the zero case. -/
theorem le_zero_of_forall_le_mul_sq {f A : ℝ}
    (h : ∀ β : ℝ, 0 < β → β ≤ 1 → f ≤ A * β ^ 2) : f ≤ 0 := by
  have hc : Continuous (fun β : ℝ => A * β ^ 2) := continuous_const.mul (continuous_id.pow 2)
  have hlim : Tendsto (fun β : ℝ => A * β ^ 2) (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    simpa only [zero_pow two_ne_zero, mul_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ β : ℝ in nhdsWithin 0 (Ioi 0), β < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hh : ∀ᶠ β : ℝ in nhdsWithin 0 (Ioi 0), f ≤ A * β ^ 2 := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with β hβ hβ1
    exact h β hβ hβ1.le
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim hh

/-- The analogous lower-bound conclusion used for positivity of log covariance. -/
theorem nonneg_of_forall_neg_mul_sq_le {f A : ℝ}
    (h : ∀ β : ℝ, 0 < β → β ≤ 1 → -A * β ^ 2 ≤ f) : 0 ≤ f := by
  have hn : -f ≤ 0 := le_zero_of_forall_le_mul_sq (A := A) (fun β hβ hβ1 => by
    have hb := h β hβ hβ1
    linarith only [hb])
  exact neg_nonpos.mp hn

/-- Pure algebra at the scale balancing an inverse-square and a square term. -/
theorem balance_inverse_square {s t β : ℝ} (hs : s ≠ 0) (ht : t ≠ 0)
    (hβ : β ^ 2 = t / s) : (β⁻¹) ^ 2 * t ^ 2 + s ^ 2 * β ^ 2 = 2 * s * t := by
  rw [inv_pow, hβ, inv_div]
  field_simp [hs, ht]
  ring

/-- Optimisation of the truncation estimate, including zero covariance. The
condition `c ≤ A` ensures that the chosen truncation scale is at most one. -/
theorem optimise_inverse_square_bound {f c A : ℝ} (hA : 0 < A) (hc : 0 ≤ c) (hcA : c ≤ A)
    (h : ∀ β : ℝ, 0 < β → β ≤ 1 → f ≤ (β⁻¹) ^ 2 * c + A * β ^ 2) :
    f ≤ 2 * Real.sqrt A * Real.sqrt c := by
  by_cases hc0 : c = 0
  · have hf : f ≤ 0 := le_zero_of_forall_le_mul_sq (A := A) (fun β hβ hβ1 => by
      have hb := h β hβ hβ1
      simpa only [hc0, mul_zero, zero_add] using hb)
    rw [hc0, Real.sqrt_zero, mul_zero]
    exact hf
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  let s := Real.sqrt A
  let t := Real.sqrt c
  have hs : 0 < s := Real.sqrt_pos.mpr hA
  have ht : 0 < t := Real.sqrt_pos.mpr hcpos
  have hts : t ≤ s := Real.sqrt_le_sqrt hcA
  let β := Real.sqrt (t / s)
  have hβ : 0 < β := Real.sqrt_pos.mpr (div_pos ht hs)
  have hβ1 : β ≤ 1 := by
    calc
      β = Real.sqrt (t / s) := rfl
      _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt ((div_le_one hs).mpr hts)
      _ = 1 := Real.sqrt_one
  have hβsq : β ^ 2 = t / s := Real.sq_sqrt (div_nonneg ht.le hs.le)
  have hsSq : s ^ 2 = A := Real.sq_sqrt hA.le
  have htSq : t ^ 2 = c := Real.sq_sqrt hc
  have hb := balance_inverse_square hs.ne' ht.ne' hβsq
  rw [hsSq, htSq] at hb
  exact (h β hβ hβ1).trans_eq hb

/-- Real-valued probability inequalities imply positive quadrant dependence. -/
theorem posQuadrantDependent_of_real {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (h : ∀ u v : ℝ, P.real {ω | u < X ω} * P.real {ω | v < Y ω} ≤
      P.real {ω | u < X ω ∧ v < Y ω}) : PosQuadrantDependent P X Y := by
  intro u v
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (measure_ne_top P _) (measure_ne_top P _)) (measure_ne_top P _)).mp
  have hh := h u v
  change (P {ω | u < X ω}).toReal * (P {ω | v < Y ω}).toReal ≤
    (P {ω | u < X ω ∧ v < Y ω}).toReal at hh
  simpa only [ENNReal.toReal_mul] using hh

/-- The scalar associated-log estimate with an explicit universal constant.
The mean-one normalization is not needed once the stated moment bounds hold. -/
theorem covariance_log_le_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hpos : ∀ᵐ ω ∂P, 0 < X ω ∧ 0 < Y ω)
    (hX2 : MemLp X 2 P) (hY2 : MemLp Y 2 P)
    (hLX2 : MemLp (fun ω => Real.log (X ω)) 2 P)
    (hLY2 : MemLp (fun ω => Real.log (Y ω)) 2 P)
    {V : ℝ} (hV : 1 ≤ V)
    (hXB : (∫ ω, X ω ^ 2 ∂P) ≤ V) (hYB : (∫ ω, Y ω ^ 2 ∂P) ≤ V)
    (hIX : Integrable (fun ω => (X ω)⁻¹ ^ 4) P)
    (hIY : Integrable (fun ω => (Y ω)⁻¹ ^ 4) P)
    (hIXB : (∫ ω, (X ω)⁻¹ ^ 4 ∂P) ≤ V ^ 10)
    (hIYB : (∫ ω, (Y ω)⁻¹ ^ 4 ∂P) ≤ V ^ 10)
    (hLXB : (∫ ω, Real.log (X ω) ^ 2 ∂P) ≤ 4 * (1 + Real.log V) ^ 2)
    (hLYB : (∫ ω, Real.log (Y ω) ^ 2 ∂P) ≤ 4 * (1 + Real.log V) ^ 2)
    (hQ : PosQuadrantDependent P X Y) :
    0 ≤ covariance (fun ω => Real.log (X ω)) (fun ω => Real.log (Y ω)) P ∧
      covariance (fun ω => Real.log (X ω)) (fun ω => Real.log (Y ω)) P ≤
        4 * V ^ (5 / 2 : ℝ) * Real.sqrt (1 + Real.log V) * Real.sqrt (covariance X Y P) := by
  let f := covariance (fun ω => Real.log (X ω)) (fun ω => Real.log (Y ω)) P
  let c := covariance X Y P
  let S := 1 + Real.log V
  let A := 4 * V ^ 5 * S
  have hV0 : 0 ≤ V := zero_le_one.trans hV
  have hS1 : 1 ≤ S := le_add_of_nonneg_right (Real.log_nonneg hV)
  have hA : 0 < A := mul_pos
    (mul_pos (by norm_num) (pow_pos (zero_lt_one.trans_le hV) _)) (zero_lt_one.trans_le hS1)
  have hc : 0 ≤ c := by
    have ht := covariance_le_truncation P hpos hX2 hY2 hLX2 hLY2 hQ
      (β := 1) (by norm_num) le_rfl
    simpa only [inv_one, one_pow, one_mul] using ht.1.trans ht.2
  have hcV : c ≤ V := by
    have hcs := abs_covariance_le_of_sq_bounds P hX2 hY2 (Real.sqrt_nonneg V) (Real.sqrt_nonneg V)
      (by rw [Real.sq_sqrt hV0]; exact hXB) (by rw [Real.sq_sqrt hV0]; exact hYB)
    calc
      c ≤ |c| := le_abs_self _
      _ ≤ Real.sqrt V * Real.sqrt V := hcs
      _ = V := by rw [← pow_two, Real.sq_sqrt hV0]
  have hV5 : V ≤ V ^ 5 := by
    simpa only [pow_one] using pow_le_pow_right₀ hV (by decide : 1 ≤ 5)
  have hVA : V ≤ A := by
    calc
      V ≤ V ^ 5 := hV5
      _ ≤ V ^ 5 * S := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hS1 (pow_nonneg hV0 5)
      _ ≤ 4 * (V ^ 5 * S) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 4)
          (mul_nonneg (pow_nonneg hV0 5) (zero_le_one.trans hS1))
      _ = A := by dsimp only [A]; ring
  have herror (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) :
      |f - covariance (fun ω => truncatedLog β (X ω)) (fun ω => truncatedLog β (Y ω)) P| ≤
        A * β ^ 2 :=
    covariance_log_truncation_error_le P hX2.aemeasurable hY2.aemeasurable hpos hLX2 hLY2 hV
      hIX hIY hIXB hIYB hLXB hLYB hβ hβ1
  have hf : 0 ≤ f := by
    apply nonneg_of_forall_neg_mul_sq_le (A := A)
    intro β hβ hβ1
    have ht := (covariance_le_truncation P hpos hX2 hY2 hLX2 hLY2 hQ hβ hβ1).1
    have he := (abs_le.mp (herror β hβ hβ1)).1
    linarith only [ht, he]
  have hub : f ≤ 2 * Real.sqrt A * Real.sqrt c := by
    apply optimise_inverse_square_bound hA hc (hcV.trans hVA)
    intro β hβ hβ1
    have ht := (covariance_le_truncation P hpos hX2 hY2 hLX2 hLY2 hQ hβ hβ1).2
    have he := (abs_le.mp (herror β hβ hβ1)).2
    linarith only [ht, he]
  have hrootV : Real.sqrt (V ^ 5) = V ^ (5 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hV0]
    congr 1
    norm_num
  have hroot : Real.sqrt A = 2 * V ^ (5 / 2 : ℝ) * Real.sqrt S := by
    change Real.sqrt (4 * V ^ 5 * S) = _
    rw [Real.sqrt_mul (mul_nonneg (by norm_num : 0 ≤ (4 : ℝ)) (pow_nonneg hV0 5)),
      Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ)), hrootV]
    rw [show Real.sqrt (4 : ℝ) = 2 by
      simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  refine ⟨hf, ?_⟩
  calc
    f ≤ 2 * Real.sqrt A * Real.sqrt c := hub
    _ = 4 * V ^ (5 / 2 : ℝ) * Real.sqrt (1 + Real.log V) * Real.sqrt (covariance X Y P) := by
      rw [hroot]
      ring

universe u

/-- Lemma 6.5 of the note: an absolute constant controls the logarithmic
covariance by the square root of the mass covariance, uniformly over all
probability spaces. -/
theorem covariance_log_le_of_posQuadrant :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X Y : Ω → ℝ) (V : ℝ), 1 ≤ V → (∀ᵐ ω ∂P, 0 < X ω ∧ 0 < Y ω) →
      MemLp X 2 P → MemLp Y 2 P → MemLp (fun ω => Real.log (X ω)) 2 P →
      MemLp (fun ω => Real.log (Y ω)) 2 P → (∫ ω, X ω ∂P) = 1 → (∫ ω, Y ω ∂P) = 1 →
      (∫ ω, X ω ^ 2 ∂P) ≤ V → (∫ ω, Y ω ^ 2 ∂P) ≤ V →
      Integrable (fun ω => (X ω)⁻¹ ^ 4) P → Integrable (fun ω => (Y ω)⁻¹ ^ 4) P →
      (∫ ω, (X ω)⁻¹ ^ 4 ∂P) ≤ V ^ 10 → (∫ ω, (Y ω)⁻¹ ^ 4 ∂P) ≤ V ^ 10 →
      (∫ ω, Real.log (X ω) ^ 2 ∂P) ≤ 4 * (1 + Real.log V) ^ 2 →
      (∫ ω, Real.log (Y ω) ^ 2 ∂P) ≤ 4 * (1 + Real.log V) ^ 2 →
      (∀ a b : ℝ, P.real {ω | a < X ω} * P.real {ω | b < Y ω} ≤
        P.real {ω | a < X ω ∧ b < Y ω}) →
      0 ≤ covariance (fun ω => Real.log (X ω)) (fun ω => Real.log (Y ω)) P ∧
        covariance (fun ω => Real.log (X ω)) (fun ω => Real.log (Y ω)) P ≤
          C * V ^ (5 / 2 : ℝ) * Real.sqrt (1 + Real.log V) * Real.sqrt (covariance X Y P) := by
  refine ⟨4, by norm_num, ?_⟩
  intro Ω _ P _ X Y V hV hpos hX2 hY2 hLX2 hLY2 _ _ hXB hYB hIX hIY hIXB hIYB hLXB hLYB hQ
  exact covariance_log_le_moment_bound P hpos hX2 hY2 hLX2 hLY2 hV hXB hYB hIX hIY
    hIXB hIYB hLXB hLYB (posQuadrantDependent_of_real P hQ)

end Critical2DKPZ.Extensions.GffTangent
