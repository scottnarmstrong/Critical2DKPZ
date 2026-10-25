/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SubseqDenseInputs
public import Critical2DKPZ.SHF.Flow.SlabSmoothedBridgeIdentity
public import Critical2DKPZ.SHF.Flow.SlabMeanKernelLimit
public import Critical2DKPZ.SHF.Flow.SlabMeanKernelGaussianBound
public import Critical2DKPZ.SHF.Moments.TimeRounding
public import Critical2DKPZ.SHF.Moments.WalkScaling
public import Critical2DKPZ.SHF.Flow.KernelProductCutoffTail
public import Critical2DKPZ.SHF.Flow.KernelProductCutoffUniform
public import Critical2DKPZ.Analysis.Heat.Semigroup
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Bounded

/-! Auxiliary estimates control the mollified heat connector across a fixed slab. -/

@[expose] public noncomputable section

open MeasureTheory
open Filter
open ProbabilityTheory
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.SHF.Moments
open Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported Convolution

namespace Critical2DKPZ.SHF.Flow

/-- A positive-time planar heat kernel is uniformly continuous on the whole plane. -/
theorem uniformContinuous_heatKernel {v : ℝ} (hv : 0 < v) :
    UniformContinuous (heatKernel v) := by
  have hnorm : Tendsto (fun x : Plane => ‖x‖) (cocompact Plane) atTop :=
    tendsto_norm_cocompact_atTop
  have hsq : Tendsto (fun x : Plane => ‖x‖ ^ 2) (cocompact Plane) atTop := by
    have h := hnorm.atTop_mul_atTop₀ hnorm
    simpa only [pow_two] using h
  have harg : Tendsto (fun x : Plane => -((2 * v)⁻¹) * ‖x‖ ^ 2)
      (cocompact Plane) atBot := by
    have hc : -((2 * v)⁻¹) < 0 := neg_lt_zero.mpr (inv_pos.mpr (by positivity))
    exact hsq.const_mul_atTop_of_neg hc
  have hexp : Tendsto (fun x : Plane => Real.exp (-((2 * v)⁻¹) * ‖x‖ ^ 2))
      (cocompact Plane) (nhds 0) := Real.tendsto_exp_atBot.comp harg
  have hzero : Tendsto (heatKernel v) (cocompact Plane) (nhds 0) := by
    have hconst : Tendsto (fun _ : Plane => (2 * Real.pi * v)⁻¹)
        (cocompact Plane) (nhds ((2 * Real.pi * v)⁻¹)) := tendsto_const_nhds
    have h := hconst.mul hexp
    convert h using 1
    · funext x
      rw [heatKernel_eq_exp]
    · simp
  have hzero' : Tendsto (heatKernel v) (cocompact Plane) (nhds 0) := hzero
  exact (Critical2DKPZ.continuous_heatKernel v).uniformContinuous_of_tendsto_cocompact hzero'

/-- The scaled profile is a uniform approximate identity for the heat kernel on all endpoint
pairs. The bound is independent of the location of the endpoints. -/
theorem mollifiedHeatKernel_tendsto_uniform
    {v : ℝ} (hv : 0 < v) (w : Plane → ℝ) (hw : Continuous w)
    (hwc : HasCompactSupport w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∫ x, w x = 1) :
    ∀ ε > 0, ∃ η > 0, ∀ e : ℝ, 0 < e → e < η → ∀ a b,
      |(∫ y, e⁻¹ ^ 2 * w (e⁻¹ • (a - y)) * heatKernel v (b - y)) -
        heatKernel v (b - a)| < ε := by
  intro ε hε
  obtain ⟨Rw₀, hRw₀⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp hwc.isBounded
  let Rw := max Rw₀ 0
  have hRw : 0 ≤ Rw := le_max_right _ _
  have hwBound {x : Plane} (hx : x ∈ tsupport w) : ‖x‖ ≤ Rw := by
    have hball := hRw₀ hx
    have hn : ‖x‖ ≤ Rw₀ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hball
    exact hn.trans (le_max_left _ _)
  obtain ⟨δ, hδ, hmod⟩ :=
    Metric.uniformContinuous_iff.mp (uniformContinuous_heatKernel hv)
      (ε / 2) (half_pos hε)
  let η := min 1 (δ / (Rw + 1))
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min one_pos (div_pos hδ (by positivity))
  refine ⟨η, hη, ?_⟩
  intro e he heη a b
  have heone : e < 1 := lt_of_lt_of_le heη (min_le_left _ _)
  have heRw : e * Rw < δ := by
    have hsmall := lt_of_lt_of_le heη (min_le_right _ _)
    have hmul : e * (Rw + 1) < δ := (lt_div_iff₀ (by positivity)).mp hsmall
    nlinarith [hRw]
  let we : Plane → ℝ := fun x => e⁻¹ ^ 2 * w (e⁻¹ • x)
  have hwe : Continuous we := by
    dsimp [we]
    exact continuous_const.mul (hw.comp
      ((continuous_const : Continuous fun _ : Plane => e⁻¹).smul continuous_id))
  have hwec : HasCompactSupport we := by
    have hcomp : HasCompactSupport (fun x : Plane => w (e⁻¹ • x)) :=
      hwc.comp_smul (inv_ne_zero he.ne')
    change HasCompactSupport (fun x : Plane => (e⁻¹ ^ 2 : ℝ) • w (e⁻¹ • x))
    exact HasCompactSupport.smul_left
      (f := fun _ : Plane => (e⁻¹ ^ 2 : ℝ)) hcomp
  have hmass : ∫ x, we x = 1 := by
    have hdim : Module.finrank ℝ Plane = 2 := by
      simp only [Plane, finrank_euclideanSpace, Fintype.card_fin]
    have hscale := Measure.integral_comp_smul volume w e⁻¹
    rw [hdim] at hscale
    have habs : |((e⁻¹) ^ 2)⁻¹| = e ^ 2 := by
      rw [abs_of_pos (inv_pos.mpr (pow_pos (inv_pos.mpr he) 2))]
      field_simp
    rw [habs, smul_eq_mul] at hscale
    have hscale' : (∫ x, w (e⁻¹ • x)) = e ^ 2 * ∫ x, w x := hscale
    rw [show we = fun x => (e⁻¹ ^ 2) * w (e⁻¹ • x) by rfl,
      integral_const_mul, hscale', hw1]
    have hcancel : e⁻¹ ^ 2 * e ^ 2 = 1 := by field_simp
    calc
      e⁻¹ ^ 2 * (e ^ 2 * 1) = (e⁻¹ ^ 2 * e ^ 2) * 1 := by ring
      _ = 1 := by rw [hcancel]; norm_num
  have hweNonneg (x : Plane) : 0 ≤ we x := by
    dsimp [we]
    exact mul_nonneg (sq_nonneg _) (hw0 _)
  have hmassTranslate (a : Plane) : ∫ y, we (a - y) = 1 := by
    rw [integral_sub_left_eq_self we volume a, hmass]
  have hsupportBound {a y : Plane} (hwy : we (a - y) ≠ 0) :
      ‖a - y‖ ≤ e * Rw := by
    have hmem : e⁻¹ • (a - y) ∈ tsupport w := by
      by_contra hnot
      have hz : w (e⁻¹ • (a - y)) = 0 := image_eq_zero_of_notMem_tsupport hnot
      apply hwy
      simp [we, hz]
    have hn := hwBound hmem
    have hnorm : ‖e⁻¹ • (a - y)‖ = e⁻¹ * ‖a - y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr he)]
    rw [hnorm] at hn
    have hmul := mul_le_mul_of_nonneg_left hn (le_of_lt he)
    have hcancel : e * e⁻¹ = 1 := by field_simp
    have hleft : e * (e⁻¹ * ‖a - y‖) = ‖a - y‖ := by
      rw [← mul_assoc, hcancel, one_mul]
    rw [hleft] at hmul
    exact hmul
  have hkernelDiff (y : Plane) (hwy : we (a - y) ≠ 0) :
      |heatKernel v (b - y) - heatKernel v (b - a)| < ε / 2 := by
    have hdist : dist (b - y) (b - a) < δ := by
      rw [dist_eq_norm, show (b - y) - (b - a) = a - y by abel]
      exact lt_of_le_of_lt (hsupportBound hwy) heRw
    have h := hmod hdist
    simpa only [Real.dist_eq] using h
  have hweight : Integrable (fun y : Plane => we (a - y)) := by
    have hsupp : HasCompactSupport (fun y : Plane => we (a - y)) :=
      hwec.comp_homeomorph (Homeomorph.subLeft a)
    exact (hwe.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport hsupp
  have hweightedKernel : Integrable (fun y : Plane => we (a - y) * heatKernel v (b - y)) := by
    have hc : Continuous (fun y : Plane => we (a - y) * heatKernel v (b - y)) := by
      exact (hwe.comp (continuous_const.sub continuous_id)).mul
        ((Critical2DKPZ.continuous_heatKernel v).comp (continuous_const.sub continuous_id))
    have hsupp : HasCompactSupport
        (fun y : Plane => we (a - y) * heatKernel v (b - y)) := by
      exact (hwec.comp_homeomorph (Homeomorph.subLeft a)).mul_right
    exact hc.integrable_of_hasCompactSupport hsupp
  have hweightedConst : Integrable (fun y : Plane => we (a - y) * heatKernel v (b - a)) :=
    hweight.mul_const _
  have hdiffIntegral :
      (∫ y, we (a - y) * heatKernel v (b - y)) - heatKernel v (b - a) =
        ∫ y, we (a - y) * (heatKernel v (b - y) - heatKernel v (b - a)) := by
    calc
      _ = (∫ y, we (a - y) * heatKernel v (b - y)) -
          (∫ y, we (a - y) * heatKernel v (b - a)) := by
        rw [integral_mul_const, hmassTranslate]
        ring
      _ = ∫ y, (we (a - y) * heatKernel v (b - y) -
          we (a - y) * heatKernel v (b - a)) :=
        (integral_sub hweightedKernel hweightedConst).symm
      _ = ∫ y, we (a - y) * (heatKernel v (b - y) - heatKernel v (b - a)) := by
        apply integral_congr_ae
        filter_upwards [] with y
        ring
  have hweightedDiff : Integrable
      (fun y : Plane => we (a - y) * (heatKernel v (b - y) - heatKernel v (b - a))) := by
    exact (hweightedKernel.sub hweightedConst).congr
      (Filter.Eventually.of_forall fun y => by
        change we (a - y) * heatKernel v (b - y) -
          we (a - y) * heatKernel v (b - a) = _
        ring)
  have herror :
      |∫ y, we (a - y) * (heatKernel v (b - y) - heatKernel v (b - a))| ≤ ε / 2 := by
    calc
      _ = ‖∫ y, we (a - y) * (heatKernel v (b - y) - heatKernel v (b - a))‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ ∫ y, ‖we (a - y) * (heatKernel v (b - y) - heatKernel v (b - a))‖ :=
        norm_integral_le_integral_norm _
      _ = ∫ y, |we (a - y) * (heatKernel v (b - y) - heatKernel v (b - a))| := by
        apply integral_congr_ae
        filter_upwards [] with y
        exact Real.norm_eq_abs _
      _ ≤ ∫ y, we (a - y) * (ε / 2) := by
        apply integral_mono hweightedDiff.abs (hweight.mul_const (ε / 2))
        intro y
        change |we (a - y) * (heatKernel v (b - y) - heatKernel v (b - a))| ≤
          we (a - y) * (ε / 2)
        by_cases hzero : we (a - y) = 0
        · simp [hzero]
        · rw [abs_mul, abs_of_nonneg (hweNonneg _)]
          exact mul_le_mul_of_nonneg_left (le_of_lt (hkernelDiff y hzero)) (hweNonneg _)
      _ = ε / 2 := by rw [integral_mul_const, hmassTranslate, one_mul]
  change |(∫ y, we (a - y) * heatKernel v (b - y)) - heatKernel v (b - a)| < ε
  rw [hdiffIntegral]
  exact lt_of_le_of_lt herror (by linarith)

/-- Scaling a unit-mass profile in the plane preserves its mass. -/
theorem integral_slabScaledProfile_eq_one {e : ℝ} (he : 0 < e)
    (w : Plane → ℝ) (hw1 : ∫ x, w x = 1) :
    ∫ x, e⁻¹ ^ 2 * w (e⁻¹ • x) = 1 := by
  have hdim : Module.finrank ℝ Plane = 2 := by
    simp only [Plane, finrank_euclideanSpace, Fintype.card_fin]
  have hscale := Measure.integral_comp_smul volume w e⁻¹
  rw [hdim] at hscale
  have habs : |((e⁻¹) ^ 2)⁻¹| = e ^ 2 := by
    rw [abs_of_pos (inv_pos.mpr (pow_pos (inv_pos.mpr he) 2))]
    field_simp
  rw [habs, smul_eq_mul] at hscale
  have hscale' : (∫ x, w (e⁻¹ • x)) = e ^ 2 * ∫ x, w x := hscale
  rw [integral_const_mul, hscale', hw1]
  have hcancel : e⁻¹ ^ 2 * e ^ 2 = 1 := by field_simp
  calc
    e⁻¹ ^ 2 * (e ^ 2 * 1) = (e⁻¹ ^ 2 * e ^ 2) * 1 := by ring
    _ = 1 := by rw [hcancel]; norm_num

/-- The mean slab kernel converges uniformly when only the endpoint displacement is bounded.
The local CLT and lattice mesh errors are uniform over all sites, so no compactness of the
absolute endpoint locations is needed. -/
theorem tendsto_slabMeanKernel_uniformOn_differenceBall (ϑ : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {v : ℝ} (hv : 0 < v) (R : ℝ) (hR : 0 ≤ R) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      ∀ x y, ‖y - x‖ ≤ R →
        |slabMeanKernel ϑ N t (t + v) x y - heatKernel v (y - x)| < ε := by
  intro ε hε
  let Rheat := R + 4
  have hRheat : 0 ≤ Rheat := by dsimp [Rheat]; positivity
  let Kheat : Set (ℝ × Plane) := Set.Icc (v / 2) (2 * v) ×ˢ
    Metric.closedBall 0 Rheat
  have hKheat : IsCompact Kheat := isCompact_Icc.prod (isCompact_closedBall 0 Rheat)
  have hheatContinuous : ContinuousOn
      (fun p : ℝ × Plane => heatKernel p.1 p.2) Kheat := by
    exact Critical2DKPZ.DeltaBose.continuousOn_heatKernel.mono (by
      intro p hp
      exact lt_of_lt_of_le (by positivity) hp.1.1)
  have hheatUniform : UniformContinuousOn
      (fun p : ℝ × Plane => heatKernel p.1 p.2) Kheat :=
    hKheat.uniformContinuousOn_of_continuous hheatContinuous
  obtain ⟨δ, hδ, hmod⟩ :=
    Metric.uniformContinuousOn_iff.mp hheatUniform (ε / 2) (half_pos hε)
  let n : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * (t + v)) - evenCeil ((N : ℝ) * t)
  have htime : Tendsto (fun N : ℕ => (n N : ℝ) / N) atTop (nhds v) := by
    simpa only [n, add_sub_cancel_left] using
      tendsto_evenCeil_gap_div (s := t) (t := t + v) ht (by linarith)
  obtain ⟨C, hC, hclt⟩ := srwKernel_scaled_localCLT
  have herror : ∀ᶠ N : ℕ in atTop, 4 * C / (v ^ 2 * (N : ℝ)) < ε / 2 := by
    have hlim := tendsto_const_div_nat (4 * C / v ^ 2)
    filter_upwards [hlim.eventually (Iio_mem_nhds (half_pos hε))] with N hN
    have hEq : (4 * C / v ^ 2) / (N : ℝ) = 4 * C / (v ^ 2 * (N : ℝ)) := by ring
    rw [hEq] at hN
    exact hN
  have htimeWindow : ∀ᶠ N : ℕ in atTop,
      (n N : ℝ) / N ∈ Set.Ioo (v / 2) (2 * v) := by
    filter_upwards [htime.eventually (Ioo_mem_nhds
      (by linarith : v / 2 < v) (by linarith : v < 2 * v))] with N hN
    exact hN
  have htimeClose : ∀ᶠ N : ℕ in atTop,
      dist ((n N : ℝ) / N) v < δ / 2 := by
    filter_upwards [htime.eventually (Metric.ball_mem_nhds v (half_pos hδ))] with N hN
    simpa only [Metric.mem_ball] using hN
  have hmesh : ∀ᶠ N : ℕ in atTop,
      (Real.sqrt ((N : ℝ) / 2))⁻¹ < min (δ / 4) 1 := by
    filter_upwards [tendsto_lattice_mesh.eventually
      (Iio_mem_nhds (by positivity : 0 < min (δ / 4) 1))] with N hN
    exact hN
  have hNlarge : ∀ᶠ N : ℕ in atTop, (2 / v : ℝ) < N :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
      (eventually_gt_atTop (2 / v))
  filter_upwards [eventually_gt_atTop 0, herror, htimeWindow, htimeClose, hmesh, hNlarge]
      with N hN hNerr hNtime hNclose hNmesh hNlarge
  have hNmeshδ : (Real.sqrt ((N : ℝ) / 2))⁻¹ < δ / 4 :=
    lt_of_lt_of_le hNmesh (min_le_left _ _)
  have hNmeshOne : (Real.sqrt ((N : ℝ) / 2))⁻¹ < 1 :=
    lt_of_lt_of_le hNmesh (min_le_right _ _)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hlargeProduct : 1 < (v / 2) * (N : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hNlarge (by positivity : 0 < v / 2)
    have hcancel : (2 / v) * (v / 2) = 1 := by field_simp [hv.ne']
    rw [hcancel] at hmul
    nlinarith
  have hnreal : (v / 2) * (N : ℝ) < (n N : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hNtime.1 hNpos
    simpa only [div_mul_cancel₀ _ hNpos.ne'] using hmul
  have hnpos : 1 ≤ n N := by
    exact_mod_cast (show (1 : ℝ) ≤ (n N : ℝ) by linarith)
  have hnlower : (v / 2) * (N : ℝ) ≤ (n N : ℝ) := hnreal.le
  have hcltError (x y : Plane) :
      |((N : ℝ) / 4) * srwKernel (n N) (latticePoint N y - latticePoint N x) -
          heatKernel ((n N : ℝ) / N)
            (latticeRepresentative N (latticePoint N y - latticePoint N x))| < ε / 2 := by
    have hzEven : Even ((latticePoint N y - latticePoint N x) 0 +
        (latticePoint N y - latticePoint N x) 1 + (n N : ℤ)) := by
      exact latticePoint_gap_phase N (n N) (even_evenCeil_sub ((N : ℝ) * t)
        ((N : ℝ) * (t + v))) x y
    have hraw := hclt N (n N) hN hnpos (latticePoint N y - latticePoint N x) hzEven
    have hden : ((v / 2) * (N : ℝ)) ^ 2 ≤ (n N : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hnlower 2
    have hcmp : C * (N : ℝ) / (n N : ℝ) ^ 2 ≤
        4 * C / (v ^ 2 * (N : ℝ)) := by
      have hdiv := div_le_div_of_nonneg_left (by positivity : 0 ≤ C * (N : ℝ))
        (by positivity : 0 < ((v / 2) * (N : ℝ)) ^ 2) hden
      calc
        C * (N : ℝ) / (n N : ℝ) ^ 2 ≤
            C * (N : ℝ) / ((v / 2) * (N : ℝ)) ^ 2 := hdiv
        _ = 4 * C / (v ^ 2 * (N : ℝ)) := by field_simp [hNpos.ne']; ring
    calc
      |((N : ℝ) / 4) * srwKernel (n N) (latticePoint N y - latticePoint N x) -
          heatKernel ((n N : ℝ) / N)
            (latticeRepresentative N (latticePoint N y - latticePoint N x))|
        ≤ C * (N : ℝ) / (n N : ℝ) ^ 2 := hraw
      _ ≤ 4 * C / (v ^ 2 * (N : ℝ)) := hcmp
      _ < ε / 2 := hNerr
  have hspatial (x y : Plane) :
      dist (cellSample N y - cellSample N x) (y - x) < δ := by
    have hxsample := Critical2DKPZ.dist_cellSample_le hN x
    have hysample := Critical2DKPZ.dist_cellSample_le hN y
    have hdecomp : cellSample N y - cellSample N x - (y - x) =
        (cellSample N y - y) - (cellSample N x - x) := by abel
    rw [dist_eq_norm, hdecomp]
    calc
      ‖(cellSample N y - y) - (cellSample N x - x)‖ ≤
          ‖cellSample N y - y‖ + ‖cellSample N x - x‖ := norm_sub_le _ _
      _ = dist (cellSample N y) y + dist (cellSample N x) x := by
        rw [dist_eq_norm, dist_eq_norm]
      _ ≤ 2 * (Real.sqrt ((N : ℝ) / 2))⁻¹ := by linarith [hysample, hxsample]
      _ < δ := by nlinarith [hNmeshδ]
  intro x y hxy
  have hxsample := Critical2DKPZ.dist_cellSample_le hN x
  have hysample := Critical2DKPZ.dist_cellSample_le hN y
  have hsampleX : ‖cellSample N x - x‖ ≤ (Real.sqrt ((N : ℝ) / 2))⁻¹ := by
    simpa only [dist_eq_norm] using hxsample
  have hsampleY : ‖cellSample N y - y‖ ≤ (Real.sqrt ((N : ℝ) / 2))⁻¹ := by
    simpa only [dist_eq_norm] using hysample
  have hdispSample : ‖cellSample N y - cellSample N x‖ ≤ R + 2 := by
    have hdecomp : cellSample N y - cellSample N x =
        (y - x) + ((cellSample N y - y) - (cellSample N x - x)) := by abel
    rw [hdecomp]
    calc
      _ ≤ ‖y - x‖ + ‖(cellSample N y - y) - (cellSample N x - x)‖ := norm_add_le _ _
      _ ≤ R + (‖cellSample N y - y‖ + ‖cellSample N x - x‖) := by
        exact add_le_add hxy (norm_sub_le _ _)
      _ ≤ R + 2 := by nlinarith [hsampleX, hsampleY, hNmeshOne]
  have hp : ((n N : ℝ) / N, cellSample N y - cellSample N x) ∈ Kheat := by
    change ((n N : ℝ) / N ∈ Set.Icc (v / 2) (2 * v)) ∧
      (cellSample N y - cellSample N x ∈ Metric.closedBall 0 Rheat)
    constructor
    · exact ⟨hNtime.1.le, hNtime.2.le⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right, Rheat] using
        hdispSample.trans (by linarith)
  have hq : (v, y - x) ∈ Kheat := by
    change (v ∈ Set.Icc (v / 2) (2 * v)) ∧ (y - x ∈ Metric.closedBall 0 Rheat)
    constructor
    · exact ⟨by linarith, by linarith⟩
    · apply Metric.mem_closedBall.mpr
      rw [dist_zero_right]
      dsimp [Rheat]
      linarith
  have hpairclose : dist ((n N : ℝ) / N, cellSample N y - cellSample N x)
      (v, y - x) < δ := by
    rw [Prod.dist_eq]
    exact max_lt_iff.mpr ⟨hNclose.trans (by linarith), hspatial x y⟩
  have hheat := hmod _ hp _ hq hpairclose
  have hrep : latticeRepresentative N (latticePoint N y - latticePoint N x) =
      cellSample N y - cellSample N x := by
    simp only [latticeRepresentative, cellSample]
    rw [← smul_sub]
    congr 1
    ext i
    simp [siteToPlane]
  have hcltError' := hcltError x y
  rw [hrep] at hcltError'
  have hslab : slabMeanKernel ϑ N t (t + v) x y =
      ((N : ℝ) / 4) * srwKernel (n N) (latticePoint N y - latticePoint N x) := by
    rw [slabMeanKernel_eq_srwKernel]
  rw [hslab]
  calc
    |((N : ℝ) / 4) * srwKernel (n N) (latticePoint N y - latticePoint N x) -
        heatKernel v (y - x)| =
      |(((N : ℝ) / 4) * srwKernel (n N) (latticePoint N y - latticePoint N x) -
        heatKernel ((n N : ℝ) / N) (cellSample N y - cellSample N x)) +
        (heatKernel ((n N : ℝ) / N) (cellSample N y - cellSample N x) - heatKernel v (y - x))| := by
          congr 1
          ring
    _ ≤ |((N : ℝ) / 4) * srwKernel (n N) (latticePoint N y - latticePoint N x) -
        heatKernel ((n N : ℝ) / N) (cellSample N y - cellSample N x)| +
        |heatKernel ((n N : ℝ) / N) (cellSample N y - cellSample N x) - heatKernel v (y - x)| :=
          abs_add_le _ _
    _ < ε := by
      have hheat' : |heatKernel ((n N : ℝ) / N) (cellSample N y - cellSample N x) -
          heatKernel v (y - x)| < ε / 2 := by
        simpa only [Real.dist_eq, Prod.fst, Prod.snd] using hheat
      have hhalves : ε / 2 + ε / 2 = ε := by ring
      rw [← hhalves]
      exact add_lt_add hcltError' hheat'


/-- On a bounded displacement window, the mollified and unsmoothed slab connectors become
uniformly close as the profile scale shrinks and the lattice scale grows. -/
theorem tendsto_slabSmoothedConnector_sub_slabMeanKernel_uniformOn_differenceBall
    (ϑ : ℝ) {t : ℝ} (ht : 0 ≤ t) {v : ℝ} (hv : 0 < v)
    (w : Plane → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∫ x, w x = 1) (R : ℝ) (hR : 0 ≤ R) :
    ∀ ε > 0, ∃ η > 0, ∀ e : ℝ, 0 < e → e < η →
      ∀ᶠ N : ℕ in atTop, ∀ a b, ‖b - a‖ ≤ R →
        |slabSmoothedConnector ϑ N t (t + v)
            (fun x => e⁻¹ ^ 2 * w (e⁻¹ • x)) a b -
          slabMeanKernel ϑ N t (t + v) a b| < ε := by
  intro ε hε
  let δ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Rw₀, hRw₀⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp hwc.isBounded
  let Rw := max Rw₀ 0
  have hRw : 0 ≤ Rw := le_max_right _ _
  have hwBound {x : Plane} (hx : x ∈ tsupport w) : ‖x‖ ≤ Rw := by
    have hball := hRw₀ hx
    have hn : ‖x‖ ≤ Rw₀ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hball
    exact hn.trans (le_max_left _ _)
  obtain ⟨η₀, hη₀, hprofile⟩ :=
    mollifiedHeatKernel_tendsto_uniform hv w hw hwc hw0 hw1 δ hδ
  let η := min 1 η₀
  have hη : 0 < η := lt_min one_pos hη₀
  let Rmid := R + Rw
  have hRmid : 0 ≤ Rmid := by dsimp [Rmid]; positivity
  have hslab := tendsto_slabMeanKernel_uniformOn_differenceBall
    ϑ ht hv Rmid hRmid δ hδ
  refine ⟨η, hη, ?_⟩
  intro e he heη
  have heone : e < 1 := lt_of_lt_of_le heη (min_le_left _ _)
  have heeta : e < η₀ := lt_of_lt_of_le heη (min_le_right _ _)
  filter_upwards [hslab] with N hN
  intro a b hab
  let we : Plane → ℝ := fun x => e⁻¹ ^ 2 * w (e⁻¹ • x)
  have hwe : Continuous we := by
    exact continuous_const.mul (hw.comp
      ((continuous_const : Continuous fun _ : Plane => e⁻¹).smul continuous_id))
  have hwec : HasCompactSupport we := by
    have hcomp : HasCompactSupport (fun x : Plane => w (e⁻¹ • x)) :=
      hwc.comp_smul (inv_ne_zero he.ne')
    change HasCompactSupport (fun x : Plane => (e⁻¹ ^ 2 : ℝ) • w (e⁻¹ • x))
    exact HasCompactSupport.smul_left
      (f := fun _ : Plane => (e⁻¹ ^ 2 : ℝ)) hcomp
  have hmass : ∫ x, we x = 1 := integral_slabScaledProfile_eq_one he w hw1
  have hweNonneg (x : Plane) : 0 ≤ we x := by
    dsimp [we]
    exact mul_nonneg (sq_nonneg _) (hw0 _)
  have hmassTranslate (a : Plane) : ∫ z, we (a - z) = 1 := by
    rw [integral_sub_left_eq_self we volume a, hmass]
  have hsupportBound {z : Plane} (hzero : we (a - z) ≠ 0) :
      ‖a - z‖ ≤ e * Rw := by
    have hmem : e⁻¹ • (a - z) ∈ tsupport w := by
      by_contra hnot
      have hz : w (e⁻¹ • (a - z)) = 0 := image_eq_zero_of_notMem_tsupport hnot
      apply hzero
      simp [we, hz]
    have hn := hwBound hmem
    have hnorm : ‖e⁻¹ • (a - z)‖ = e⁻¹ * ‖a - z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr he)]
    rw [hnorm] at hn
    have hmul := mul_le_mul_of_nonneg_left hn (le_of_lt he)
    have hcancel : e * e⁻¹ = 1 := by field_simp
    have hleft : e * (e⁻¹ * ‖a - z‖) = ‖a - z‖ := by
      rw [← mul_assoc, hcancel, one_mul]
    rw [hleft] at hmul
    exact hmul
  have hNkernel {z : Plane} (hz : we (a - z) ≠ 0) :
      |slabMeanKernel ϑ N t (t + v) z b - heatKernel v (b - z)| < δ := by
    have hdisp : ‖b - z‖ ≤ Rmid := by
      have hdecomp : b - z = (b - a) + (a - z) := by abel
      rw [hdecomp]
      exact (norm_add_le _ _).trans
        (add_le_add hab (le_trans (hsupportBound hz) (by nlinarith [hRw, heone.le])))
    exact hN z b hdisp
  have hweight : Integrable (fun z : Plane => we (a - z)) := by
    have hsupp : HasCompactSupport (fun z : Plane => we (a - z)) :=
      hwec.comp_homeomorph (Homeomorph.subLeft a)
    exact (hwe.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport hsupp
  have hslabBound (z : Plane) :
      |slabMeanKernel ϑ N t (t + v) z b| ≤ (N : ℝ) / 4 := by
    rw [slabMeanKernel_eq_srwKernel, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ (N : ℝ) / 4),
      abs_of_nonneg (Polymer.kernel_nonneg _ _)]
    calc
      (N : ℝ) / 4 * srwKernel _ _ ≤ (N : ℝ) / 4 * 1 :=
        mul_le_mul_of_nonneg_left (Polymer.srwKernel_le_one _ _) (by positivity)
      _ = (N : ℝ) / 4 := by ring
  have hslabMeas : Measurable (fun z : Plane => slabMeanKernel ϑ N t (t + v) z b) := by
    have hEq : (fun z : Plane => slabMeanKernel ϑ N t (t + v) z b) =
        fun z => (N : ℝ) / 4 *
          srwKernel (evenCeil ((N : ℝ) * (t + v)) - evenCeil ((N : ℝ) * t))
            (latticePoint N b - latticePoint N z) := by
      funext z
      exact slabMeanKernel_eq_srwKernel ϑ N t (t + v) z b
    rw [hEq]
    exact measurable_const.mul
      ((measurable_of_countable (fun q : Site =>
        srwKernel (evenCeil ((N : ℝ) * (t + v)) - evenCeil ((N : ℝ) * t))
          (latticePoint N b - q))).comp (measurable_latticePoint N))
  have hweightedSlab : Integrable
      (fun z : Plane => we (a - z) * slabMeanKernel ϑ N t (t + v) z b) := by
    have hmajor : Integrable (fun z : Plane => ‖we (a - z)‖ * ((N : ℝ) / 4)) :=
      hweight.norm.mul_const ((N : ℝ) / 4)
    have hmeas : Measurable (fun z : Plane =>
        we (a - z) * slabMeanKernel ϑ N t (t + v) z b) :=
      (hwe.comp (continuous_const.sub continuous_id)).measurable.mul hslabMeas
    apply hmajor.mono' hmeas.aestronglyMeasurable
    filter_upwards [] with z
    calc
      ‖we (a - z) * slabMeanKernel ϑ N t (t + v) z b‖ =
          we (a - z) * |slabMeanKernel ϑ N t (t + v) z b| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hweNonneg _)]
      _ ≤ we (a - z) * ((N : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left (hslabBound z) (hweNonneg _)
      _ = ‖we (a - z)‖ * ((N : ℝ) / 4) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (hweNonneg _)]
  have hheatInt : Integrable
      (fun z : Plane => we (a - z) * heatKernel v (b - z)) := by
    have hc : Continuous (fun z : Plane => we (a - z) * heatKernel v (b - z)) := by
      exact (hwe.comp (continuous_const.sub continuous_id)).mul
        ((Critical2DKPZ.continuous_heatKernel v).comp (continuous_const.sub continuous_id))
    have hsupp : HasCompactSupport
        (fun z : Plane => we (a - z) * heatKernel v (b - z)) := by
      exact (hwec.comp_homeomorph (Homeomorph.subLeft a)).mul_right
    exact hc.integrable_of_hasCompactSupport hsupp
  have hdiffInt : Integrable (fun z : Plane => we (a - z) *
      (slabMeanKernel ϑ N t (t + v) z b - heatKernel v (b - z))) := by
    have hEq : (fun z : Plane => we (a - z) *
        (slabMeanKernel ϑ N t (t + v) z b - heatKernel v (b - z))) =
        (fun z => we (a - z) * slabMeanKernel ϑ N t (t + v) z b) -
          (fun z => we (a - z) * heatKernel v (b - z)) := by
      funext z
      simp only [Pi.sub_apply]
      ring
    rw [hEq]
    exact hweightedSlab.sub hheatInt
  have hdiffIntegral :
      slabSmoothedConnector ϑ N t (t + v) we a b -
        (∫ z, we (a - z) * heatKernel v (b - z)) =
      ∫ z, we (a - z) *
        (slabMeanKernel ϑ N t (t + v) z b - heatKernel v (b - z)) := by
    rw [slabSmoothedConnector]
    calc
      _ = (∫ z, we (a - z) * slabMeanKernel ϑ N t (t + v) z b) -
          ∫ z, we (a - z) * heatKernel v (b - z) := rfl
      _ = ∫ z, we (a - z) *
          (slabMeanKernel ϑ N t (t + v) z b - heatKernel v (b - z)) := by
        rw [← integral_sub hweightedSlab hheatInt]
        apply integral_congr_ae
        filter_upwards [] with z
        ring
  have herror : |∫ z, we (a - z) *
      (slabMeanKernel ϑ N t (t + v) z b - heatKernel v (b - z))| ≤ δ := by
    calc
      _ = ‖∫ z, we (a - z) *
          (slabMeanKernel ϑ N t (t + v) z b - heatKernel v (b - z))‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ ∫ z, ‖we (a - z) *
          (slabMeanKernel ϑ N t (t + v) z b - heatKernel v (b - z))‖ :=
        norm_integral_le_integral_norm _
      _ = ∫ z, |we (a - z) *
          (slabMeanKernel ϑ N t (t + v) z b - heatKernel v (b - z))| := by
        apply integral_congr_ae
        filter_upwards [] with z
        exact Real.norm_eq_abs _
      _ ≤ ∫ z, we (a - z) * δ := by
        apply integral_mono hdiffInt.abs (hweight.mul_const δ)
        intro z
        change |we (a - z) *
          (slabMeanKernel ϑ N t (t + v) z b - heatKernel v (b - z))| ≤ we (a - z) * δ
        by_cases hzero : we (a - z) = 0
        · simp [hzero]
        · rw [abs_mul, abs_of_nonneg (hweNonneg _)]
          exact mul_le_mul_of_nonneg_left (le_of_lt (hNkernel hzero)) (hweNonneg _)
      _ = δ := by rw [integral_mul_const, hmassTranslate, one_mul]
  have hcont :
      |(∫ z, we (a - z) * heatKernel v (b - z)) - heatKernel v (b - a)| < δ := by
    have h := hprofile e he (lt_of_lt_of_le heη (min_le_right _ _)) a b
    simpa only [show (fun z => e⁻¹ ^ 2 * w (e⁻¹ • (a - z))) =
      fun z => we (a - z) by rfl] using h
  have hraw : |slabMeanKernel ϑ N t (t + v) a b - heatKernel v (b - a)| < δ := by
    have hba : ‖b - a‖ ≤ Rmid := hab.trans (by dsimp [Rmid]; linarith)
    exact hN a b hba
  have hsmoothedErr :
      |slabSmoothedConnector ϑ N t (t + v) we a b -
          (∫ z, we (a - z) * heatKernel v (b - z))| ≤ δ := by
    rw [hdiffIntegral]
    exact herror
  have hsmoothed :
      |slabSmoothedConnector ϑ N t (t + v) we a b - heatKernel v (b - a)| ≤ 2 * δ := by
    calc
      _ ≤ |slabSmoothedConnector ϑ N t (t + v) we a b -
            (∫ z, we (a - z) * heatKernel v (b - z))| +
          |(∫ z, we (a - z) * heatKernel v (b - z)) - heatKernel v (b - a)| :=
        abs_sub_le _ _ _
      _ ≤ δ + δ := add_le_add hsmoothedErr (le_of_lt hcont)
      _ = 2 * δ := by ring
  calc
    |slabSmoothedConnector ϑ N t (t + v) we a b -
        slabMeanKernel ϑ N t (t + v) a b| ≤ 2 * δ + δ := by
      calc
        _ = |(slabSmoothedConnector ϑ N t (t + v) we a b - heatKernel v (b - a)) +
            (heatKernel v (b - a) - slabMeanKernel ϑ N t (t + v) a b)| := by
          congr 1
          ring
        _ ≤ |slabSmoothedConnector ϑ N t (t + v) we a b - heatKernel v (b - a)| +
            |heatKernel v (b - a) - slabMeanKernel ϑ N t (t + v) a b| := abs_add_le _ _
        _ ≤ 2 * δ + δ := add_le_add hsmoothed (le_of_lt (by simpa only [abs_sub_comm] using hraw))
    _ < ε := by dsimp [δ]; linarith

/-- Convolving a slab kernel with a compactly supported unit-mass profile preserves a Gaussian
envelope uniformly over mollifier scales `e ≤ 1`. -/
theorem exists_slabSmoothedConnector_gaussianBound (ϑ : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {v : ℝ} (hv : 0 < v) (w : Plane → ℝ) (hw : Continuous w)
    (hwc : HasCompactSupport w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∫ x, w x = 1) :
    ∃ C c : ℝ, 0 < c ∧ ∀ e : ℝ, 0 < e → e ≤ 1 → ∀ N a b,
      |slabSmoothedConnector ϑ N t (t + v)
        (fun x => e⁻¹ ^ 2 * w (e⁻¹ • x)) a b| ≤ C * Real.exp (-c * ‖b - a‖ ^ 2) := by
  obtain ⟨C₀, c₀, hc₀, hraw⟩ := exists_slabMeanKernel_gaussianBound ϑ ht hv
  have hC₀ : 0 ≤ C₀ := by
    have h := hraw 0 (0 : Plane) 0
    have hnonneg : 0 ≤ |slabMeanKernel ϑ 0 t (t + v) 0 0| := abs_nonneg _
    have hexp : 0 < Real.exp (-c₀ * ‖(0 : Plane) - 0‖ ^ 2) := Real.exp_pos _
    nlinarith
  obtain ⟨Rw₀, hRw₀⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp hwc.isBounded
  let Rw := max Rw₀ 0
  have hRw : 0 ≤ Rw := le_max_right _ _
  have hwBound {x : Plane} (hx : x ∈ tsupport w) : ‖x‖ ≤ Rw := by
    have hball := hRw₀ hx
    have hn : ‖x‖ ≤ Rw₀ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hball
    exact hn.trans (le_max_left _ _)
  refine ⟨C₀ * Real.exp (c₀ * Rw ^ 2), c₀ / 2, by positivity, ?_⟩
  intro e he heone N a b
  let we : Plane → ℝ := fun x => e⁻¹ ^ 2 * w (e⁻¹ • x)
  have hwe : Continuous we := by
    exact continuous_const.mul (hw.comp
      ((continuous_const : Continuous fun _ : Plane => e⁻¹).smul continuous_id))
  have hwec : HasCompactSupport we := by
    have hcomp : HasCompactSupport (fun x : Plane => w (e⁻¹ • x)) :=
      hwc.comp_smul (inv_ne_zero he.ne')
    change HasCompactSupport (fun x : Plane => (e⁻¹ ^ 2 : ℝ) • w (e⁻¹ • x))
    exact HasCompactSupport.smul_left
      (f := fun _ : Plane => (e⁻¹ ^ 2 : ℝ)) hcomp
  have hmass : ∫ x, we x = 1 := integral_slabScaledProfile_eq_one he w hw1
  have hweNonneg (x : Plane) : 0 ≤ we x := by
    dsimp [we]
    exact mul_nonneg (sq_nonneg _) (hw0 _)
  have hweight : Integrable (fun z : Plane => we (a - z)) := by
    have hsupp : HasCompactSupport (fun z : Plane => we (a - z)) :=
      hwec.comp_homeomorph (Homeomorph.subLeft a)
    exact (hwe.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport hsupp
  have hmassTranslate : ∫ z, we (a - z) = 1 := by
    rw [integral_sub_left_eq_self we volume a, hmass]
  have hsupportBound {z : Plane} (hzero : we (a - z) ≠ 0) :
      ‖a - z‖ ≤ Rw := by
    have hmem : e⁻¹ • (a - z) ∈ tsupport w := by
      by_contra hnot
      have hz : w (e⁻¹ • (a - z)) = 0 := image_eq_zero_of_notMem_tsupport hnot
      apply hzero
      simp [we, hz]
    have hn := hwBound hmem
    have hnorm : ‖e⁻¹ • (a - z)‖ = e⁻¹ * ‖a - z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr he)]
    rw [hnorm] at hn
    have hmul := mul_le_mul_of_nonneg_left hn he.le
    have hcancel : e * e⁻¹ = 1 := by field_simp
    have hleft : e * (e⁻¹ * ‖a - z‖) = ‖a - z‖ := by
      rw [← mul_assoc, hcancel, one_mul]
    rw [hleft] at hmul
    have hscaleBound : e * Rw ≤ Rw := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right heone hRw
    exact hmul.trans hscaleBound
  have hslabBound (z : Plane) :
      |slabMeanKernel ϑ N t (t + v) z b| ≤ (N : ℝ) / 4 := by
    rw [slabMeanKernel_eq_srwKernel, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ (N : ℝ) / 4),
      abs_of_nonneg (Polymer.kernel_nonneg _ _)]
    calc
      (N : ℝ) / 4 * srwKernel _ _ ≤ (N : ℝ) / 4 * 1 :=
        mul_le_mul_of_nonneg_left (Polymer.srwKernel_le_one _ _) (by positivity)
      _ = (N : ℝ) / 4 := by ring
  have hslabMeas : Measurable (fun z : Plane => slabMeanKernel ϑ N t (t + v) z b) := by
    have hEq : (fun z : Plane => slabMeanKernel ϑ N t (t + v) z b) =
        fun z => (N : ℝ) / 4 *
          srwKernel (evenCeil ((N : ℝ) * (t + v)) - evenCeil ((N : ℝ) * t))
            (latticePoint N b - latticePoint N z) := by
      funext z
      exact slabMeanKernel_eq_srwKernel ϑ N t (t + v) z b
    rw [hEq]
    exact measurable_const.mul
      ((measurable_of_countable (fun q : Site =>
      srwKernel (evenCeil ((N : ℝ) * (t + v)) - evenCeil ((N : ℝ) * t))
        (latticePoint N b - q))).comp (measurable_latticePoint N))
  have hweightedSlab : Integrable
      (fun z : Plane => we (a - z) * slabMeanKernel ϑ N t (t + v) z b) := by
    have hmajor : Integrable (fun z : Plane => ‖we (a - z)‖ * ((N : ℝ) / 4)) :=
      hweight.norm.mul_const ((N : ℝ) / 4)
    have hm : Measurable (fun z : Plane =>
        we (a - z) * slabMeanKernel ϑ N t (t + v) z b) :=
      (hwe.comp (continuous_const.sub continuous_id)).measurable.mul hslabMeas
    apply hmajor.mono' hm.aestronglyMeasurable
    filter_upwards [] with z
    calc
      ‖we (a - z) * slabMeanKernel ϑ N t (t + v) z b‖ =
          we (a - z) * |slabMeanKernel ϑ N t (t + v) z b| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hweNonneg _)]
      _ ≤ we (a - z) * ((N : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left (hslabBound z) (hweNonneg _)
      _ = ‖we (a - z)‖ * ((N : ℝ) / 4) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (hweNonneg _)]
  let D := C₀ * Real.exp (c₀ * Rw ^ 2)
  have hkernel (z : Plane) (hzero : we (a - z) ≠ 0) :
      |slabMeanKernel ϑ N t (t + v) z b| ≤ D * Real.exp (-c₀ / 2 * ‖b - a‖ ^ 2) := by
    have hshift : ‖a - z‖ ≤ Rw := hsupportBound hzero
    have htri : ‖b - a‖ ≤ ‖b - z‖ + ‖a - z‖ := by
      calc
        ‖b - a‖ = ‖(b - z) + (z - a)‖ := by congr 1; abel
        _ ≤ ‖b - z‖ + ‖z - a‖ := norm_add_le _ _
        _ = ‖b - z‖ + ‖a - z‖ := by congr 1; exact norm_sub_rev z a
    have hsq : ‖b - a‖ ^ 2 ≤ 2 * ‖b - z‖ ^ 2 + 2 * Rw ^ 2 := by
      have hsquare := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr htri
      nlinarith [sq_nonneg (‖b - z‖ - ‖a - z‖), norm_nonneg (b - z),
        norm_nonneg (a - z), hshift, hsquare]
    have harg : -c₀ * ‖b - z‖ ^ 2 ≤
        c₀ * Rw ^ 2 - c₀ / 2 * ‖b - a‖ ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hsq hc₀.le
      nlinarith
    have hexp := Real.exp_le_exp.mpr harg
    have hprod : Real.exp (-c₀ * ‖b - z‖ ^ 2) ≤
        Real.exp (c₀ * Rw ^ 2) * Real.exp (-c₀ / 2 * ‖b - a‖ ^ 2) := by
      calc
        _ ≤ Real.exp (c₀ * Rw ^ 2 - c₀ / 2 * ‖b - a‖ ^ 2) := hexp
        _ = _ := by
          rw [← Real.exp_add]
          congr 1
          ring
    calc
      _ ≤ C₀ * Real.exp (-c₀ * ‖b - z‖ ^ 2) := hraw N z b
      _ ≤ D * Real.exp (-c₀ / 2 * ‖b - a‖ ^ 2) := by
        have hmul := mul_le_mul_of_nonneg_left hprod hC₀
        simpa [D, mul_assoc] using hmul
  have hmajor : Integrable (fun z : Plane =>
      we (a - z) * (D * Real.exp (-c₀ / 2 * ‖b - a‖ ^ 2))) :=
    hweight.mul_const _
  rw [slabSmoothedConnector]
  calc
    |∫ z, we (a - z) * slabMeanKernel ϑ N t (t + v) z b| ≤
        ∫ z, |we (a - z) * slabMeanKernel ϑ N t (t + v) z b| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ z, we (a - z) * (D * Real.exp (-c₀ / 2 * ‖b - a‖ ^ 2)) := by
      apply integral_mono hweightedSlab.abs hmajor
      intro z
      change |we (a - z) * slabMeanKernel ϑ N t (t + v) z b| ≤
        we (a - z) * (D * Real.exp (-c₀ / 2 * ‖b - a‖ ^ 2))
      by_cases hzero : we (a - z) = 0
      · simp [hzero]
      · rw [abs_mul, abs_of_nonneg (hweNonneg _)]
        exact mul_le_mul_of_nonneg_left (hkernel z hzero) (hweNonneg _)
    _ = D * Real.exp (-c₀ / 2 * ‖b - a‖ ^ 2) := by
      rw [integral_mul_const, hmassTranslate, one_mul]
    _ = C₀ * Real.exp (c₀ * Rw ^ 2) *
        Real.exp (-(c₀ / 2) * ‖b - a‖ ^ 2) := by
      dsimp [D]
      congr 1
      ring

/-- The product of the two outer endpoint masses has a uniformly bounded second moment. This
companion is used when a compact cutoff is removed from a kernel pairing. -/
theorem eventually_slabOuterEndpointMassProduct_sq_bound (ϑ : ℝ)
    {s t r u : ℝ} (hs : 0 ≤ s) (hst : s < t) (htr : t < r) (hru : r < u)
    (Φ : C_c(Plane × Plane, ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω =>
        (((polymerMeasure ϑ N s t ω
          ((Prod.fst '' tsupport Φ) ×ˢ (Set.univ : Set Plane))).toReal) *
          ((polymerMeasure ϑ N r u ω
          ((Set.univ : Set Plane) ×ˢ (Prod.snd '' tsupport Φ))).toReal)) ^ 2)
        disorderLaw ∧
      ∫ ω,
        (((polymerMeasure ϑ N s t ω
          ((Prod.fst '' tsupport Φ) ×ˢ (Set.univ : Set Plane))).toReal) *
          ((polymerMeasure ϑ N r u ω
          ((Set.univ : Set Plane) ×ˢ (Prod.snd '' tsupport Φ))).toReal)) ^ 2
        ∂disorderLaw ≤ C := by
  classical
  let A : Set Plane := Prod.fst '' tsupport Φ
  let B : Set Plane := Prod.snd '' tsupport Φ
  have hA : IsCompact A := Φ.hasCompactSupport.image continuous_fst
  have hB : IsCompact B := Φ.hasCompactSupport.image continuous_snd
  obtain ⟨RA₀, hRA₀⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp hA.isBounded
  obtain ⟨RB₀, hRB₀⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp hB.isBounded
  let RA := max RA₀ 0
  let RB := max RB₀ 0
  have hRA : 0 ≤ RA := le_max_right _ _
  have hRB : 0 ≤ RB := le_max_right _ _
  have hAbox {x : Plane} (hx : x ∈ A) : ‖x‖ ≤ RA := by
    have hball := hRA₀ hx
    have hn : ‖x‖ ≤ RA₀ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hball
    exact hn.trans (le_max_left _ _)
  have hBbox {y : Plane} (hy : y ∈ B) : ‖y‖ ≤ RB := by
    have hball := hRB₀ hy
    have hn : ‖y‖ ≤ RB₀ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hball
    exact hn.trans (le_max_left _ _)
  obtain ⟨CXraw, hXevent⟩ := eventually_firstCompact_mass_sixth_integrable_le
    ϑ hs hst A hA RA hRA (fun x hx => hAbox hx)
  have hr0 : 0 ≤ r := by linarith
  obtain ⟨CYraw, hYevent⟩ := eventually_secondCutoff_sixth_integrable_le
    ϑ hr0 hru RB hRB
  let CX := max CXraw 0
  let CY := max CYraw 0
  have hCX : 0 ≤ CX := le_max_right _ _
  have hCY : 0 ≤ CY := le_max_right _ _
  refine ⟨2 + CX + CY, by positivity, ?_⟩
  filter_upwards [hXevent, hYevent] with N hXN hYN
  let X : Disorder → ℝ := fun ω =>
    (polymerMeasure ϑ N s t ω (A ×ˢ (Set.univ : Set Plane))).toReal
  let Y : Disorder → ℝ := fun ω =>
    (polymerMeasure ϑ N r u ω ((Set.univ : Set Plane) ×ˢ B)).toReal
  let Z : Disorder → ℝ := fun ω =>
    ∫ y, polymerTailCutoff RB hRB y
      ∂((polymerMeasure ϑ N r u ω).map Prod.snd)
  have hXm : Measurable X := by
    dsimp [X, A]
    exact measurable_polymerMeasure_real_mass ϑ N s t _
      (hA.measurableSet.prod MeasurableSet.univ)
  have hYm : Measurable Y := by
    dsimp [Y, B]
    exact measurable_polymerMeasure_real_mass ϑ N r u _
      (MeasurableSet.univ.prod hB.measurableSet)
  have hXnonneg (ω : Disorder) : 0 ≤ X ω := ENNReal.toReal_nonneg
  have hYnonneg (ω : Disorder) : 0 ≤ Y ω := ENNReal.toReal_nonneg
  have hZnonneg (ω : Disorder) : 0 ≤ Z ω :=
    integral_nonneg fun y => polymerTailCutoff_nonneg RB hRB y
  have hYleZ (ω : Disorder) : Y ω ≤ Z ω := by
    dsimp [Y, Z, B]
    have h := polymerMeasure_compact_second_mass_le_flatCutoff
      ϑ N r u ω B hB RB hRB (fun y hy => hBbox hy)
    have habs : (fun y : Plane => |polymerTailCutoff RB hRB y|) =
        fun y => polymerTailCutoff RB hRB y := by
      funext y
      exact abs_of_nonneg (polymerTailCutoff_nonneg RB hRB y)
    rw [habs] at h
    exact h
  have hX6 : Integrable (fun ω => X ω ^ 6) disorderLaw := by
    simpa [X, A] using hXN.1
  have hX6bound : ∫ ω, X ω ^ 6 ∂disorderLaw ≤ CX := by
    have hraw : ∫ ω, X ω ^ 6 ∂disorderLaw ≤ CXraw := by
      simpa [X, A] using hXN.2
    exact hraw.trans (le_max_left _ _)
  have hZ6 : Integrable (fun ω => Z ω ^ 6) disorderLaw := by
    dsimp [Z]
    exact hYN.1
  have hY6 : Integrable (fun ω => Y ω ^ 6) disorderLaw := by
    apply hZ6.mono' (hYm.pow_const 6).aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hYnonneg ω) 6)]
    exact pow_le_pow_left₀ (hYnonneg ω) (hYleZ ω) 6
  have hY6bound : ∫ ω, Y ω ^ 6 ∂disorderLaw ≤ CY := by
    have hraw : ∫ ω, Y ω ^ 6 ∂disorderLaw ≤ CYraw := by
      calc
        _ ≤ ∫ ω, Z ω ^ 6 ∂disorderLaw :=
          integral_mono_ae hY6 hZ6 (Filter.Eventually.of_forall fun ω =>
            pow_le_pow_left₀ (hYnonneg ω) (hYleZ ω) 6)
        _ ≤ _ := by simpa [Z] using hYN.2
    exact hraw.trans (le_max_left _ _)
  have hX4 : Integrable (fun ω => X ω ^ 4) disorderLaw := by
    have hmajor : Integrable (fun ω => 1 + X ω ^ 6) disorderLaw :=
      (integrable_const (1 : ℝ)).add hX6
    apply hmajor.mono' (hXm.pow_const 4).aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_of_nonneg (pow_nonneg (hXnonneg ω) 4)]
    by_cases hle : X ω ≤ 1
    · have hpow : X ω ^ 4 ≤ 1 := pow_le_one₀ (hXnonneg ω) hle
      nlinarith [pow_nonneg (hXnonneg ω) 6]
    · have hge : 1 ≤ X ω := le_of_not_ge hle
      have hpow : X ω ^ 4 ≤ X ω ^ 6 := by
        calc
          X ω ^ 4 ≤ X ω ^ 4 * X ω ^ 2 :=
            le_mul_of_one_le_right (pow_nonneg (hXnonneg ω) 4) (one_le_pow₀ hge)
          _ = X ω ^ 6 := by ring
      exact hpow.trans (le_add_of_nonneg_left (by positivity))
  have hY4 : Integrable (fun ω => Y ω ^ 4) disorderLaw := by
    have hmajor : Integrable (fun ω => 1 + Y ω ^ 6) disorderLaw :=
      (integrable_const (1 : ℝ)).add hY6
    apply hmajor.mono' (hYm.pow_const 4).aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_of_nonneg (pow_nonneg (hYnonneg ω) 4)]
    by_cases hle : Y ω ≤ 1
    · have hpow : Y ω ^ 4 ≤ 1 := pow_le_one₀ (hYnonneg ω) hle
      nlinarith [pow_nonneg (hYnonneg ω) 6]
    · have hge : 1 ≤ Y ω := le_of_not_ge hle
      have hpow : Y ω ^ 4 ≤ Y ω ^ 6 := by
        calc
          Y ω ^ 4 ≤ Y ω ^ 4 * Y ω ^ 2 :=
            le_mul_of_one_le_right (pow_nonneg (hYnonneg ω) 4) (one_le_pow₀ hge)
          _ = Y ω ^ 6 := by ring
      exact hpow.trans (le_add_of_nonneg_left (by positivity))
  have hX4bound : ∫ ω, X ω ^ 4 ∂disorderLaw ≤ 1 + CX := by
    have hmajor : Integrable (fun ω => 1 + X ω ^ 6) disorderLaw :=
      (integrable_const (1 : ℝ)).add hX6
    have hpoint (ω : Disorder) : X ω ^ 4 ≤ 1 + X ω ^ 6 := by
      by_cases hle : X ω ≤ 1
      · have hpow : X ω ^ 4 ≤ 1 := pow_le_one₀ (hXnonneg ω) hle
        linarith [pow_nonneg (hXnonneg ω) 6]
      · have hge : 1 ≤ X ω := le_of_not_ge hle
        have hpow : X ω ^ 4 ≤ X ω ^ 6 := by
          calc
            X ω ^ 4 ≤ X ω ^ 4 * X ω ^ 2 :=
              le_mul_of_one_le_right (pow_nonneg (hXnonneg ω) 4) (one_le_pow₀ hge)
            _ = X ω ^ 6 := by ring
        linarith
    calc
      _ ≤ ∫ ω, (1 + X ω ^ 6) ∂disorderLaw :=
        integral_mono hX4 hmajor hpoint
      _ = 1 + ∫ ω, X ω ^ 6 ∂disorderLaw := by
        rw [integral_add (integrable_const (1 : ℝ)) hX6, integral_const]
        simp [Measure.real, measure_univ]
      _ ≤ 1 + CX := by linarith
  have hY4bound : ∫ ω, Y ω ^ 4 ∂disorderLaw ≤ 1 + CY := by
    have hmajor : Integrable (fun ω => 1 + Y ω ^ 6) disorderLaw :=
      (integrable_const (1 : ℝ)).add hY6
    have hpoint (ω : Disorder) : Y ω ^ 4 ≤ 1 + Y ω ^ 6 := by
      by_cases hle : Y ω ≤ 1
      · have hpow : Y ω ^ 4 ≤ 1 := pow_le_one₀ (hYnonneg ω) hle
        linarith [pow_nonneg (hYnonneg ω) 6]
      · have hge : 1 ≤ Y ω := le_of_not_ge hle
        have hpow : Y ω ^ 4 ≤ Y ω ^ 6 := by
          calc
            Y ω ^ 4 ≤ Y ω ^ 4 * Y ω ^ 2 :=
              le_mul_of_one_le_right (pow_nonneg (hYnonneg ω) 4) (one_le_pow₀ hge)
            _ = Y ω ^ 6 := by ring
        linarith
    calc
      _ ≤ ∫ ω, (1 + Y ω ^ 6) ∂disorderLaw :=
        integral_mono hY4 hmajor hpoint
      _ = 1 + ∫ ω, Y ω ^ 6 ∂disorderLaw := by
        rw [integral_add (integrable_const (1 : ℝ)) hY6, integral_const]
        simp [Measure.real, measure_univ]
      _ ≤ 1 + CY := by linarith
  have hprodMeas : Measurable (fun ω => (X ω * Y ω) ^ 2) :=
    (hXm.mul hYm).pow_const 2
  have hsum : Integrable (fun ω => (X ω ^ 4 + Y ω ^ 4) / 2) disorderLaw := by
    exact ((hX4.add hY4).const_mul (1 / 2)).congr
      (Filter.Eventually.of_forall fun ω => by
        change (1 / 2 : ℝ) * (X ω ^ 4 + Y ω ^ 4) =
          (X ω ^ 4 + Y ω ^ 4) / 2
        ring)
  have hprodInt : Integrable (fun ω => (X ω * Y ω) ^ 2) disorderLaw := by
    apply hsum.mono' hprodMeas.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_of_nonneg (sq_nonneg (X ω * Y ω))]
    nlinarith [sq_nonneg (X ω ^ 2 - Y ω ^ 2)]
  have hprodBound :
      ∫ ω, (X ω * Y ω) ^ 2 ∂disorderLaw ≤ 2 + CX + CY := by
    calc
      _ ≤ ∫ ω, (X ω ^ 4 + Y ω ^ 4) / 2 ∂disorderLaw := by
        apply integral_mono hprodInt hsum
        intro ω
        nlinarith [sq_nonneg (X ω ^ 2 - Y ω ^ 2)]
      _ = ((∫ ω, X ω ^ 4 ∂disorderLaw) + ∫ ω, Y ω ^ 4 ∂disorderLaw) / 2 := by
        rw [show (fun ω => (X ω ^ 4 + Y ω ^ 4) / 2) =
          fun ω => (1 / 2 : ℝ) * (X ω ^ 4 + Y ω ^ 4) by funext ω; ring,
          integral_const_mul, integral_add hX4 hY4]
        ring
      _ ≤ 2 + CX + CY := by linarith [hX4bound, hY4bound]
  refine ⟨hprodInt, ?_⟩
  simpa only [X, Y, A, B] using hprodBound

/-- The continuum connector obtained by smoothing the heat kernel with the reflected profile. -/
noncomputable def slabSmoothedHeatConnector (v e : ℝ) (w : Plane → ℝ) : Plane × Plane → ℝ :=
  let wₑ : Plane → ℝ := fun x => e⁻¹ ^ 2 * w (e⁻¹ • x)
  let wᵣ : Plane → ℝ := fun x => wₑ (-x)
  fun p => ((heatKernel v) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] wᵣ) (p.2 - p.1)

/-- Convolution with a compactly supported profile makes the heat connector continuous. -/
theorem continuous_slabSmoothedHeatConnector {v e : ℝ} (he : 0 < e)
    (w : Plane → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w) :
    Continuous (slabSmoothedHeatConnector v e w) := by
  let wₑ : Plane → ℝ := fun x => e⁻¹ ^ 2 * w (e⁻¹ • x)
  have hwₑ : Continuous wₑ := by
    exact continuous_const.mul (hw.comp
      ((continuous_const : Continuous fun _ : Plane => e⁻¹).smul continuous_id))
  have hwₑc : HasCompactSupport wₑ := by
    have hcomp : HasCompactSupport (fun x : Plane => w (e⁻¹ • x)) :=
      hwc.comp_smul (inv_ne_zero he.ne')
    change HasCompactSupport (fun x : Plane => (e⁻¹ ^ 2 : ℝ) • w (e⁻¹ • x))
    exact HasCompactSupport.smul_left
      (f := fun _ : Plane => (e⁻¹ ^ 2 : ℝ)) hcomp
  let wᵣ : Plane → ℝ := fun x => wₑ (-x)
  have hwᵣ : Continuous wᵣ := hwₑ.comp continuous_neg
  have hwᵣc : HasCompactSupport wᵣ :=
    hwₑc.comp_homeomorph (Homeomorph.neg Plane)
  have hconv : Continuous
      ((heatKernel v) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] wᵣ) := by
    exact hwᵣc.continuous_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (Critical2DKPZ.continuous_heatKernel v).locallyIntegrable hwᵣ
  exact hconv.comp (continuous_snd.sub continuous_fst)

/-- The smoothed heat connector is the integral of the scaled profile against the translated heat kernel. -/
theorem slabSmoothedHeatConnector_eq_integral {v e : ℝ} (w : Plane → ℝ) (a b : Plane) :
    slabSmoothedHeatConnector v e w (a, b) =
      ∫ y, e⁻¹ ^ 2 * w (e⁻¹ • (a - y)) * heatKernel v (b - y) := by
  let wₑ : Plane → ℝ := fun x => e⁻¹ ^ 2 * w (e⁻¹ • x)
  let wᵣ : Plane → ℝ := fun x => wₑ (-x)
  change ((heatKernel v) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] wᵣ) (b - a) = _
  rw [convolution_def]
  have hchange := integral_sub_left_eq_self
    (fun y : Plane => heatKernel v y * wᵣ ((b - a) - y)) volume b
  calc
    _ = ∫ y, heatKernel v y * wᵣ ((b - a) - y) := rfl
    _ = ∫ y, heatKernel v (b - y) * wᵣ ((b - a) - (b - y)) := hchange.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [wᵣ, wₑ]
      rw [show -(b - a - (b - y)) = a - y by abel]
      ring


/-- The squared difference between the smoothed and unsmoothed separated slab products is integrable at every finite scale. -/
theorem integrable_slabSmoothedProduct_sub_slabProduct_sq
    (ϑ : ℝ) (N : ℕ) {s t u : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (Φ : C_c(Plane × Plane, ℝ)) (w : Plane → ℝ)
    (hw : Continuous w) (hwc : HasCompactSupport w) {v : ℝ}
    (hv : 0 < v) (hvu : t + v < u) {e : ℝ} (he : 0 < e) :
    Integrable (fun ω =>
      (kernelProductPairing (polymerMeasure ϑ N s t ω)
          (fun a b => ∫ y, e⁻¹ ^ 2 * w (e⁻¹ • (a - y)) *
            slabMeanKernel ϑ N t (t + v) y b)
          (polymerMeasure ϑ N (t + v) u ω) Φ -
        kernelProductPairing (polymerMeasure ϑ N s t ω)
          (slabMeanKernel ϑ N t (t + v))
          (polymerMeasure ϑ N (t + v) u ω) Φ) ^ 2) disorderLaw := by
  classical
  let wₑ : Plane → ℝ := fun x => e⁻¹ ^ 2 * w (e⁻¹ • x)
  have hwₑ : Continuous wₑ := by
    dsimp [wₑ]
    exact continuous_const.mul (hw.comp
      ((continuous_const : Continuous fun _ : Plane => e⁻¹).smul continuous_id))
  have hwₑc : HasCompactSupport wₑ := by
    have hcomp : HasCompactSupport (fun x : Plane => w (e⁻¹ • x)) :=
      hwc.comp_smul (inv_ne_zero he.ne')
    change HasCompactSupport (fun x : Plane => (e⁻¹ ^ 2 : ℝ) • w (e⁻¹ • x))
    exact HasCompactSupport.smul_left
      (f := fun _ : Plane => (e⁻¹ ^ 2 : ℝ)) hcomp
  by_cases hN : N = 0
  · subst N
    simp [polymerMeasure_zero_at_zero, kernelProductPairing]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    let t' : ℝ := t + v
    let b : ℕ := evenCeil ((N : ℝ) * t)
    let c : ℕ := evenCeil ((N : ℝ) * t')
    let A : Disorder → ℝ := fun ω =>
      kernelProductPairing (polymerMeasure ϑ N s t ω)
        (fun a b => ∫ y, wₑ (a - y) * slabMeanKernel ϑ N t t' y b)
        (polymerMeasure ϑ N t' u ω) Φ
    let B : Disorder → ℝ := fun ω =>
      kernelProductPairing (polymerMeasure ϑ N s t ω) (slabMeanKernel ϑ N t t')
        (polymerMeasure ϑ N t' u ω) Φ
    let X : Disorder → ℝ := fun ω =>
      smoothedProductPairing (polymerMeasure ϑ N s t ω) wₑ
        (polymerMeasure ϑ N t u ω) Φ
    let Y : Disorder → ℝ := fun ω => ∫ p, Φ p ∂(polymerMeasure ϑ N s u ω)
    have hX : MemLp X 2 disorderLaw := by
      simpa only [X] using
        (memLp_smoothedProductPairing_two ϑ N s t t u Φ wₑ hwₑ hwₑc)
    have hXm : Measurable X := by
      dsimp [X]
      exact measurable_smoothedProductPairing ϑ N s t t u Φ wₑ hwₑ hwₑc
    have hXint : Integrable X disorderLaw := hX.integrable (by norm_num)
    have hY : MemLp Y 2 disorderLaw := memLp_polymerPairing_two ϑ N s u Φ
    have hYm : Measurable Y := by
      dsimp [Y]
      exact measurable_polymerPairing ϑ N s u Φ
    have hYint : Integrable Y disorderLaw := hY.integrable (by norm_num)
    let m : MeasurableSpace Disorder :=
      Gaussian.coordinateSigma (fun _ : ℕ × Site => ℝ) (Gaussian.timeBlock b c)ᶜ
    have hm : m ≤ MeasurableSpace.pi := by
      dsimp only [m]
      exact Gaussian.coordinateSigma_le (fun _ : ℕ × Site => ℝ) (Gaussian.timeBlock b c)ᶜ
    have hXCEbase := Gaussian.condExp_coordinateSigma_ae_eq
      (fun _ : ℕ × Site => ProbabilityTheory.gaussianReal 0 1)
      (Gaussian.timeBlock b c)ᶜ hXm hXint
    have hXCE : disorderLaw[X | m] =ᵐ[disorderLaw]
        fun ω => ∫ η, X (Gaussian.resample (Gaussian.timeBlock b c)ᶜ ω η) ∂disorderLaw := by
      simpa only [disorderLaw, m] using hXCEbase
    have hXCEresample : disorderLaw[X | m] =ᵐ[disorderLaw]
        fun ω => ∫ η, X (Gaussian.resample (Gaussian.timeBlock b c) η ω) ∂disorderLaw := by
      filter_upwards [hXCE] with ω hω
      calc
        disorderLaw[X | m] ω =
            ∫ η, X (Gaussian.resample (Gaussian.timeBlock b c)ᶜ ω η) ∂disorderLaw := hω
        _ = ∫ η, X (Gaussian.resample (Gaussian.timeBlock b c) η ω) ∂disorderLaw := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun η => congrArg X
            (resample_compl_eq_swapped (Gaussian.timeBlock b c) ω η)
    let a : ℕ := evenCeil ((N : ℝ) * s)
    have hab : a ≤ b := by
      dsimp [a, b]
      exact Critical2DKPZ.evenCeil_mono
        (mul_le_mul_of_nonneg_left (le_of_lt hst) (Nat.cast_nonneg N))
    have hfirst (ω : Disorder) (x y : Site) (η : Disorder) :
        pointToPoint (criticalBeta ϑ N) a (b - a) x y
          (Gaussian.resample (Gaussian.timeBlock b c) η ω) =
        pointToPoint (criticalBeta ϑ N) a (b - a) x y ω := by
      apply blockMeasurable_resample_outside
        (a := a) (b := b) (c := b) (d := c)
        (Set.disjoint_left.mpr fun n hn hc => by
          simp only [Set.mem_Ioc] at hn hc
          omega)
      convert Polymer.measurable_pointToPoint_block (criticalBeta ϑ N) a (b - a) x y using 1
      rw [Nat.add_sub_of_le hab]
    have hμ (ω η : Disorder) :
        polymerMeasure ϑ N s t (Gaussian.resample (Gaussian.timeBlock b c) η ω) =
          polymerMeasure ϑ N s t ω := by
      have hdensity :
          (fun p : Plane × Plane => ENNReal.ofReal
            (rescaledP2P ϑ N s t p (Gaussian.resample (Gaussian.timeBlock b c) η ω))) =
          fun p => ENNReal.ofReal (rescaledP2P ϑ N s t p ω) := by
        funext p
        congr 1
        simpa only [rescaledP2P] using congrArg
          (fun r : ℝ => (N : ℝ) / 4 * r)
          (hfirst ω (latticePoint N p.1) (latticePoint N p.2) η)
      change (volume : Measure (Plane × Plane)).withDensity _ =
        (volume : Measure (Plane × Plane)).withDensity _
      rw [hdensity]
    have hXbridge (ω : Disorder) :
        (∫ η, X (Gaussian.resample (Gaussian.timeBlock b c) η ω) ∂disorderLaw) = A ω := by
      calc
        _ = ∫ η, smoothedProductPairing (polymerMeasure ϑ N s t ω) wₑ
              (polymerMeasure ϑ N t u (Gaussian.resample (Gaussian.timeBlock b c) η ω)) Φ
              ∂disorderLaw := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun η => by
              dsimp [X]
              rw [hμ ω η]
        _ = A ω := by
            dsimp [A, wₑ, t', b, c]
            exact integral_smoothedProductPairing_resample_slab_eq_kernelProductPairing
              ϑ N hNpos hs hst (by linarith) hvu Φ wₑ hwₑ hwₑc ω
    have hAce : A =ᵐ[disorderLaw] disorderLaw[X | m] := by
      filter_upwards [hXCEresample] with ω hω
      exact (hω.trans (hXbridge ω)).symm
    have hA : MemLp A 2 disorderLaw := by
      have hcond : MemLp (disorderLaw[X | m]) 2 disorderLaw := hX.condExp (by norm_num)
      exact hcond.ae_eq hAce.symm
    have hYCEbase := Gaussian.condExp_coordinateSigma_ae_eq
      (fun _ : ℕ × Site => ProbabilityTheory.gaussianReal 0 1)
      (Gaussian.timeBlock b c)ᶜ hYm hYint
    have hYCE : disorderLaw[Y | m] =ᵐ[disorderLaw]
        fun ω => ∫ η, Y (Gaussian.resample (Gaussian.timeBlock b c)ᶜ ω η) ∂disorderLaw := by
      simpa only [disorderLaw, m] using hYCEbase
    have hYCEresample : disorderLaw[Y | m] =ᵐ[disorderLaw]
        fun ω => ∫ η, Y (Gaussian.resample (Gaussian.timeBlock b c) η ω) ∂disorderLaw := by
      filter_upwards [hYCE] with ω hω
      calc
        disorderLaw[Y | m] ω =
            ∫ η, Y (Gaussian.resample (Gaussian.timeBlock b c)ᶜ ω η) ∂disorderLaw := hω
        _ = ∫ η, Y (Gaussian.resample (Gaussian.timeBlock b c) η ω) ∂disorderLaw := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun η => congrArg Y
            (resample_compl_eq_swapped (Gaussian.timeBlock b c) ω η)
    have hYbridge (ω : Disorder) :
        (∫ η, Y (Gaussian.resample (Gaussian.timeBlock b c) η ω) ∂disorderLaw) = B ω := by
      dsimp [Y, B, t', b, c]
      exact integral_polymerPairing_resample_slab_eq_kernelProductPairing
        ϑ N hNpos (le_of_lt hst) (le_add_of_nonneg_right hv.le) (le_of_lt hvu) Φ ω
    have hBce : B =ᵐ[disorderLaw] disorderLaw[Y | m] := by
      filter_upwards [hYCEresample] with ω hω
      exact (hω.trans (hYbridge ω)).symm
    have hB : MemLp B 2 disorderLaw := by
      have hcond : MemLp (disorderLaw[Y | m]) 2 disorderLaw := hY.condExp (by norm_num)
      exact hcond.ae_eq hBce.symm
    have hD : MemLp (fun ω => A ω - B ω) 2 disorderLaw := hA.sub hB
    have hDsq : Integrable (fun ω => ‖A ω - B ω‖ ^ 2) disorderLaw :=
      hD.integrable_norm_pow'
    have hrewrite (ω : Disorder) : ‖A ω - B ω‖ ^ 2 = (A ω - B ω) ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]
    have hDsq' : Integrable (fun ω => (A ω - B ω) ^ 2) disorderLaw :=
      hDsq.congr (Filter.Eventually.of_forall hrewrite)
    exact hDsq'.congr (Filter.Eventually.of_forall fun ω => by
      simp only [A, B, wₑ, t'])

end Critical2DKPZ.SHF.Flow

end
