/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.JointConvergence.Basic
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! # Moment convergence under weak convergence -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BoundedContinuousFunction ENNReal Topology

namespace Critical2DKPZ.JointConvergence

private def momentCutoff (p K : ℝ) (hp : 0 < p) (hK : 0 ≤ K) : ℝ →ᵇ ℝ :=
  ⟨⟨fun x => min (|x| ^ p) (K ^ p),
    ((Real.continuous_rpow_const hp.le).comp continuous_abs).min continuous_const⟩,
    ⟨K ^ p, fun x y => by
      rw [Real.dist_eq]
      have hx0 : 0 ≤ min (|x| ^ p) (K ^ p) :=
        le_min (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg hK _)
      have hy0 : 0 ≤ min (|y| ^ p) (K ^ p) :=
        le_min (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg hK _)
      have hxK : min (|x| ^ p) (K ^ p) ≤ K ^ p := min_le_right _ _
      have hyK : min (|y| ^ p) (K ^ p) ≤ K ^ p := min_le_right _ _
      rw [abs_le]
      constructor <;> linarith⟩⟩

private theorem rpow_cutoff_error {p q K : ℝ} (hp : 0 < p) (hpq : p < q)
    (hK : 1 ≤ K) (x : ℝ) :
    0 ≤ |x| ^ p - min (|x| ^ p) (K ^ p) ∧
      |x| ^ p - min (|x| ^ p) (K ^ p) ≤ K ^ (p - q) * |x| ^ q := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  by_cases hKa : K ≤ |x|
  · have hax : 0 < |x| := lt_of_lt_of_le hK0 hKa
    have hqp : p - q ≤ 0 := sub_nonpos.mpr hpq.le
    have hnegativePower : |x| ^ (p - q) ≤ K ^ (p - q) :=
      Real.rpow_le_rpow_of_nonpos hK0 hKa hqp
    have hdecomp : |x| ^ p = |x| ^ q * |x| ^ (p - q) := by
      calc
        |x| ^ p = |x| ^ (q + (p - q)) := by congr 1; ring
        _ = |x| ^ q * |x| ^ (p - q) := Real.rpow_add hax _ _
    have horder : K ^ p ≤ |x| ^ p :=
      Real.rpow_le_rpow hK0.le hKa hp.le
    constructor
    · exact sub_nonneg.mpr (min_le_left _ _)
    · rw [min_eq_right horder]
      calc
        |x| ^ p - K ^ p ≤ |x| ^ p := sub_le_self _ (Real.rpow_nonneg hK0.le _)
        _ = |x| ^ q * |x| ^ (p - q) := hdecomp
        _ ≤ |x| ^ q * K ^ (p - q) :=
          mul_le_mul_of_nonneg_left hnegativePower (Real.rpow_nonneg (abs_nonneg _) _)
        _ = K ^ (p - q) * |x| ^ q := by ring
  · have hKa' : |x| ≤ K := le_of_not_ge hKa
    have horder : |x| ^ p ≤ K ^ p := Real.rpow_le_rpow (abs_nonneg _) hKa' hp.le
    rw [min_eq_left horder]
    constructor
    · simp
    · simpa [sub_self] using
        (mul_nonneg (Real.rpow_nonneg hK0.le _) (Real.rpow_nonneg (abs_nonneg _) _))

private theorem integrable_abs_rpow_of_larger {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ} {p q : ℝ} (hf : AEStronglyMeasurable f μ)
    (hp : 0 < p) (hpq : p < q)
    (hfq : Integrable (fun x => |f x| ^ q) μ) :
    Integrable (fun x => |f x| ^ p) μ := by
  have hcont : Continuous (fun x : ℝ => |x| ^ p) :=
    (Real.continuous_rpow_const hp.le).comp continuous_abs
  have hmeas : AEStronglyMeasurable (fun x => |f x| ^ p) μ :=
    hcont.comp_aestronglyMeasurable hf
  have hsum : Integrable (fun x : α => 1 + |f x| ^ q) μ := integrable_const 1 |>.add hfq
  apply hsum.mono' hmeas
  filter_upwards [] with x
  have hbound : |f x| ^ p ≤ 1 + |f x| ^ q := by
    by_cases hx : 1 ≤ |f x|
    · have hpow := Real.rpow_le_rpow_of_exponent_le hx hpq.le
      linarith
    · have hx' : |f x| ≤ 1 := le_of_not_ge hx
      have hpow : |f x| ^ p ≤ 1 := Real.rpow_le_one (abs_nonneg _) hx' hp.le
      linarith [Real.rpow_nonneg (abs_nonneg (f x)) q]
  simpa [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg (f x)) p),
    Real.norm_of_nonneg (by positivity : 0 ≤ (1 + |f x| ^ q : ℝ))] using hbound

private theorem integral_rpow_cutoff_error_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ} {p q K M : ℝ}
    (hf : AEStronglyMeasurable f μ) (hp : 0 < p) (hpq : p < q) (hK : 1 ≤ K)
    (hfq : Integrable (fun x => |f x| ^ q) μ)
    (hM : ∫ x, |f x| ^ q ∂μ ≤ M) :
    |∫ x, |f x| ^ p ∂μ - ∫ x, min (|f x| ^ p) (K ^ p) ∂μ| ≤
      K ^ (p - q) * M := by
  have hfp : Integrable (fun x => |f x| ^ p) μ :=
    integrable_abs_rpow_of_larger hf hp hpq hfq
  have hcut : Integrable (fun x => min (|f x| ^ p) (K ^ p)) μ := by
    have hcont : Continuous (fun x : ℝ => min (|x| ^ p) (K ^ p)) :=
      ((Real.continuous_rpow_const hp.le).comp continuous_abs).min continuous_const
    apply (integrable_const (K ^ p)).mono' (hcont.comp_aestronglyMeasurable hf)
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (le_min (Real.rpow_nonneg (abs_nonneg _) _)
      (Real.rpow_nonneg (by positivity) _))]
    exact min_le_right _ _
  have hdiff : Integrable (fun x => |f x| ^ p - min (|f x| ^ p) (K ^ p)) μ := hfp.sub hcut
  have hscale : Integrable (fun x => K ^ (p - q) * |f x| ^ q) μ := hfq.const_mul _
  have hpoint (x : α) :
      0 ≤ |f x| ^ p - min (|f x| ^ p) (K ^ p) ∧
      |f x| ^ p - min (|f x| ^ p) (K ^ p) ≤ K ^ (p - q) * |f x| ^ q :=
    rpow_cutoff_error hp hpq hK (f x)
  have hnonneg : 0 ≤ ∫ x, (|f x| ^ p - min (|f x| ^ p) (K ^ p)) ∂μ :=
    integral_nonneg (fun x => (hpoint x).1)
  have hupper :
      ∫ x, (|f x| ^ p - min (|f x| ^ p) (K ^ p)) ∂μ ≤ K ^ (p - q) * M := by
    calc
      _ ≤ ∫ x, K ^ (p - q) * |f x| ^ q ∂μ :=
        integral_mono hdiff hscale (fun x => (hpoint x).2)
      _ = K ^ (p - q) * ∫ x, |f x| ^ q ∂μ := by
        rw [integral_const_mul]
      _ ≤ K ^ (p - q) * M :=
        mul_le_mul_of_nonneg_left hM (Real.rpow_nonneg (by positivity) _)
  have heq :
      (∫ x, |f x| ^ p ∂μ) - ∫ x, min (|f x| ^ p) (K ^ p) ∂μ =
        ∫ x, (|f x| ^ p - min (|f x| ^ p) (K ^ p)) ∂μ := by
    rw [integral_sub hfp hcut]
  rw [heq]
  calc
    |∫ x, (|f x| ^ p - min (|f x| ^ p) (K ^ p)) ∂μ| =
        ∫ x, (|f x| ^ p - min (|f x| ^ p) (K ^ p)) ∂μ := abs_of_nonneg hnonneg
    _ ≤ K ^ (p - q) * M := hupper

/-- If `X N → Y` in law and the `q`-th absolute moments of `X N` are eventually integrable with
bound `M`, then `|Y|^q` is integrable and `∫ |Y|^q ≤ M`. -/
theorem integrable_rpow_limit_of_tendstoInDistribution {Ω' Ω : Type*}
    [MeasurableSpace Ω'] [MeasurableSpace Ω] {μ : ℕ → Measure Ω'} {P : Measure Ω}
    [∀ N, IsProbabilityMeasure (μ N)] [IsProbabilityMeasure P]
    {X : ℕ → Ω' → ℝ} {Y : Ω → ℝ} {q M : ℝ}
    (hX : TendstoInDistribution X atTop Y μ P) (hq : 0 < q)
    (hint : ∀ᶠ N in atTop, Integrable (fun ω => |X N ω| ^ q) (μ N))
    (hbound : ∀ᶠ N in atTop, ∫ ω, |X N ω| ^ q ∂(μ N) ≤ M) :
    Integrable (fun ω => |Y ω| ^ q) P ∧ ∫ ω, |Y ω| ^ q ∂P ≤ M := by
  have hYsm : AEStronglyMeasurable Y P := hX.aemeasurable_limit.aestronglyMeasurable
  have hqCont : Continuous (fun x : ℝ => |x| ^ q) :=
    (Real.continuous_rpow_const hq.le).comp continuous_abs
  have hOpen : ∀ G, IsOpen G → (P.map Y) G ≤
      atTop.liminf (fun N => ((μ N).map (X N)) G) := by
    intro G hG
    exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto hX.tendsto hG
  have hport := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    hqCont (fun x => Real.rpow_nonneg (abs_nonneg x) _) hOpen
  have hmapY : ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ q) ∂P.map Y =
      ∫⁻ ω, ENNReal.ofReal (|Y ω| ^ q) ∂P :=
    lintegral_map' (by fun_prop) hX.aemeasurable_limit
  have hmapN : ∀ᶠ N in atTop,
      ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ q) ∂(μ N).map (X N) =
        ENNReal.ofReal (∫ ω, |X N ω| ^ q ∂(μ N)) := by
    filter_upwards [hint] with N hN
    rw [lintegral_map' (by fun_prop) (hX.forall_aemeasurable N)]
    rw [← ofReal_integral_eq_lintegral_ofReal hN
      (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)]
  have hpush : ∫⁻ ω, ENNReal.ofReal (|Y ω| ^ q) ∂P ≤ ENNReal.ofReal M := by
    rw [← hmapY]
    calc
      _ ≤ atTop.liminf (fun N => ∫⁻ x : ℝ,
          ENNReal.ofReal (|x| ^ q) ∂(μ N).map (X N)) := hport
      _ = atTop.liminf (fun N => ENNReal.ofReal
          (∫ ω, |X N ω| ^ q ∂(μ N))) := liminf_congr hmapN
      _ ≤ ENNReal.ofReal M := by
        refine liminf_le_of_le (by isBoundedDefault) (fun b hb => ?_)
        obtain ⟨N, hN⟩ :=
          (hb.and (hbound.mono fun N hN => ENNReal.ofReal_le_ofReal hN)).exists
        exact hN.1.trans hN.2
  have hM : 0 ≤ M := by
    obtain ⟨N, hN⟩ := hbound.exists
    exact (integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)).trans hN
  have hYqMeas : AEStronglyMeasurable (fun ω => |Y ω| ^ q) P :=
    hqCont.comp_aestronglyMeasurable hYsm
  have hYqInt : Integrable (fun ω => |Y ω| ^ q) P := by
    refine ⟨hYqMeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω =>
      Real.rpow_nonneg (abs_nonneg _) _)]
    exact lt_of_le_of_lt hpush ENNReal.ofReal_lt_top
  have hboundReal : ∫ ω, |Y ω| ^ q ∂P ≤ M := by
    have h := hpush
    rw [← ofReal_integral_eq_lintegral_ofReal hYqInt
      (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)] at h
    exact (ENNReal.ofReal_le_ofReal_iff hM).mp h
  exact ⟨hYqInt, hboundReal⟩

/-- Convergence in law with a bounded higher moment gives convergence of lower absolute moments. -/
theorem tendsto_integral_abs_rpow_of_tendstoInDistribution {Ω' Ω : Type*}
    [MeasurableSpace Ω'] [MeasurableSpace Ω] {μ : ℕ → Measure Ω'} {P : Measure Ω}
    [∀ N, IsProbabilityMeasure (μ N)] [IsProbabilityMeasure P]
    {X : ℕ → Ω' → ℝ} {Y : Ω → ℝ}
    (hX : TendstoInDistribution X atTop Y μ P) {p q M : ℝ} (hp : 0 < p) (hpq : p < q)
    (hM : ∀ᶠ N in atTop, ∫ ω, |X N ω| ^ q ∂(μ N) ≤ M)
    (hint : ∀ᶠ N in atTop, Integrable (fun ω => |X N ω| ^ q) (μ N)) :
    Tendsto (fun N => ∫ ω, |X N ω| ^ p ∂(μ N)) atTop
      (𝓝 (∫ ω, |Y ω| ^ p ∂P)) := by
  have hXsm (N : ℕ) : AEStronglyMeasurable (X N) (μ N) :=
    (hX.forall_aemeasurable N).aestronglyMeasurable
  have hYsm : AEStronglyMeasurable Y P := hX.aemeasurable_limit.aestronglyMeasurable
  have hqCont : Continuous (fun x : ℝ => |x| ^ q) :=
    (Real.continuous_rpow_const (le_of_lt (lt_trans hp hpq))).comp continuous_abs
  have hOpen : ∀ G, IsOpen G → (P.map Y) G ≤
      atTop.liminf (fun N => ((μ N).map (X N)) G) := by
    intro G hG
    exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto hX.tendsto hG
  have hqMap : ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ q) ∂P.map Y ≤
      atTop.liminf (fun N => ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ q) ∂(μ N).map (X N)) :=
    lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure hqCont
      (fun x => Real.rpow_nonneg (abs_nonneg x) _) hOpen
  have hqXMap : ∀ᶠ N in atTop,
      ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ q) ∂(μ N).map (X N) =
        ENNReal.ofReal (∫ ω, |X N ω| ^ q ∂(μ N)) := by
    filter_upwards [hint] with N hN
    rw [lintegral_map' (by fun_prop) (hX.forall_aemeasurable N)]
    rw [← ofReal_integral_eq_lintegral_ofReal hN
      (Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)]
  have hqYMap :
      ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ q) ∂P.map Y =
        ∫⁻ ω, ENNReal.ofReal (|Y ω| ^ q) ∂P :=
    lintegral_map' (by fun_prop) hX.aemeasurable_limit
  have hqYbound : ∫⁻ ω, ENNReal.ofReal (|Y ω| ^ q) ∂P ≤ ENNReal.ofReal M := by
    rw [← hqYMap]
    calc
      _ ≤ atTop.liminf (fun N => ∫⁻ x : ℝ,
          ENNReal.ofReal (|x| ^ q) ∂(μ N).map (X N)) := hqMap
      _ = atTop.liminf (fun N => ENNReal.ofReal (∫ ω, |X N ω| ^ q ∂(μ N))) := by
        exact liminf_congr hqXMap
      _ ≤ ENNReal.ofReal M := by
        refine liminf_le_of_le (by isBoundedDefault) (fun b hb => ?_)
        obtain ⟨N, hbN⟩ :=
          (hb.and (hM.mono fun N hN => ENNReal.ofReal_le_ofReal hN)).exists
        exact hbN.1.trans hbN.2
  have hYqInt : Integrable (fun ω => |Y ω| ^ q) P := by
    refine ⟨hqCont.comp_aestronglyMeasurable hYsm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω =>
      Real.rpow_nonneg (abs_nonneg _) _)]
    exact lt_of_le_of_lt hqYbound ENNReal.ofReal_lt_top
  have hMnonneg : 0 ≤ M := by
    obtain ⟨N, hMN⟩ := hM.exists
    exact (integral_nonneg_of_ae
      (Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)).trans hMN
  have hYqM : ∫ ω, |Y ω| ^ q ∂P ≤ M := by
    have hlin := hqYbound
    rw [← ofReal_integral_eq_lintegral_ofReal hYqInt
      (Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)] at hlin
    have hreal := ENNReal.toReal_mono (ENNReal.ofReal_ne_top (r := M)) hlin
    simpa only [ENNReal.toReal_ofReal hMnonneg, ENNReal.toReal_ofReal
      (integral_nonneg_of_ae (Eventually.of_forall fun ω =>
        Real.rpow_nonneg (abs_nonneg _) _))] using hreal
  have hmomentCutoff (K : ℝ) (hK : 1 ≤ K) :
      Tendsto (fun N => ∫ ω, momentCutoff p K hp (by linarith) (X N ω) ∂(μ N)) atTop
        (𝓝 (∫ ω, momentCutoff p K hp (by linarith) (Y ω) ∂P)) := by
    have htest :=
      (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
        hX.forall_aemeasurable hX.aemeasurable_limit).mp hX
    exact htest (momentCutoff p K hp (by linarith))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hpow : Tendsto (fun K : ℝ => K ^ (p - q)) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (sub_pos.mpr hpq)
    have he : p - q = -(q - p) := by ring
    simpa only [he] using h
  have hsmallT : Tendsto (fun K : ℝ => 2 * (M * K ^ (p - q))) atTop (𝓝 0) := by
    simpa [mul_assoc] using (tendsto_const_nhds.mul hpow).const_mul 2
  have hsmall : ∀ᶠ K : ℝ in atTop, 2 * (M * K ^ (p - q)) < ε / 4 :=
    hsmallT.eventually (Iio_mem_nhds (by positivity))
  have hKevent : ∀ᶠ K : ℝ in atTop, 1 ≤ K ∧ 2 * (M * K ^ (p - q)) < ε / 4 :=
    (eventually_ge_atTop (1 : ℝ)).and hsmall
  obtain ⟨K, hK, hKsmall⟩ := hKevent.exists
  have hK0 : 0 ≤ K := by linarith
  have hcutConv := hmomentCutoff K hK
  have hcutNear : ∀ᶠ N : ℕ in atTop,
      |(∫ ω, momentCutoff p K hp hK0 (X N ω) ∂(μ N)) -
        ∫ ω, momentCutoff p K hp hK0 (Y ω) ∂P| < ε / 3 := by
    have h := (Metric.tendsto_nhds.mp hcutConv) (ε / 3) (by positivity)
    simpa only [Real.dist_eq] using h
  filter_upwards [hcutNear, hM, hint] with N hN hMN hIN
  have htailX := integral_rpow_cutoff_error_le (hXsm N) hp hpq hK hIN hMN
  have htailY := integral_rpow_cutoff_error_le hYsm hp hpq hK hYqInt hYqM
  have htailY' :
      |(∫ ω, momentCutoff p K hp hK0 (Y ω) ∂P) - ∫ ω, |Y ω| ^ p ∂P| ≤
        K ^ (p - q) * M := by
    rw [abs_sub_comm]
    exact htailY
  have hsmall' : K ^ (p - q) * M < ε / 4 := by
    nlinarith [hKsmall]
  calc
    |(∫ ω, |X N ω| ^ p ∂(μ N)) - ∫ ω, |Y ω| ^ p ∂P| ≤
        |(∫ ω, |X N ω| ^ p ∂(μ N)) -
          ∫ ω, momentCutoff p K hp hK0 (X N ω) ∂(μ N)| +
        |(∫ ω, momentCutoff p K hp hK0 (X N ω) ∂(μ N)) -
          ∫ ω, |Y ω| ^ p ∂P| := abs_sub_le _ _ _
    _ ≤ K ^ (p - q) * M +
        (|(∫ ω, momentCutoff p K hp hK0 (X N ω) ∂(μ N)) -
          ∫ ω, momentCutoff p K hp hK0 (Y ω) ∂P| + K ^ (p - q) * M) := by
        apply add_le_add htailX
        calc
          |(∫ ω, momentCutoff p K hp hK0 (X N ω) ∂(μ N)) -
              ∫ ω, |Y ω| ^ p ∂P| ≤
              |(∫ ω, momentCutoff p K hp hK0 (X N ω) ∂(μ N)) -
                ∫ ω, momentCutoff p K hp hK0 (Y ω) ∂P| +
              |(∫ ω, momentCutoff p K hp hK0 (Y ω) ∂P) - ∫ ω, |Y ω| ^ p ∂P| :=
            abs_sub_le _ _ _
          _ ≤ _ := add_le_add (le_refl _) htailY'
    _ < ε := by nlinarith [hN, htailX, htailY, hsmall']

private theorem abs_max_zero_le (x : ℝ) : |max x 0| ≤ |x| := by
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx, abs_of_nonneg hx]
  · rw [max_eq_right hx, abs_zero]
    exact abs_nonneg _

private theorem tendsto_integral_positivePart_of_tendstoInDistribution
    {Ω' Ω : Type*} [MeasurableSpace Ω'] [MeasurableSpace Ω]
    {μ : ℕ → Measure Ω'} {P : Measure Ω} [∀ N, IsProbabilityMeasure (μ N)]
    [IsProbabilityMeasure P] {X : ℕ → Ω' → ℝ} {Y : Ω → ℝ}
    (hX : TendstoInDistribution X atTop Y μ P) {q M : ℝ} (hq : 1 < q)
    (hM : ∀ᶠ N in atTop, ∫ ω, |X N ω| ^ q ∂(μ N) ≤ M)
    (hint : ∀ᶠ N in atTop, Integrable (fun ω => |X N ω| ^ q) (μ N)) :
    Tendsto (fun N => ∫ ω, max (X N ω) 0 ∂(μ N)) atTop
      (𝓝 (∫ ω, max (Y ω) 0 ∂P)) := by
  have hXsm (N : ℕ) : AEStronglyMeasurable (X N) (μ N) :=
    (hX.forall_aemeasurable N).aestronglyMeasurable
  have hposDist : TendstoInDistribution (fun N ω => max (X N ω) 0) atTop
      (fun ω => max (Y ω) 0) μ P :=
    hX.continuous_comp (continuous_id.max continuous_const)
  have hposPowInt (N : ℕ) (hIN : Integrable (fun ω => |X N ω| ^ q) (μ N)) :
      Integrable (fun ω => |max (X N ω) 0| ^ q) (μ N) := by
    have hposMeas : AEStronglyMeasurable (fun ω => max (X N ω) 0) (μ N) :=
      (continuous_id.max continuous_const).comp_aestronglyMeasurable (hXsm N)
    have hpowCont : Continuous (fun x : ℝ => |x| ^ q) :=
      (Real.continuous_rpow_const (le_of_lt (lt_trans zero_lt_one hq))).comp continuous_abs
    have hposPowMeas : AEStronglyMeasurable (fun ω => |max (X N ω) 0| ^ q) (μ N) :=
      hpowCont.comp_aestronglyMeasurable hposMeas
    apply hIN.mono' hposPowMeas
    filter_upwards [] with ω
    calc
      ‖|max (X N ω) 0| ^ q‖ = |max (X N ω) 0| ^ q :=
        Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
      _ ≤ |X N ω| ^ q :=
        Real.rpow_le_rpow (abs_nonneg _) (abs_max_zero_le _) (le_of_lt (lt_trans zero_lt_one hq))
  have hposHint : ∀ᶠ N in atTop, Integrable (fun ω => |max (X N ω) 0| ^ q) (μ N) := by
    filter_upwards [hint] with N hIN
    exact hposPowInt N hIN
  have hposBound : ∀ᶠ N in atTop,
      ∫ ω, |max (X N ω) 0| ^ q ∂(μ N) ≤ M := by
    filter_upwards [hM, hint] with N hMN hIN
    calc
      ∫ ω, |max (X N ω) 0| ^ q ∂(μ N) ≤ ∫ ω, |X N ω| ^ q ∂(μ N) :=
        integral_mono (hposPowInt N hIN) hIN (fun ω =>
          Real.rpow_le_rpow (abs_nonneg _) (abs_max_zero_le _) (le_of_lt (lt_trans zero_lt_one hq)) )
      _ ≤ M := hMN
  have hposConv := tendsto_integral_abs_rpow_of_tendstoInDistribution
    hposDist zero_lt_one hq hposBound hposHint
  simpa only [Real.rpow_one, abs_of_nonneg (le_max_right (X _ _) 0),
    abs_of_nonneg (le_max_right (Y _) 0)] using hposConv

/-- Convergence in law with a bounded higher moment gives convergence of signed first moments. -/
theorem tendsto_integral_of_tendstoInDistribution {Ω' Ω : Type*} [MeasurableSpace Ω']
    [MeasurableSpace Ω] {μ : ℕ → Measure Ω'} {P : Measure Ω} [∀ N, IsProbabilityMeasure (μ N)]
    [IsProbabilityMeasure P] {X : ℕ → Ω' → ℝ} {Y : Ω → ℝ}
    (hX : TendstoInDistribution X atTop Y μ P) {q M : ℝ} (hq : 1 < q)
    (hM : ∀ᶠ N in atTop, ∫ ω, |X N ω| ^ q ∂(μ N) ≤ M)
    (hint : ∀ᶠ N in atTop, Integrable (fun ω => |X N ω| ^ q) (μ N)) :
    Tendsto (fun N => ∫ ω, X N ω ∂(μ N)) atTop (𝓝 (∫ ω, Y ω ∂P)) := by
  have hpos := tendsto_integral_positivePart_of_tendstoInDistribution hX hq hM hint
  have hnegDist : TendstoInDistribution (fun N ω => -X N ω) atTop
      (fun ω => -Y ω) μ P := hX.continuous_comp continuous_neg
  have hnegM : ∀ᶠ N in atTop, ∫ ω, |-X N ω| ^ q ∂(μ N) ≤ M := by
    simpa only [abs_neg] using hM
  have hnegInt : ∀ᶠ N in atTop, Integrable (fun ω => |-X N ω| ^ q) (μ N) := by
    simpa only [abs_neg] using hint
  have hneg := tendsto_integral_positivePart_of_tendstoInDistribution hnegDist hq hnegM hnegInt
  have hdiff : Tendsto (fun N =>
      (∫ ω, max (X N ω) 0 ∂(μ N)) - ∫ ω, max (-X N ω) 0 ∂(μ N)) atTop
      (𝓝 ((∫ ω, max (Y ω) 0 ∂P) - ∫ ω, max (-Y ω) 0 ∂P)) := hpos.sub hneg
  have hXsm (N : ℕ) : AEStronglyMeasurable (X N) (μ N) :=
    (hX.forall_aemeasurable N).aestronglyMeasurable
  have hXint : ∀ᶠ N in atTop, Integrable (X N) (μ N) := by
    filter_upwards [hint] with N hN
    have habs : Integrable (fun ω => |X N ω|) (μ N) :=
      by simpa only [Real.rpow_one] using
        integrable_abs_rpow_of_larger (hXsm N) zero_lt_one hq hN
    have hnorm : Integrable (fun ω => ‖X N ω‖) (μ N) := by
      simpa [Real.norm_eq_abs] using habs
    exact (integrable_norm_iff (hXsm N)).mp hnorm
  have hYqInt : Integrable (fun ω => |Y ω| ^ q) P := by
    have hYsm : AEStronglyMeasurable Y P := hX.aemeasurable_limit.aestronglyMeasurable
    have hqCont : Continuous (fun x : ℝ => |x| ^ q) :=
      (Real.continuous_rpow_const (le_of_lt (lt_trans zero_lt_one hq))).comp continuous_abs
    have hOpen : ∀ G, IsOpen G → (P.map Y) G ≤ atTop.liminf (fun N => ((μ N).map (X N)) G) := by
      intro G hG
      exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto hX.tendsto hG
    have hqMap : ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ q) ∂P.map Y ≤
        atTop.liminf (fun N => ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ q) ∂(μ N).map (X N)) :=
      lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure hqCont
        (fun x => Real.rpow_nonneg (abs_nonneg x) _) hOpen
    have hqXMap : ∀ᶠ N in atTop,
        ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ q) ∂(μ N).map (X N) =
          ENNReal.ofReal (∫ ω, |X N ω| ^ q ∂(μ N)) := by
      filter_upwards [hint] with N hN
      rw [lintegral_map' (by fun_prop) (hX.forall_aemeasurable N)]
      rw [← ofReal_integral_eq_lintegral_ofReal hN
        (Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)]
    have hqYMap : ∫⁻ x : ℝ, ENNReal.ofReal (|x| ^ q) ∂P.map Y =
        ∫⁻ ω, ENNReal.ofReal (|Y ω| ^ q) ∂P :=
      lintegral_map' (by fun_prop) hX.aemeasurable_limit
    have hbound : ∫⁻ ω, ENNReal.ofReal (|Y ω| ^ q) ∂P ≤ ENNReal.ofReal M := by
      rw [← hqYMap]
      calc
        _ ≤ atTop.liminf (fun N => ∫⁻ x : ℝ,
            ENNReal.ofReal (|x| ^ q) ∂(μ N).map (X N)) := hqMap
        _ = atTop.liminf (fun N => ENNReal.ofReal (∫ ω, |X N ω| ^ q ∂(μ N))) := liminf_congr hqXMap
        _ ≤ ENNReal.ofReal M := by
          refine liminf_le_of_le (by isBoundedDefault) (fun b hb => ?_)
          obtain ⟨N, hbN⟩ :=
            (hb.and (hM.mono fun N hN => ENNReal.ofReal_le_ofReal hN)).exists
          exact hbN.1.trans hbN.2
    refine ⟨hqCont.comp_aestronglyMeasurable hYsm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω =>
      Real.rpow_nonneg (abs_nonneg _) _)]
    exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  have hYabsInt : Integrable (fun ω => |Y ω|) P :=
    by simpa only [Real.rpow_one] using
      integrable_abs_rpow_of_larger hX.aemeasurable_limit.aestronglyMeasurable
        zero_lt_one hq hYqInt
  have hYint : Integrable Y P := by
    have hnorm : Integrable (fun ω => ‖Y ω‖) P := by
      simpa [Real.norm_eq_abs] using hYabsInt
    exact (integrable_norm_iff hX.aemeasurable_limit.aestronglyMeasurable).mp hnorm
  have hposInt (N : ℕ) (hN : Integrable (X N) (μ N)) :
      Integrable (fun ω => max (X N ω) 0) (μ N) := by
    have hnorm : Integrable (fun ω => ‖max (X N ω) 0‖) (μ N) := by
      apply hN.norm.mono' (((continuous_id.max continuous_const).comp_aestronglyMeasurable (hXsm N)).norm)
      filter_upwards [] with ω
      simpa [Real.norm_eq_abs] using abs_max_zero_le (X N ω)
    exact (integrable_norm_iff ((continuous_id.max continuous_const).comp_aestronglyMeasurable (hXsm N))).mp hnorm
  have hnegInt' (N : ℕ) (hN : Integrable (X N) (μ N)) :
      Integrable (fun ω => max (-X N ω) 0) (μ N) := by
    have hnegI : Integrable (fun ω => -X N ω) (μ N) := hN.neg
    have hnorm : Integrable (fun ω => ‖max (-X N ω) 0‖) (μ N) := by
      apply hnegI.norm.mono' (((continuous_id.max continuous_const).comp_aestronglyMeasurable
        ((continuous_neg).comp_aestronglyMeasurable (hXsm N))).norm)
      filter_upwards [] with ω
      simpa [Real.norm_eq_abs] using abs_max_zero_le (-X N ω)
    exact (integrable_norm_iff ((continuous_id.max continuous_const).comp_aestronglyMeasurable
      ((continuous_neg).comp_aestronglyMeasurable (hXsm N)))).mp hnorm
  have hYposInt : Integrable (fun ω => max (Y ω) 0) P := by
    have hnorm : Integrable (fun ω => ‖max (Y ω) 0‖) P := by
      apply hYint.norm.mono' (((continuous_id.max continuous_const).comp_aestronglyMeasurable
        (hX.aemeasurable_limit.aestronglyMeasurable)).norm)
      filter_upwards [] with ω
      simpa [Real.norm_eq_abs] using abs_max_zero_le (Y ω)
    exact (integrable_norm_iff ((continuous_id.max continuous_const).comp_aestronglyMeasurable
      hX.aemeasurable_limit.aestronglyMeasurable)).mp hnorm
  have hYnegInt : Integrable (fun ω => max (-Y ω) 0) P := by
    have hnegYint : Integrable (fun ω => -Y ω) P := hYint.neg
    have hnorm : Integrable (fun ω => ‖max (-Y ω) 0‖) P := by
      apply hnegYint.norm.mono' (((continuous_id.max continuous_const).comp_aestronglyMeasurable
        (continuous_neg.comp_aestronglyMeasurable hX.aemeasurable_limit.aestronglyMeasurable)).norm)
      filter_upwards [] with ω
      simpa [Real.norm_eq_abs] using abs_max_zero_le (-Y ω)
    exact (integrable_norm_iff ((continuous_id.max continuous_const).comp_aestronglyMeasurable
      (continuous_neg.comp_aestronglyMeasurable hX.aemeasurable_limit.aestronglyMeasurable))).mp hnorm
  have hrep (x : ℝ) : max x 0 - max (-x) 0 = x := by
    by_cases hx : 0 ≤ x
    · simp [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
    · have hx' : x ≤ 0 := le_of_not_ge hx
      simp [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx')]
  have htargetEq : (∫ ω, Y ω ∂P) =
      (∫ ω, max (Y ω) 0 ∂P) - ∫ ω, max (-Y ω) 0 ∂P := by
    rw [← integral_sub hYposInt hYnegInt]
    apply integral_congr_ae
    filter_upwards [] with ω
    exact (hrep (Y ω)).symm
  have hsourceEq : ∀ᶠ N in atTop, (∫ ω, X N ω ∂(μ N)) =
      (∫ ω, max (X N ω) 0 ∂(μ N)) - ∫ ω, max (-X N ω) 0 ∂(μ N) := by
    filter_upwards [hXint] with N hN
    rw [← integral_sub (hposInt N hN) (hnegInt' N hN)]
    apply integral_congr_ae
    filter_upwards [] with ω
    exact (hrep (X N ω)).symm
  have hdiff' : Tendsto (fun N =>
      (∫ ω, X N ω ∂(μ N))) atTop (𝓝 ((∫ ω, max (Y ω) 0 ∂P) - ∫ ω, max (-Y ω) 0 ∂P)) := by
    apply hdiff.congr'
    filter_upwards [hsourceEq] with N hN
    exact hN.symm
  rw [htargetEq]
  exact hdiff'

end Critical2DKPZ.JointConvergence

end
