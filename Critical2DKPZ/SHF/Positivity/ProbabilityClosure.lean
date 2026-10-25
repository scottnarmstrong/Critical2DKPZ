/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic

/-! # Positivity and logarithms under convergence in distribution -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace Critical2DKPZ.SHF.Positivity

/-- A bounded continuous regularization of the extended reciprocal on the real line. -/
def inverseRegularization (n : ℕ) (y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((max y (1 / ((n : ℝ) + 1)))⁻¹)

/-- The continuous reciprocal regularizations increase to the extended reciprocal,
including the infinite value at nonpositive inputs. -/
theorem inverseRegularization_tendsto (y : ℝ) :
    Tendsto (fun n : ℕ => inverseRegularization n y) atTop
      (𝓝 ((ENNReal.ofReal y)⁻¹)) := by
  by_cases hy : 0 < y
  · have hε : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hEq : (fun n : ℕ => inverseRegularization n y) =ᶠ[atTop]
        fun _ => (ENNReal.ofReal y)⁻¹ := by
      filter_upwards [hε.eventually (Iio_mem_nhds hy)] with n hn
      change ENNReal.ofReal ((max y (1 / ((n : ℝ) + 1)))⁻¹) =
        (ENNReal.ofReal y)⁻¹
      rw [max_eq_left hn.le]
      exact ENNReal.ofReal_inv_of_pos hy
    exact Tendsto.congr' (hEq.mono fun n hn => hn.symm) tendsto_const_nhds
  · have hy' : y ≤ 0 := le_of_not_gt hy
    have hreal : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
      have h := (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h
    have htop : Tendsto (fun n : ℕ => ENNReal.ofReal ((n : ℝ) + 1)) atTop (𝓝 ∞) :=
      ENNReal.tendsto_ofReal_atTop.comp hreal
    have hEq : (fun n : ℕ => inverseRegularization n y) =ᶠ[atTop]
        fun n => ENNReal.ofReal ((n : ℝ) + 1) := by
      filter_upwards [] with n
      change ENNReal.ofReal ((max y (1 / ((n : ℝ) + 1)) )⁻¹) =
        ENNReal.ofReal ((n : ℝ) + 1)
      rw [max_eq_right (le_trans hy' (by positivity))]
      simp [one_div]
    have h := Tendsto.congr' (hEq.mono fun n hn => hn.symm) htop
    simpa [ENNReal.ofReal_eq_zero.mpr hy'] using h

/-- The regularized reciprocal increases with the cutoff index. -/
theorem inverseRegularization_monotone (y : ℝ) :
    Monotone (fun n : ℕ => inverseRegularization n y) := by
  apply monotone_nat_of_le_succ
  intro n
  have hden : (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 1 := by norm_num
  have heps : (1 : ℝ) / (((n + 1 : ℕ) : ℝ) + 1) ≤
      1 / ((n : ℝ) + 1) := one_div_le_one_div_of_le (by positivity) hden
  have hdenle : max y (1 / (((n + 1 : ℕ) : ℝ) + 1)) ≤
      max y (1 / ((n : ℝ) + 1)) := max_le_max le_rfl heps
  have hpos₀ : 0 < max y (1 / ((n : ℝ) + 1)) :=
    lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hpos₁ : 0 < max y (1 / (((n + 1 : ℕ) : ℝ) + 1)) :=
    lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hinv : (max y (1 / ((n : ℝ) + 1)))⁻¹ ≤
      (max y (1 / (((n + 1 : ℕ) : ℝ) + 1)))⁻¹ :=
    (inv_le_inv₀ hpos₀ hpos₁).2 hdenle
  simpa only [inverseRegularization] using ENNReal.ofReal_le_ofReal hinv

/-- Each bounded reciprocal regularization is bounded above by the extended reciprocal. -/
theorem inverseRegularization_le (n : ℕ) (y : ℝ) :
    inverseRegularization n y ≤ (ENNReal.ofReal y)⁻¹ :=
  (inverseRegularization_monotone y).ge_of_tendsto (inverseRegularization_tendsto y) n

/-- Fatou in law for the extended reciprocal, whose value is infinite on nonpositive inputs. -/
theorem lintegral_inv_le_liminf_of_tendstoInDistribution {Ω' Ω : Type*}
    [MeasurableSpace Ω'] [MeasurableSpace Ω] {μ : ℕ → Measure Ω'} {P : Measure Ω}
    [∀ N, IsProbabilityMeasure (μ N)] [IsProbabilityMeasure P]
    {X : ℕ → Ω' → ℝ} {Y : Ω → ℝ}
    (hX : TendstoInDistribution X atTop Y μ P) :
    ∫⁻ ω, (ENNReal.ofReal (Y ω))⁻¹ ∂P ≤
      liminf (fun N => ∫⁻ ω, (ENNReal.ofReal (X N ω))⁻¹ ∂(μ N)) atTop := by
  let νN : ℕ → ProbabilityMeasure ℝ := fun N => ⟨(μ N).map (X N), inferInstance⟩
  let ν : ProbabilityMeasure ℝ := ⟨P.map Y, inferInstance⟩
  have hweak : Tendsto νN atTop (𝓝 ν) := by
    simpa only [νN, ν] using hX.tendsto
  have hopen : ∀ G, IsOpen G →
      (ν : Measure ℝ) G ≤ atTop.liminf (fun N => (νN N : Measure ℝ) G) := by
    intro G hG
    exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hG
  let r : ℕ → ℝ → ℝ := fun n y => (max y (1 / ((n : ℝ) + 1)))⁻¹
  have hrcont (n : ℕ) : Continuous (r n) := by
    apply (continuous_id.max continuous_const).inv₀
    intro y
    exact ne_of_gt (lt_of_lt_of_le (by positivity) (le_max_right _ _))
  have hrnonneg (n : ℕ) (y : ℝ) : 0 ≤ r n y :=
    inv_nonneg.mpr (le_of_lt (lt_of_lt_of_le (by positivity) (le_max_right _ _)))
  have hport (n : ℕ) :
      ∫⁻ y, ENNReal.ofReal (r n y) ∂(ν : Measure ℝ) ≤
        liminf (fun N => ∫⁻ y, ENNReal.ofReal (r n y) ∂(νN N : Measure ℝ)) atTop :=
    lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
      (hrcont n) (hrnonneg n) hopen
  have hregmeas (n : ℕ) : Measurable (inverseRegularization n) := by
    exact ENNReal.measurable_ofReal.comp (hrcont n).measurable
  have hmapLim (n : ℕ) :
      ∫⁻ y, inverseRegularization n y ∂(ν : Measure ℝ) =
        ∫⁻ ω, inverseRegularization n (Y ω) ∂P :=
    lintegral_map' (hregmeas n).aemeasurable hX.aemeasurable_limit
  have hmapSeq (N n : ℕ) :
      ∫⁻ y, inverseRegularization n y ∂(νN N : Measure ℝ) =
        ∫⁻ ω, inverseRegularization n (X N ω) ∂(μ N) :=
    lintegral_map' (hregmeas n).aemeasurable (hX.forall_aemeasurable N)
  have hportSource (n : ℕ) :
      ∫⁻ ω, inverseRegularization n (Y ω) ∂P ≤
        liminf (fun N => ∫⁻ ω, inverseRegularization n (X N ω) ∂(μ N)) atTop := by
    calc
      _ = ∫⁻ y, ENNReal.ofReal (r n y) ∂(ν : Measure ℝ) := (hmapLim n).symm
      _ ≤ liminf (fun N => ∫⁻ y, ENNReal.ofReal (r n y)
          ∂(νN N : Measure ℝ)) atTop := hport n
      _ = liminf (fun N => ∫⁻ ω, inverseRegularization n (X N ω) ∂(μ N)) atTop := by
        congr 1
        funext N
        exact hmapSeq N n
  have hregLe (N n : ℕ) :
      ∫⁻ ω, inverseRegularization n (X N ω) ∂(μ N) ≤
        ∫⁻ ω, (ENNReal.ofReal (X N ω))⁻¹ ∂(μ N) :=
    lintegral_mono (fun ω => inverseRegularization_le n (X N ω))
  have htargetBound (n : ℕ) :
      ∫⁻ ω, inverseRegularization n (Y ω) ∂P ≤
        liminf (fun N => ∫⁻ ω, (ENNReal.ofReal (X N ω))⁻¹ ∂(μ N)) atTop := by
    have hsourceBound : Filter.IsBoundedUnder (· ≥ ·) atTop
        (fun N => ∫⁻ ω, inverseRegularization n (X N ω) ∂(μ N)) :=
      Filter.isBoundedUnder_of ⟨0, fun _ => bot_le⟩
    have htargetCobounded : Filter.IsCoboundedUnder (· ≥ ·) atTop
        (fun N => ∫⁻ ω, (ENNReal.ofReal (X N ω))⁻¹ ∂(μ N)) := by
      refine ⟨∞, ?_⟩
      intro a ha
      exact le_top
    exact hportSource n |>.trans (Filter.liminf_le_liminf
      (Filter.Eventually.of_forall (hregLe · n)) hsourceBound htargetCobounded)
  have hregAEMeas (n : ℕ) : AEMeasurable (fun ω => inverseRegularization n (Y ω)) P :=
    (hregmeas n).comp_aemeasurable hX.aemeasurable_limit
  have hregMonotone : ∀ᵐ ω ∂P, Monotone (fun n => inverseRegularization n (Y ω)) :=
    Filter.Eventually.of_forall fun ω => inverseRegularization_monotone (Y ω)
  have hregTendsto : ∀ᵐ ω ∂P,
      Tendsto (fun n => inverseRegularization n (Y ω)) atTop
        (𝓝 ((ENNReal.ofReal (Y ω))⁻¹)) :=
    Filter.Eventually.of_forall fun ω => inverseRegularization_tendsto (Y ω)
  have hlimit := lintegral_tendsto_of_tendsto_of_monotone
    hregAEMeas hregMonotone hregTendsto
  exact le_of_tendsto' hlimit htargetBound

/-- A bounded change of a test function on a measurable exceptional set changes its probability
integral by at most its uniform size times the measure of that set. -/
theorem abs_integral_sub_le_of_agree_off {μ : Measure ℝ} [IsProbabilityMeasure μ] {f g : ℝ → ℝ}
    {s : Set ℝ} (hs : MeasurableSet s) (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : ∀ y ∉ s, f y = g y) {C : ℝ} (hC : ∀ y ∈ s, |f y - g y| ≤ C) :
    |(∫ y, f y ∂μ) - (∫ y, g y ∂μ)| ≤ C * μ.real s := by
  have hsub : Integrable (fun y => f y - g y) μ := hf.sub hg
  have hcompl : ∫ y in sᶜ, (f y - g y) ∂μ = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun y hy => by simp [hfg y hy]
  have hsplit : ∫ y, (f y - g y) ∂μ = ∫ y in s, (f y - g y) ∂μ := by
    rw [← integral_add_compl hs hsub, hcompl, add_zero]
  have hbound : ∀ y ∈ s, ‖f y - g y‖ ≤ C := by
    intro y hy
    simpa only [Real.norm_eq_abs] using hC y hy
  calc
    |(∫ y, f y ∂μ) - (∫ y, g y ∂μ)| = ‖∫ y, (f y - g y) ∂μ‖ := by
      rw [← integral_sub hf hg]
      simp only [Real.norm_eq_abs]
    _ = ‖∫ y in s, (f y - g y) ∂μ‖ := congrArg norm hsplit
    _ ≤ C * μ.real s := norm_setIntegral_le_of_norm_le_const (measure_lt_top μ s) hbound

/-- The mass of shrinking closed intervals around zero tends to the mass at zero. -/
theorem measure_closedBalls_zero_tendsto {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} (hYm : AEMeasurable Y P)
    (hY : ∀ᵐ ω ∂P, Y ω ≠ 0) :
    Tendsto (fun n : ℕ => (P.map Y) (Metric.closedBall (0 : ℝ) (1 / ((n : ℝ) + 1))))
      atTop (𝓝 0) := by
  let ν : ProbabilityMeasure ℝ := ⟨P.map Y, inferInstance⟩
  let s : ℕ → Set ℝ := fun n => Metric.closedBall (0 : ℝ) (1 / ((n : ℝ) + 1))
  have hs_meas : ∀ n, MeasurableSet (s n) := fun n => Metric.isClosed_closedBall.measurableSet
  have hs_mono : Antitone s := by
    intro n m hnm
    apply Metric.closedBall_subset_closedBall
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hnm 1
  have hfin : ∃ n, (ν : Measure ℝ) (s n) ≠ ∞ := ⟨0, measure_ne_top _ _⟩
  have hlim := tendsto_measure_iInter_atTop
    (fun n => (hs_meas n).nullMeasurableSet) hs_mono hfin
  have hinter : (⋂ n, s n) = ({0} : Set ℝ) := by
    ext y
    simp only [Set.mem_iInter, Set.mem_singleton_iff]
    constructor
    · intro hy
      by_contra hy0
      have hypos : 0 < |y| := abs_pos.mpr hy0
      have hseq : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hev := hseq.eventually (Iio_mem_nhds hypos)
      obtain ⟨n, hn⟩ := eventually_atTop.mp hev
      have hsmall : (1 : ℝ) / ((n : ℝ) + 1) < |y| := hn n le_rfl
      have hlarge : |y| ≤ (1 : ℝ) / ((n : ℝ) + 1) := by
        simpa [s, Real.dist_eq] using hy n
      exact (not_lt_of_ge hlarge) hsmall
    · intro hy
      subst y
      intro n
      have hr : 0 ≤ (1 : ℝ) / ((n : ℝ) + 1) := by positivity
      simpa [s, Metric.mem_closedBall] using hr
  have hzero : (ν : Measure ℝ) {0} = 0 := by
    have hpre : P {ω | Y ω = 0} = 0 := by
      rw [ae_iff] at hY
      simpa only [not_ne_iff] using hY
    change (P.map Y) {0} = 0
    rw [Measure.map_apply_of_aemeasurable hYm (measurableSet_singleton (0 : ℝ))]
    simpa only [Set.preimage, Set.mem_singleton_iff] using hpre
  have hlimzero : Tendsto (fun n : ℕ => (ν : Measure ℝ) (s n)) atTop (𝓝 0) := by
    rw [← hzero, ← hinter]
    exact hlim
  simpa [ν, s] using hlimzero

/-- If the limiting law has no atom at zero, applying `log |x|` preserves convergence in distribution; the assigned value at zero is immaterial. -/
theorem tendstoInDistribution_log_of_ne_zero {Ω' Ω : Type*} [MeasurableSpace Ω']
    [MeasurableSpace Ω] {μ : ℕ → Measure Ω'} {P : Measure Ω}
    [∀ N, IsProbabilityMeasure (μ N)] [IsProbabilityMeasure P]
    {X : ℕ → Ω' → ℝ} {Y : Ω → ℝ}
    (hX : TendstoInDistribution X atTop Y μ P) (hY : ∀ᵐ ω ∂P, Y ω ≠ 0) :
    TendstoInDistribution (fun N ω => Real.log (X N ω)) atTop (fun ω => Real.log (Y ω)) μ P := by
  have hlogX : ∀ N, AEMeasurable (fun ω => Real.log (X N ω)) (μ N) :=
    fun N => Real.measurable_log.comp_aemeasurable (hX.forall_aemeasurable N)
  have hlogY : AEMeasurable (fun ω => Real.log (Y ω)) P :=
    Real.measurable_log.comp_aemeasurable hX.aemeasurable_limit
  apply (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hlogX hlogY).2
  intro F
  let νN : ℕ → ProbabilityMeasure ℝ := fun N => ⟨(μ N).map (X N), inferInstance⟩
  let ν : ProbabilityMeasure ℝ := ⟨P.map Y, inferInstance⟩
  have hweak : Tendsto νN atTop (𝓝 ν) := by
    simpa only [νN, ν] using hX.tendsto
  let f : ℝ → ℝ := fun y => F (Real.log y)
  have hfmeas : Measurable f := F.continuous.measurable.comp Real.measurable_log
  have hfintN (N : ℕ) : Integrable f (νN N : Measure ℝ) := by
    apply Integrable.of_bound hfmeas.aestronglyMeasurable ‖F‖
    exact Filter.Eventually.of_forall fun y => F.norm_coe_le_norm (Real.log y)
  have hfint : Integrable f (ν : Measure ℝ) := by
    apply Integrable.of_bound hfmeas.aestronglyMeasurable ‖F‖
    exact Filter.Eventually.of_forall fun y => F.norm_coe_le_norm (Real.log y)
  refine Metric.tendsto_nhds.2 ?_
  intro η hη
  let d : ℝ := η / (16 * (‖F‖ + 1))
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hballs := measure_closedBalls_zero_tendsto hX.aemeasurable_limit hY
  have hevBall := hballs.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hd))
  obtain ⟨n, hn⟩ := eventually_atTop.mp hevBall
  let ε : ℝ := 1 / ((n : ℝ) + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  let s : Set ℝ := Metric.closedBall (0 : ℝ) ε
  have hs : MeasurableSet s := Metric.isClosed_closedBall.measurableSet
  have hqSmall : (ν : Measure ℝ) s < ENNReal.ofReal d := by
    simpa [ν, s, ε] using hn n le_rfl
  let r : ℝ → ℝ := fun y => Real.log (max |y| ε)
  have hrcont : Continuous r := by
    apply continuous_iff_continuousAt.mpr
    intro y
    change ContinuousAt (fun z : ℝ => Real.log (max |z| ε)) y
    have hpos : 0 < max |y| ε := lt_of_lt_of_le hε (le_max_right _ _)
    have hlogAt : ContinuousAt Real.log (max |y| ε) :=
      Real.continuousAt_log (ne_of_gt hpos)
    have hcAt : ContinuousAt (fun z : ℝ => max |z| ε) y :=
      (continuous_abs.max continuous_const).continuousAt
    exact ContinuousAt.comp (f := fun z : ℝ => max |z| ε) (x := y) (g := Real.log)
      hlogAt hcAt
  let g : ℝ → ℝ := fun y => F (r y)
  have hgmeas : Measurable g := F.continuous.measurable.comp hrcont.measurable
  have hagree : ∀ y ∉ s, f y = g y := by
    intro y hy
    have hdist : ε < dist y 0 := lt_of_not_ge (by simpa [s, Metric.mem_closedBall] using hy)
    have habs : ε < |y| := by simpa [Real.dist_eq] using hdist
    dsimp [f, g, r]
    rw [max_eq_left habs.le, Real.log_abs]
  have hbound : ∀ y ∈ s, |f y - g y| ≤ 2 * ‖F‖ := by
    intro y hy
    dsimp [f, g, r]
    calc
      |F (Real.log y) - F (Real.log (max |y| ε))| ≤
          |F (Real.log y)| + |F (Real.log (max |y| ε))| := abs_sub _ _
      _ ≤ ‖F‖ + ‖F‖ := add_le_add (F.norm_coe_le_norm _) (F.norm_coe_le_norm _)
      _ = 2 * ‖F‖ := by ring
  have hgintN (N : ℕ) : Integrable g (νN N : Measure ℝ) := by
    apply Integrable.of_bound hgmeas.aestronglyMeasurable ‖F‖
    exact Filter.Eventually.of_forall fun y => F.norm_coe_le_norm (r y)
  have hgint : Integrable g (ν : Measure ℝ) := by
    apply Integrable.of_bound hgmeas.aestronglyMeasurable ‖F‖
    exact Filter.Eventually.of_forall fun y => F.norm_coe_le_norm (r y)
  have hsourceRegIntN (N : ℕ) : Integrable (fun ω => F (r (X N ω))) (μ N) := by
    apply Integrable.of_bound (hgmeas.comp_aemeasurable (hX.forall_aemeasurable N)).aestronglyMeasurable
      ‖F‖
    exact Filter.Eventually.of_forall fun ω => F.norm_coe_le_norm (r (X N ω))
  have hsourceRegInt : Integrable (fun ω => F (r (Y ω))) P := by
    apply Integrable.of_bound (hgmeas.comp_aemeasurable hX.aemeasurable_limit).aestronglyMeasurable
      ‖F‖
    exact Filter.Eventually.of_forall fun ω => F.norm_coe_le_norm (r (Y ω))
  have hregDist : TendstoInDistribution (fun N => r ∘ X N) atTop (r ∘ Y) μ P :=
    hX.continuous_comp hrcont
  have hregTest : Tendsto (fun N => ∫ ω, F (r (X N ω)) ∂(μ N)) atTop
      (𝓝 (∫ ω, F (r (Y ω)) ∂P)) := by
    have h := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
      hregDist.forall_aemeasurable hregDist.aemeasurable_limit).1 hregDist F
    simpa only [Function.comp_def] using h
  let q : ℝ≥0∞ := (ν : Measure ℝ) s
  let qN : ℕ → ℝ≥0∞ := fun N => (νN N : Measure ℝ) s
  have hport : atTop.limsup qN ≤ q := by
    simpa only [qN, q] using
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hweak (Metric.isClosed_closedBall)
  have hroom : q < q + ENNReal.ofReal d :=
    ENNReal.lt_add_right (measure_ne_top _ _) (ne_of_gt (ENNReal.ofReal_pos.mpr hd))
  have hqEvent : ∀ᶠ N : ℕ in atTop, qN N < q + ENNReal.ofReal d :=
    eventually_lt_of_limsup_lt (hport.trans_lt hroom)
  have hqReal : q.toReal < d := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2 hqSmall
    simpa [ENNReal.toReal_ofReal hd.le] using h
  have hqNReal : ∀ᶠ N : ℕ in atTop, (qN N).toReal < q.toReal + d := by
    filter_upwards [hqEvent] with N hN
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top _ _)
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩)).2 hN
    rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hd.le] at h
    simpa only [qN] using h
  have hqNsmall : ∀ᶠ N : ℕ in atTop, (qN N).toReal < 2 * d := by
    filter_upwards [hqNReal] with N hN
    linarith
  have herrorN (N : ℕ) :
      |(∫ ω, F (Real.log (X N ω)) ∂(μ N)) - (∫ ω, F (r (X N ω)) ∂(μ N))| ≤
        2 * ‖F‖ * (qN N).toReal := by
    have hmapf : ∫ y, f y ∂(νN N : Measure ℝ) =
        ∫ ω, F (Real.log (X N ω)) ∂(μ N) :=
      integral_map (hX.forall_aemeasurable N) hfmeas.aestronglyMeasurable
    have hmapg : ∫ y, g y ∂(νN N : Measure ℝ) =
        ∫ ω, F (r (X N ω)) ∂(μ N) :=
      integral_map (hX.forall_aemeasurable N) hgmeas.aestronglyMeasurable
    rw [← hmapf, ← hmapg]
    simpa [qN, Measure.real] using
      (abs_integral_sub_le_of_agree_off hs (hfintN N) (hgintN N) hagree hbound)
  have herror :
      |(∫ ω, F (Real.log (Y ω)) ∂P) - (∫ ω, F (r (Y ω)) ∂P)| ≤ 2 * ‖F‖ * q.toReal := by
    have hmapf : ∫ y, f y ∂(ν : Measure ℝ) = ∫ ω, F (Real.log (Y ω)) ∂P :=
      integral_map hX.aemeasurable_limit hfmeas.aestronglyMeasurable
    have hmapg : ∫ y, g y ∂(ν : Measure ℝ) = ∫ ω, F (r (Y ω)) ∂P :=
      integral_map hX.aemeasurable_limit hgmeas.aestronglyMeasurable
    rw [← hmapf, ← hmapg]
    simpa [q, Measure.real] using
      (abs_integral_sub_le_of_agree_off hs hfint hgint hagree hbound)
  have hcombined : 6 * ‖F‖ * d < η / 2 := by
    dsimp [d]
    have hF : 0 ≤ ‖F‖ := norm_nonneg _
    field_simp
    nlinarith
  have hregEvent := hregTest.eventually (Metric.ball_mem_nhds _ (by positivity : 0 < η / 2))
  filter_upwards [hregEvent, hqNsmall] with N hreg hqsmall
  have hreg' :
      |(∫ ω, F (r (X N ω)) ∂(μ N)) - (∫ ω, F (r (Y ω)) ∂P)| < η / 2 := by
    simpa [Real.dist_eq] using hreg
  have herrorN' :
      |(∫ ω, F (Real.log (X N ω)) ∂(μ N)) - (∫ ω, F (r (X N ω)) ∂(μ N))| ≤
        4 * ‖F‖ * d := by
    calc
      _ ≤ 2 * ‖F‖ * (qN N).toReal := herrorN N
      _ ≤ 2 * ‖F‖ * (2 * d) := mul_le_mul_of_nonneg_left hqsmall.le (by positivity)
      _ = 4 * ‖F‖ * d := by ring
  have herror' :
      |(∫ ω, F (Real.log (Y ω)) ∂P) - (∫ ω, F (r (Y ω)) ∂P)| ≤
        2 * ‖F‖ * d := by
    calc
      _ ≤ 2 * ‖F‖ * q.toReal := herror
      _ ≤ 2 * ‖F‖ * d := mul_le_mul_of_nonneg_left hqReal.le (by positivity)
  let a : ℝ := ∫ ω, F (Real.log (X N ω)) ∂(μ N)
  let b : ℝ := ∫ ω, F (r (X N ω)) ∂(μ N)
  let c : ℝ := ∫ ω, F (r (Y ω)) ∂P
  let e : ℝ := ∫ ω, F (Real.log (Y ω)) ∂P
  have hlast : |c - e| ≤ 2 * ‖F‖ * d := by
    simpa only [c, e, abs_sub_comm] using herror'
  have hfirst : |a - b| ≤ 4 * ‖F‖ * d := by
    simpa only [a, b] using herrorN'
  have hmiddle : |b - c| ≤ η / 2 := hreg'.le
  have hsum : |a - b| + (|b - c| + |c - e|) ≤
      4 * ‖F‖ * d + η / 2 + 2 * ‖F‖ * d := by
    calc
      _ ≤ 4 * ‖F‖ * d + (η / 2 + 2 * ‖F‖ * d) :=
        add_le_add hfirst (add_le_add hmiddle hlast)
      _ = 4 * ‖F‖ * d + η / 2 + 2 * ‖F‖ * d := by ring
  have hfinal :
      |a - e| < η := by
    calc
      |a - e| ≤ |a - b| + |b - e| := abs_sub_le _ _ _
      _ ≤ |a - b| + (|b - c| + |c - e|) :=
        add_le_add le_rfl (abs_sub_le _ _ _)
      _ ≤ 4 * ‖F‖ * d + η / 2 + 2 * ‖F‖ * d := hsum
      _ < η := by linarith [hcombined]
  simpa [a, e, Real.dist_eq] using hfinal

/-- A finite integral of the extended reciprocal forces a real-valued random variable to be
strictly positive almost surely. -/
theorem ae_pos_of_finite_lintegral_inverse {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Y : Ω → ℝ} (hY : AEMeasurable Y P)
    (hfinite : ∫⁻ ω, (ENNReal.ofReal (Y ω))⁻¹ ∂P < ∞) :
    ∀ᵐ ω ∂P, 0 < Y ω := by
  have hrecipMeas : Measurable (fun y : ℝ => (ENNReal.ofReal y)⁻¹) := by fun_prop
  have hrecipAEMeas : AEMeasurable (fun ω => (ENNReal.ofReal (Y ω))⁻¹) P :=
    hrecipMeas.comp_aemeasurable hY
  have hfiniteAE := MeasureTheory.ae_lt_top' hrecipAEMeas (ne_of_lt hfinite)
  filter_upwards [hfiniteAE] with ω hω
  by_contra hnot
  have hnonpos : Y ω ≤ 0 := le_of_not_gt hnot
  have hzero : ENNReal.ofReal (Y ω) = 0 := ENNReal.ofReal_eq_zero.mpr hnonpos
  have htop : (ENNReal.ofReal (Y ω))⁻¹ = ∞ := by simp [hzero]
  exact hω.ne htop

end Critical2DKPZ.SHF.Positivity

end
