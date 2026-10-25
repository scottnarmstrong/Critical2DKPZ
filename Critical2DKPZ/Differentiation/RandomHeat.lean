/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Differentiation.Balls
public import Critical2DKPZ.Differentiation.HeatKernel
public import Critical2DKPZ.Analysis.Heat.Basic
public import Critical2DKPZ.RandomMeasure.Random
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Heat averages of random planar measures

This module records the measurable random-measure interface used for heat averages and proves the
deterministic comparison between a normalized ball mass and its Gaussian smoothing.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal MeasureTheory Topology

namespace Critical2DKPZ.Differentiation

/-- A measurable random locally finite measure on the plane. Ball evaluation is required jointly
in the sample and center, which is the measurability needed for the countable density field. -/
structure RandomPlanarMeasure (Ω : Type*) [MeasurableSpace Ω] where
  random : Critical2DKPZ.RandomMeasure.RandomRadonMeasure Ω Plane
  measurable_ball : ∀ r : ℝ,
    Measurable (fun p : Ω × Plane =>
      Critical2DKPZ.RandomMeasure.PositiveRadonMeasure.measure (random.value p.1)
        (Metric.closedBall p.2 r))

/-- The positive Radon measure at each sample, using the canonical random
Radon-measure carrier. -/
def RandomPlanarMeasure.value {Ω : Type*} [MeasurableSpace Ω]
    (ν : RandomPlanarMeasure Ω) : Ω → Critical2DKPZ.RandomMeasure.PlaneRadonMeasure :=
  ν.random.value

/-- Evaluation measurability follows from the canonical vague-Borel random
Radon-measure interface. -/
theorem RandomPlanarMeasure.measurable {Ω : Type*} [MeasurableSpace Ω]
    (ν : RandomPlanarMeasure Ω) : Measurable (fun ω =>
      Critical2DKPZ.RandomMeasure.PositiveRadonMeasure.measure (ν.value ω)) := by
  have hEval : @Measurable Ω Critical2DKPZ.RandomMeasure.PlaneRadonMeasure
      inferInstance (MeasurableSpace.comap Subtype.val inferInstance) ν.value :=
    (Critical2DKPZ.RandomMeasure.measurable_radonMap_iff_evaluation
      ν.random.value).mp ν.random.measurable_value
  change Measurable (fun ω => (ν.value ω : Measure Plane))
  exact hEval.subtype_coe

/-- The underlying planar measure carried by a random positive Radon measure. -/
def RandomPlanarMeasure.measure {Ω : Type*} [MeasurableSpace Ω]
    (ν : RandomPlanarMeasure Ω) (ω : Ω) : Measure Plane :=
  Critical2DKPZ.RandomMeasure.PositiveRadonMeasure.measure (ν.value ω)

/-- A finite random variable that records whether an extended heat density is small. Capping at
one preserves convergence to zero and avoids assigning a metric distance to `∞`. -/
def heatProbabilityValue (a : ℝ≥0∞) : NNReal := ENNReal.toNNReal (a ⊓ (1 : ℝ≥0∞))

/-- Below one, the capped heat value is small exactly when the original extended value is. -/
theorem heatProbabilityValue_lt_iff {a : ℝ≥0∞} {ε : NNReal} (hε : ε < 1) :
    heatProbabilityValue a < ε ↔ a < ε := by
  have hcap : a ⊓ (1 : ℝ≥0∞) ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt inf_le_right (by simp))
  have hεtop : (ε : ℝ≥0∞) ≠ ∞ := by simp
  have hiff : (a ⊓ (1 : ℝ≥0∞)).toNNReal < ε ↔ a ⊓ 1 < (ε : ℝ≥0∞) := by
    simpa using ENNReal.toNNReal_lt_toNNReal hcap hεtop
  change (a ⊓ (1 : ℝ≥0∞)).toNNReal < ε ↔ a < (ε : ℝ≥0∞)
  rw [hiff]
  constructor
  · intro h
    rcases inf_lt_iff.mp h with ha | h1
    · exact ha
    · exact False.elim ((not_lt_of_ge (ENNReal.coe_le_coe.mpr hε.le)) h1)
  · intro ha
    exact lt_of_le_of_lt inf_le_left ha

/-- For each fixed center and heat time, the heat-smoothed density of a measurable random measure
is a measurable extended-valued random variable. -/
theorem measurable_heatSmoothedDensity {Ω : Type*} [MeasurableSpace Ω]
    (ν : RandomPlanarMeasure Ω) (u : ℝ) (x : Plane) :
    Measurable (fun ω => heatSmoothedDensity (ν.measure ω) u x) := by
  have hk : Measurable (fun y : Plane => ENNReal.ofReal (heatKernel u (x - y))) := by
    exact ENNReal.measurable_ofReal.comp
      ((measurable_heatKernel u).comp (measurable_const.sub measurable_id))
  exact (Measure.measurable_lintegral hk).comp ν.measurable

/-- The planar Gaussian is bounded below on the closed ball of radius `r` by its value at the
boundary radius. -/
theorem heatKernel_lower_on_closedBall {r : ℝ} (hr : 0 < r) (x y : Plane)
    (hy : y ∈ Metric.closedBall x r) :
    (2 * Real.pi * r ^ 2)⁻¹ * Real.exp (-(1 / 2 : ℝ)) ≤
      heatKernel (r ^ 2) (x - y) := by
  have hdist : dist x y ≤ r := by
    simpa [dist_comm] using hy
  have hn : ‖x - y‖ ≤ r := by simpa [dist_eq_norm] using hdist
  have hsquare : ‖x - y‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg (x - y)]
  have hden : 0 < 2 * r ^ 2 := by positivity
  have hexp : -(1 / 2 : ℝ) ≤ -‖x - y‖ ^ 2 / (2 * r ^ 2) := by
    rw [le_div_iff₀ hden]
    nlinarith
  rw [heatKernel_eq_exp]
  have harg : -((2 * r ^ 2)⁻¹) * ‖x - y‖ ^ 2 =
      -‖x - y‖ ^ 2 / (2 * r ^ 2) := by ring
  rw [harg]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp)
    (inv_nonneg.mpr (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (sq_nonneg r)))

/-- Integrating the pointwise Gaussian lower bound controls the mass of a closed ball. -/
theorem heatSmoothedDensity_lower_bound_ball (μ : Measure Plane) {r : ℝ} (hr : 0 < r)
    (x : Plane) :
    ENNReal.ofReal ((2 * Real.pi * r ^ 2)⁻¹ * Real.exp (-(1 / 2 : ℝ))) *
        μ (Metric.closedBall x r) ≤ heatSmoothedDensity μ (r ^ 2) x := by
  let B := Metric.closedBall x r
  let c : ℝ≥0∞ := ENNReal.ofReal ((2 * Real.pi * r ^ 2)⁻¹ * Real.exp (-(1 / 2 : ℝ)))
  have hpoint : ∀ y : Plane,
      B.indicator (fun _ : Plane => c) y ≤ ENNReal.ofReal (heatKernel (r ^ 2) (x - y)) := by
    intro y
    by_cases hy : y ∈ B
    · rw [Set.indicator_of_mem hy]
      apply ENNReal.ofReal_le_ofReal
      exact heatKernel_lower_on_closedBall hr x y hy
    · rw [Set.indicator_of_notMem hy]
      exact zero_le
  calc
    c * μ B = ∫⁻ y, B.indicator (fun _ : Plane => c) y ∂μ := by
      rw [lintegral_indicator_const measurableSet_closedBall]
    _ ≤ ∫⁻ y, ENNReal.ofReal (heatKernel (r ^ 2) (x - y)) ∂μ :=
      lintegral_mono hpoint
    _ = heatSmoothedDensity μ (r ^ 2) x := rfl

/-- A normalized ball mass is bounded by a fixed multiple of the Gaussian average at the
corresponding squared radius. -/
theorem closedBallDensity_le_heatSmoothedDensity (μ : Measure Plane) {r : ℝ} (hr : 0 < r)
    (x : Plane) :
    closedBallDensity μ x r ≤ ENNReal.ofReal (2 * Real.exp (1 / 2 : ℝ)) *
      heatSmoothedDensity μ (r ^ 2) x := by
  let A := (volume : Measure Plane) (Metric.closedBall x r)
  let c := ENNReal.ofReal ((2 * Real.pi * r ^ 2)⁻¹ * Real.exp (-(1 / 2 : ℝ)))
  let C := ENNReal.ofReal (2 * Real.exp (1 / 2 : ℝ))
  have hA0 : A ≠ 0 := by
    dsimp [A]
    rw [_root_.EuclideanSpace.volume_closedBall_fin_two]
    positivity
  have hAtop : A ≠ ∞ := by
    dsimp [A]
    rw [_root_.EuclideanSpace.volume_closedBall_fin_two]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  have hconst : c * C * A = 1 := by
    dsimp [c, C, A]
    rw [_root_.EuclideanSpace.volume_closedBall_fin_two]
    rw [← ENNReal.ofReal_pow (p := r) hr.le 2]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * Real.pi * r ^ 2)⁻¹ *
      Real.exp (-(1 / 2 : ℝ)))]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ r ^ 2)]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤
      ((2 * Real.pi * r ^ 2)⁻¹ * Real.exp (-(1 / 2 : ℝ))) *
        (2 * Real.exp (1 / 2 : ℝ)))]
    have hrne : r ≠ 0 := ne_of_gt hr
    have hπne : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    rw [← Real.exp_add]
    norm_num
  have hmass : μ (Metric.closedBall x r) ≤
      C * heatSmoothedDensity μ (r ^ 2) x * A := by
    have hmul' : (c * μ (Metric.closedBall x r)) * (C * A) ≤
        heatSmoothedDensity μ (r ^ 2) x * (C * A) := by
      calc
        (c * μ (Metric.closedBall x r)) * (C * A) =
            (C * A) * (c * μ (Metric.closedBall x r)) := by ac_rfl
        _ ≤ (C * A) * heatSmoothedDensity μ (r ^ 2) x :=
          mul_le_mul_right (heatSmoothedDensity_lower_bound_ball μ hr x) (C * A)
        _ = heatSmoothedDensity μ (r ^ 2) x * (C * A) := by ac_rfl
    calc
      μ (Metric.closedBall x r) = (c * C * A) * μ (Metric.closedBall x r) := by
        rw [hconst]
        simp
      _ = (c * μ (Metric.closedBall x r)) * (C * A) := by ac_rfl
      _ ≤ heatSmoothedDensity μ (r ^ 2) x * (C * A) := hmul'
      _ = C * heatSmoothedDensity μ (r ^ 2) x * A := by ac_rfl
  rw [closedBallDensity]
  change μ (Metric.closedBall x r) / A ≤ C * heatSmoothedDensity μ (r ^ 2) x
  rw [ENNReal.div_le_iff hA0 hAtop]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmass

/-- A subsequence tending to zero forces the lower limit of the full nonnegative sequence to
vanish. -/
theorem liminf_eq_zero_of_strictMono_subseq_tendsto_zero {a : ℕ → ℝ≥0∞}
    {ns : ℕ → ℕ} (hns : StrictMono ns)
    (hsub : Tendsto (fun i => a (ns i)) atTop (𝓝 0)) :
    liminf a atTop = 0 := by
  apply le_antisymm
  · by_contra hne
    have hpos : 0 < liminf a atTop := lt_of_not_ge hne
    obtain ⟨c, hc0, hcl⟩ := exists_between hpos
    have htail : ∀ᶠ n in atTop, c < a n := eventually_lt_of_lt_liminf hcl
    have hsubtail : ∀ᶠ i in atTop, c < a (ns i) := hns.tendsto_atTop.eventually htail
    have hsmall : ∀ᶠ i in atTop, a (ns i) < c := hsub.eventually (Iio_mem_nhds hc0)
    obtain ⟨i, hi⟩ := (hsubtail.and hsmall).exists
    exact (lt_asymm hi.1 hi.2)
  · exact bot_le

/-- At a deterministic point, collapse of the random heat averages in probability implies that
the measurable lower ball density is zero almost surely. -/
theorem ae_lowerClosedBallDensity_eq_zero_of_heat_tendstoInMeasure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : RandomPlanarMeasure Ω) (x : Plane)
    (hheat : TendstoInMeasure P
      (fun u ω => heatProbabilityValue (heatSmoothedDensity (ν.measure ω) u x))
      (𝓝[>] (0 : ℝ)) (fun _ => 0)) :
    ∀ᵐ ω ∂P, lowerClosedBallDensity (ν.measure ω) x = 0 := by
  let radius : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hradius : Tendsto radius atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr
      ⟨tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ), ?_⟩
    filter_upwards with n
    change 0 < 1 / ((n : ℝ) + 1)
    positivity
  have htime : Tendsto (fun n => radius n ^ 2) atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hr0 := hradius.mono_right nhdsWithin_le_nhds
      simpa [radius] using hr0.pow 2
    · filter_upwards with n
      exact pow_pos (by dsimp [radius]; positivity) 2
  have hseq : TendstoInMeasure P
      (fun n ω => heatProbabilityValue
        (heatSmoothedDensity (ν.measure ω) (radius n ^ 2) x)) atTop (fun _ => 0) :=
    hheat.comp htime
  obtain ⟨ns, hns, hae⟩ := hseq.exists_seq_tendsto_ae
  filter_upwards [hae] with ω hω
  have hωHeat : Tendsto
      (fun i => heatSmoothedDensity (ν.measure ω) (radius (ns i) ^ 2) x) atTop (𝓝 0) := by
    apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    obtain ⟨δ, hδ0, hδε⟩ :=
      ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_min hε one_pos)
    have hcap : ∀ᶠ i in atTop,
        heatProbabilityValue (heatSmoothedDensity (ν.measure ω) (radius (ns i) ^ 2) x) < δ :=
      hω.eventually (Iio_mem_nhds (ENNReal.coe_pos.mp hδ0))
    filter_upwards [hcap] with i hi
    have hδ1 : δ < 1 := ENNReal.coe_lt_coe.mp (hδε.trans_le (min_le_right ε 1))
    have hactual := (heatProbabilityValue_lt_iff hδ1).mp hi
    exact hactual.le.trans (le_of_lt (hδε.trans_le (min_le_left ε 1)))
  have hball : Tendsto
      (fun i => closedBallDensity (ν.measure ω) x (radius (ns i))) atTop (𝓝 0) := by
    have hmul : Tendsto
        (fun i => ENNReal.ofReal (2 * Real.exp (1 / 2 : ℝ)) *
          heatSmoothedDensity (ν.measure ω) (radius (ns i) ^ 2) x) atTop (𝓝 0) := by
      apply ENNReal.tendsto_nhds_zero.mpr
      intro ε hε
      obtain ⟨δ, hδpos, hδ⟩ := ENNReal.exists_nnreal_pos_mul_lt
        ENNReal.ofReal_ne_top (ne_of_gt hε)
      have hsmall : ∀ᶠ i in atTop,
          heatSmoothedDensity (ν.measure ω) (radius (ns i) ^ 2) x ≤ δ :=
        ENNReal.tendsto_nhds_zero.mp hωHeat (δ : ℝ≥0∞) (ENNReal.coe_pos.mpr hδpos)
      filter_upwards [hsmall] with i hi
      exact (calc
        ENNReal.ofReal (2 * Real.exp (1 / 2 : ℝ)) *
            heatSmoothedDensity (ν.measure ω) (radius (ns i) ^ 2) x ≤
            ENNReal.ofReal (2 * Real.exp (1 / 2 : ℝ)) * δ :=
          mul_le_mul_right hi _
        _ = δ * ENNReal.ofReal (2 * Real.exp (1 / 2 : ℝ)) := by ac_rfl
        _ < ε := hδ).le
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0)) hmul
    · exact fun _ => zero_le
    · intro i
      exact closedBallDensity_le_heatSmoothedDensity (ν.measure ω)
        (by dsimp [radius]; positivity) x
  change liminf (fun n => closedBallDensity (ν.measure ω) x (radius n)) atTop = 0
  exact liminf_eq_zero_of_strictMono_subseq_tendsto_zero hns hball

/-- The countable lower ball-density field of a random planar measure is jointly measurable. -/
theorem measurable_randomLowerClosedBallDensity {Ω : Type*} [MeasurableSpace Ω]
    (ν : RandomPlanarMeasure Ω) :
    Measurable (fun p : Ω × Plane => lowerClosedBallDensity (ν.measure p.1) p.2) := by
  apply Measurable.liminf
  intro n
  let r : ℝ := 1 / ((n : ℝ) + 1)
  have hnum : Measurable (fun p : Ω × Plane => ν.measure p.1 (Metric.closedBall p.2 r)) :=
    ν.measurable_ball r
  have hden : Measurable (fun p : Ω × Plane =>
      (volume : Measure Plane) (Metric.closedBall p.2 r)) :=
    (measurable_measure_closedBall (volume : Measure Plane) r).comp measurable_snd
  have hratio : Measurable (fun p : Ω × Plane =>
      closedBallDensity (ν.measure p.1) p.2 r) := by
    change Measurable (fun p : Ω × Plane =>
      ν.measure p.1 (Metric.closedBall p.2 r) /
        (volume : Measure Plane) (Metric.closedBall p.2 r))
    exact hnum.div hden
  simpa [r] using hratio

/-- If heat densities collapse in probability at every deterministic point, a random locally
finite planar measure is almost surely singular to Lebesgue measure. -/
theorem ae_randomMeasure_mutuallySingular_volume_of_heat_tendstoInMeasure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : RandomPlanarMeasure Ω)
    (hheat : ∀ x : Plane, TendstoInMeasure P
      (fun u ω => heatProbabilityValue (heatSmoothedDensity (ν.measure ω) u x))
      (𝓝[>] (0 : ℝ)) (fun _ => 0)) :
    ∀ᵐ ω ∂P, Measure.MutuallySingular (ν.measure ω) (volume : Measure Plane) := by
  have hf := measurable_randomLowerClosedBallDensity ν
  have hs : MeasurableSet {p : Ω × Plane |
      lowerClosedBallDensity (ν.measure p.1) p.2 = 0} := by
    exact measurableSet_eq_fun hf measurable_const
  have hxω : ∀ᵐ x ∂(volume : Measure Plane),
      ∀ᵐ ω ∂P, lowerClosedBallDensity (ν.measure ω) x = 0 := by
    filter_upwards with x
    exact ae_lowerClosedBallDensity_eq_zero_of_heat_tendstoInMeasure P ν x (hheat x)
  have hωx : ∀ᵐ ω ∂P,
      ∀ᵐ x ∂(volume : Measure Plane), lowerClosedBallDensity (ν.measure ω) x = 0 :=
    (Measure.ae_ae_comm (μ := P) (ν := (volume : Measure Plane)) hs).2 hxω
  filter_upwards [hωx] with ω hω
  exact (@ae_lowerClosedBallDensity_eq_zero_iff_singular
    (ν.measure ω) (ν.value ω).property).mp hω

/-- Under the mean-measure identity, the random measure is almost surely singular to each fixed finite positive measure. -/
theorem ae_randomMeasure_mutuallySingular_finiteMeasure_of_mean_and_heat_tendstoInMeasure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : RandomPlanarMeasure Ω) (μ : Measure Plane) [IsFiniteMeasure μ]
    (hmean : ∀ s : Set Plane, MeasurableSet s →
      (∫⁻ ω, ν.measure ω s ∂P) = (volume : Measure Plane) s)
    (hheat : ∀ x : Plane, TendstoInMeasure P
      (fun u ω => heatProbabilityValue (heatSmoothedDensity (ν.measure ω) u x))
      (𝓝[>] (0 : ℝ)) (fun _ => 0)) :
    ∀ᵐ ω ∂P, Measure.MutuallySingular μ (ν.measure ω) := by
  have hvol := ae_randomMeasure_mutuallySingular_volume_of_heat_tendstoInMeasure P ν hheat
  have hdecomp : μ.singularPart (volume : Measure Plane) +
      (volume : Measure Plane).withDensity (μ.rnDeriv (volume : Measure Plane)) = μ :=
    Measure.singularPart_add_rnDeriv μ (volume : Measure Plane)
  have hsingPart : μ.singularPart (volume : Measure Plane) ⟂ₘ
      (volume : Measure Plane) :=
    Measure.mutuallySingular_singularPart μ (volume : Measure Plane)
  rcases hsingPart with ⟨s, hs, hμs, hvolNull⟩
  have hmeanNull : (∫⁻ ω, ν.measure ω sᶜ ∂P) = 0 := by
    rw [hmean sᶜ hs.compl, hvolNull]
  have hevalMeas : Measurable (fun ω => ν.measure ω sᶜ) :=
    (Measure.measurable_coe hs.compl).comp ν.measurable
  have hνnull : (fun ω => ν.measure ω sᶜ) =ᵐ[P] 0 := by
    rwa [lintegral_eq_zero_iff hevalMeas] at hmeanNull
  filter_upwards [hvol, hνnull] with ω hωvol hωnull
  have hνsingPart : ν.measure ω ⟂ₘ μ.singularPart (volume : Measure Plane) := by
    have hsμ : μ.singularPart (volume : Measure Plane) ⟂ₘ ν.measure ω :=
      ⟨s, hs, hμs, hωnull⟩
    exact hsμ.symm
  have hνac : ν.measure ω ⟂ₘ
      (volume : Measure Plane).withDensity (μ.rnDeriv (volume : Measure Plane)) :=
    hωvol.mono_ac Measure.AbsolutelyContinuous.rfl
      (withDensity_absolutelyContinuous _ _)
  have hνμ : ν.measure ω ⟂ₘ μ := by
    rw [← hdecomp]
    exact hνsingPart.add_right hνac
  exact hνμ.symm

end Critical2DKPZ.Differentiation

end
