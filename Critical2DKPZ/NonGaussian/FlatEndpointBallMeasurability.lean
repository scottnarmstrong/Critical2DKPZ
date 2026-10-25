/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.RandomMeasure.GeneralBorel
public import Critical2DKPZ.Differentiation.RandomHeat
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Topology.Order.Compact

/-! # Joint ball-mass measurability for planar Radon measures -/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped CompactlySupported ENNReal

namespace Critical2DKPZ.NonGaussian

private theorem exists_nearby_center_contains_compact
    {K : Set Plane} (hK : IsCompact K) {x : Plane} {r : ℝ}
    (hsub : K ⊆ Metric.ball x r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x' ∈ Metric.ball x δ, K ⊆ Metric.ball x' r := by
  by_cases hne : K.Nonempty
  · obtain ⟨y₀, hy₀, hmax⟩ := hK.exists_isMaxOn hne
      (continuous_id.dist continuous_const).continuousOn
    have hyr : dist y₀ x < r := Metric.mem_ball.mp (hsub hy₀)
    let δ : ℝ := r - dist y₀ x
    have hδ : 0 < δ := sub_pos.mpr hyr
    refine ⟨δ, hδ, ?_⟩
    intro x' hx' y hy
    have hx'' : dist x x' < δ := by
      simpa only [dist_comm] using Metric.mem_ball.mp hx'
    have hbound : dist y x ≤ dist y₀ x := hmax hy
    apply Metric.mem_ball.mpr
    calc
      dist y x' ≤ dist y x + dist x x' := dist_triangle _ _ _
      _ ≤ dist y₀ x + dist x x' := by linarith only [hbound]
      _ < dist y₀ x + δ := by linarith only [hx'']
      _ = r := by dsimp [δ]; ring
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x' hx' y hy
    exact (hne ⟨y, hy⟩).elim

private theorem lowerSemicontinuous_vague_openBall_mass_joint (r : ℝ) :
    LowerSemicontinuous (fun q : Critical2DKPZ.RandomMeasure.PositiveRadonMeasure Plane × Plane =>
      q.1.measure (Metric.ball q.2 r)) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro a
  rw [isOpen_iff_mem_nhds]
  intro q hq
  have hrepr := Critical2DKPZ.RandomMeasure.vague_open_mass_eq_iSup_tests
    q.1 (Metric.ball q.2 r) Metric.isOpen_ball
  have hq' : a < ⨆ f : Critical2DKPZ.RandomMeasure.VagueOpenTest
      (Metric.ball q.2 r),
      ∫⁻ y, ENNReal.ofReal (f.1 y) ∂q.1.measure := by
    rw [← hrepr]
    exact hq
  obtain ⟨f, hfa⟩ := lt_iSup_iff.mp hq'
  let I : Critical2DKPZ.RandomMeasure.PositiveRadonMeasure Plane × Plane → ℝ≥0∞ :=
    fun z => ∫⁻ y, ENNReal.ofReal (f.1 y) ∂z.1.measure
  have hIeq (μ : Critical2DKPZ.RandomMeasure.PositiveRadonMeasure Plane) :
      (∫⁻ y, ENNReal.ofReal (f.1 y) ∂μ.measure) =
        ENNReal.ofReal (Critical2DKPZ.RandomMeasure.vaguePairing μ f.1) := by
    exact (ofReal_integral_eq_lintegral_ofReal
      (Critical2DKPZ.RandomMeasure.integrable_vagueTest μ f.1)
      (Filter.Eventually.of_forall fun y => f.2.1 y)).symm
  have hIcont : Continuous I := by
    have heq : I = fun z => ENNReal.ofReal
        (Critical2DKPZ.RandomMeasure.vaguePairing z.1 f.1) := by
      funext z
      exact hIeq z.1
    rw [heq]
    exact ENNReal.continuous_ofReal.comp
      ((Critical2DKPZ.RandomMeasure.continuous_vaguePairing f.1).comp continuous_fst)
  have hIopen : IsOpen {z | a < I z} := isOpen_Ioi.preimage hIcont
  let K : Set Plane := tsupport (f.1 : Plane → ℝ)
  have hK : IsCompact K := by
    dsimp [K]
    exact f.1.hasCompactSupport
  obtain ⟨δ, hδ, hsupport⟩ :=
    exists_nearby_center_contains_compact hK f.property.2.2
  let U := (Set.univ ×ˢ Metric.ball q.2 δ) ∩ {z | a < I z}
  have hU : IsOpen U := (isOpen_univ.prod Metric.isOpen_ball).inter hIopen
  have hqU : q ∈ U := by
    refine ⟨⟨Set.mem_univ _, Metric.mem_ball.mpr ?_⟩, hfa⟩
    simpa only [dist_self] using hδ
  filter_upwards [hU.mem_nhds hqU] with z hz
  rcases hz with ⟨⟨_, hx⟩, hza⟩
  let f' : Critical2DKPZ.RandomMeasure.VagueOpenTest (Metric.ball z.2 r) :=
    ⟨f.1, f.2.1, f.2.2.1, (hsupport z.2 hx)⟩
  have hle : I z ≤ z.1.measure (Metric.ball z.2 r) := by
    rw [Critical2DKPZ.RandomMeasure.vague_open_mass_eq_iSup_tests
      z.1 (Metric.ball z.2 r) Metric.isOpen_ball]
    exact le_iSup_of_le f' le_rfl
  exact hza.trans_le hle

/-- The mass of a closed ball is jointly measurable in its Radon measure and center. -/
theorem measurable_joint_closedBall_mass (r : ℝ) :
    Measurable (fun q : Critical2DKPZ.RandomMeasure.PositiveRadonMeasure Plane × Plane =>
      q.1.measure (Metric.closedBall q.2 r)) := by
  let radius : ℕ → ℝ := fun n => r + 1 / ((n : ℝ) + 1)
  let ballMass : ℕ → Critical2DKPZ.RandomMeasure.PositiveRadonMeasure Plane × Plane → ℝ≥0∞ :=
    fun n q => q.1.measure (Metric.ball q.2 (radius n))
  have hball (n : ℕ) : Measurable (ballMass n) := by
    change Measurable (fun q : Critical2DKPZ.RandomMeasure.PositiveRadonMeasure Plane × Plane =>
      q.1.measure (Metric.ball q.2 (radius n)))
    exact (lowerSemicontinuous_vague_openBall_mass_joint (radius n)).measurable
  have hlim (q : Critical2DKPZ.RandomMeasure.PositiveRadonMeasure Plane × Plane) :
      q.1.measure (Metric.closedBall q.2 r) =
        ⨅ n : ℕ, ballMass n q := by
    classical
    let U : ℕ → Set Plane := fun n => Metric.ball q.2 (radius n)
    have hUmeas (n : ℕ) : MeasurableSet (U n) := Metric.isOpen_ball.measurableSet
    have hUnested : Antitone U := by
      intro m n hmn x hx
      apply Metric.mem_ball.mpr
      have hx' := Metric.mem_ball.mp hx
      have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
      have hfrac : radius n ≤ radius m := by
        dsimp [radius]
        have hden : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := hmn'
        have hinv : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) hden
        linarith only [hinv]
      have hrad : radius n ≤ radius m := hfrac
      exact lt_of_lt_of_le hx' hrad
    have hInter : (⋂ n, U n) = Metric.closedBall q.2 r := by
      ext x
      simp only [U, Metric.mem_ball, Metric.mem_closedBall, Set.mem_iInter]
      constructor
      · intro h
        have hle : dist x q.2 ≤ r := by
          by_contra hn
          have hn' : r < dist x q.2 := lt_of_not_ge hn
          obtain ⟨n, hsmall⟩ := exists_nat_one_div_lt (sub_pos.mpr hn')
          have htest := h n
          linarith only [hn', hsmall, htest]
        exact hle
      · intro hx n
        have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
        have hlt : r < r + 1 / ((n : ℝ) + 1) := by linarith
        exact lt_of_le_of_lt hx hlt
    have hUnull (n : ℕ) : NullMeasurableSet (U n) q.1.measure :=
      (hUmeas n).nullMeasurableSet
    have hfin : ∃ n, q.1.measure (U n) ≠ ∞ := by
      obtain ⟨V, hVsup, _, hVfinite⟩ :=
        (isCompact_closedBall q.2 (r + 1)).exists_open_superset_measure_lt_top'
          (fun x _ => q.1.property.finiteAtNhds x)
      have hsubV : U 0 ⊆ V := by
        intro x hx
        apply hVsup
        apply Metric.mem_closedBall.mpr
        have hx' := Metric.mem_ball.mp hx
        have hrad : radius 0 = r + 1 := by norm_num [radius]
        rw [hrad] at hx'
        exact hx'.le
      refine ⟨0, ?_⟩
      exact ne_of_lt ((measure_mono hsubV).trans_lt hVfinite)
    calc
      q.1.measure (Metric.closedBall q.2 r) = q.1.measure (⋂ n, U n) := by rw [hInter]
      _ = ⨅ n, q.1.measure (U n) := hUnested.measure_iInter hUnull hfin
      _ = ⨅ n, ballMass n q := by
        apply iInf_congr
        intro n
        rfl
  rw [show (fun q : Critical2DKPZ.RandomMeasure.PositiveRadonMeasure Plane × Plane =>
      q.1.measure (Metric.closedBall q.2 r)) = fun q => ⨅ n : ℕ, ballMass n q by
          funext q
          exact hlim q]
  exact Measurable.iInf hball

end Critical2DKPZ.NonGaussian

end
