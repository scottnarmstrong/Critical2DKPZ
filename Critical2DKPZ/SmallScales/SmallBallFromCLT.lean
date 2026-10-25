/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Basic.NNReal.Basic

/-! # Bounded-value probabilities under a diverging Gaussian scaling -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open ProbabilityTheory
open scoped Topology

namespace Critical2DKPZ.SmallScales


/-- If `X / a` converges in law to a non-atomic standard Gaussian and `a` tends to infinity,
then the probability that `X` remains in any fixed bounded interval tends to zero. -/
theorem tendsto_measure_abs_le_zero_of_tendstoInDistribution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) (a : ℝ → ℝ)
    (ha : Tendsto a (nhdsWithin 0 (Ioi 0)) atTop)
    (hD : TendstoInDistribution (fun ε ω => X ε ω / a ε)
      (nhdsWithin 0 (Ioi 0)) id (fun _ => P) (gaussianReal 0 1)) (k : ℝ) :
    Tendsto (fun ε => (P {ω | |X ε ω| ≤ k}).toNNReal)
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  let γ : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  let pP : ProbabilityMeasure Ω := ⟨P, inferInstance⟩
  let ν : ℝ → ProbabilityMeasure ℝ := fun ε =>
    pP.map (fun ω => X ε ω / a ε)
  have hweak : Tendsto ν (nhdsWithin 0 (Ioi 0)) (𝓝 γ) := by
    simpa [ν, γ, pP, ProbabilityMeasure.map, Measure.map_id] using hD.tendsto
  have hγnull : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (μ := 0) (v := 1) (by norm_num)
  have hsmallENN : Tendsto (fun δ : ℝ => gaussianReal 0 1 (Icc (-δ) δ))
      (𝓝 0) (𝓝 0) := by
    simpa only [zero_sub, zero_add] using
      (@tendsto_measure_Icc (gaussianReal 0 1) inferInstance hγnull (0 : ℝ))
  have hsmall : Tendsto (fun δ : ℝ => gaussianReal 0 1 (Icc (-δ) δ))
      (𝓝 0) (𝓝 0) := hsmallENN
  have hsmallNN : Tendsto (fun δ : ℝ => (gaussianReal 0 1 (Icc (-δ) δ)).toNNReal)
      (𝓝 0) (𝓝 0) := by
    convert (ENNReal.tendsto_toNNReal (a := 0) (by simp)).comp hsmall using 1 <;> rfl
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb
    exact (not_lt_of_ge bot_le hb).elim
  · intro b hb
    have hδevent : ∀ᶠ δ : ℝ in 𝓝 0,
        (gaussianReal 0 1 (Icc (-δ) δ)).toNNReal < b :=
      hsmallNN.eventually (Iio_mem_nhds hb)
    have hδevent' : ∀ᶠ δ : ℝ in nhdsWithin 0 (Ioi 0),
        (gaussianReal 0 1 (Icc (-δ) δ)).toNNReal < b :=
      hδevent.filter_mono nhdsWithin_le_nhds
    have hδpos : ∀ᶠ δ : ℝ in nhdsWithin 0 (Ioi 0), 0 < δ :=
      eventually_mem_nhdsWithin
    obtain ⟨δ, hδb, hδ⟩ := (hδevent'.and hδpos).exists
    have hfrontierEN : gaussianReal 0 1 (frontier (Icc (-δ) δ)) = 0 := by
      have hfinite : (frontier (Icc (-δ) δ)).Finite := by
        rw [frontier_Icc (by linarith : -δ ≤ δ)]
        simp
      exact @Set.Finite.measure_zero ℝ _ (frontier (Icc (-δ) δ)) hfinite
        (gaussianReal 0 1) hγnull
    have hfrontier : γ (frontier (Icc (-δ) δ)) = 0 := by
      change (gaussianReal 0 1 (frontier (Icc (-δ) δ))).toNNReal = 0
      rw [hfrontierEN]
      rfl
    have hmeasure : Tendsto (fun ε : ℝ => ν ε (Icc (-δ) δ))
        (nhdsWithin 0 (Ioi 0)) (𝓝 (γ (Icc (-δ) δ))) :=
      ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hweak hfrontier
    have hmeasureEvent : ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0),
        ν ε (Icc (-δ) δ) < b := by
      have hδb' : γ (Icc (-δ) δ) < b := by
        change (gaussianReal 0 1 (Icc (-δ) δ)).toNNReal < b
        exact hδb
      exact hmeasure.eventually (Iio_mem_nhds hδb')
    have hscale : ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0), max (k / δ) 1 ≤ a ε := by
      exact ha.eventually (eventually_ge_atTop (max (k / δ) 1))
    filter_upwards [hmeasureEvent, hscale] with ε hμε hscaleε
    have hapos : 0 < a ε := lt_of_lt_of_le zero_lt_one
      (le_trans (le_max_right _ _) hscaleε)
    have hmap : ν ε (Icc (-δ) δ) =
        (P {ω | X ε ω / a ε ∈ Icc (-δ) δ}).toNNReal := by
      exact ProbabilityMeasure.map_apply_of_aemeasurable pP
        (hD.forall_aemeasurable ε) isClosed_Icc.measurableSet
    have hsubset : {ω | |X ε ω| ≤ k} ⊆
        {ω | X ε ω / a ε ∈ Icc (-δ) δ} := by
      intro ω hω
      have hdiv : |X ε ω / a ε| ≤ δ := by
        rw [abs_div, abs_of_pos hapos]
        calc
          |X ε ω| / a ε ≤ k / a ε := div_le_div_of_nonneg_right hω hapos.le
          _ ≤ δ := (div_le_iff₀ hapos).2 (by
            have hmul : k ≤ δ * a ε := by
              have hratio : k / δ ≤ a ε := le_trans (le_max_left _ _) hscaleε
              have hmul' := (div_le_iff₀ hδ).mp hratio
              nlinarith
            nlinarith)
      exact Set.mem_Icc.mpr (abs_le.mp hdiv)
    calc
      (P {ω | |X ε ω| ≤ k}).toNNReal ≤
          (P {ω | X ε ω / a ε ∈ Icc (-δ) δ}).toNNReal :=
        ENNReal.toNNReal_mono (measure_ne_top P _) (measure_mono hsubset)
      _ = ν ε (Icc (-δ) δ) := hmap.symm
      _ < b := hμε

/-- Select positive scales tending to zero so that a sequence of event probabilities has a
geometrically summable bound. -/
theorem exists_sequence_tending_zero_with_summable_event_probabilities
    (p : ℕ → ℝ → NNReal)
    (hp : ∀ k, Tendsto (p k) (nhdsWithin 0 (Ioi 0)) (𝓝 0)) :
    ∃ ε : ℕ → ℝ,
      Tendsto ε atTop (nhdsWithin 0 (Ioi 0)) ∧
        ∀ k, 0 < ε k ∧ ε k < 1 / ((k : ℝ) + 1) ∧
          p k (ε k) < (1 / 2 : NNReal) ^ k := by
  have hchoice (k : ℕ) :
      ∃ r : ℝ, 0 < r ∧ r < 1 / ((k : ℝ) + 1) ∧ p k r < (1 / 2 : NNReal) ^ k := by
    have hprob : ∀ᶠ r : ℝ in nhdsWithin 0 (Ioi 0), p k r < (1 / 2 : NNReal) ^ k :=
      (hp k).eventually (Iio_mem_nhds (by positivity))
    have hpos : ∀ᶠ r : ℝ in nhdsWithin 0 (Ioi 0), 0 < r :=
      eventually_mem_nhdsWithin
    have hbound : ∀ᶠ r : ℝ in nhdsWithin 0 (Ioi 0), r < 1 / ((k : ℝ) + 1) := by
      have hbound' : ∀ᶠ r : ℝ in 𝓝 0, r < 1 / ((k : ℝ) + 1) := by
        filter_upwards [Iio_mem_nhds (show 0 < 1 / ((k : ℝ) + 1) by positivity)]
          with r hr
        exact hr
      exact hbound'.filter_mono nhdsWithin_le_nhds
    obtain ⟨r, hr⟩ := ((hprob.and hpos).and hbound).exists
    exact ⟨r, hr.1.2, hr.2, hr.1.1⟩
  let ε : ℕ → ℝ := fun k => Classical.choose (hchoice k)
  have hε (k : ℕ) :
      0 < ε k ∧ ε k < 1 / ((k : ℝ) + 1) ∧ p k (ε k) < (1 / 2 : NNReal) ^ k :=
    Classical.choose_spec (hchoice k)
  have hεzero : Tendsto ε atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro b hb
      filter_upwards [] with k
      exact lt_of_lt_of_le hb (le_of_lt (hε k).1)
    · intro b hb
      have hinv : Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
        have hden : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
          tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
        have h := tendsto_inv_atTop_zero.comp hden
        convert h using 1
        ext k
        simp only [Function.comp_apply, one_div]
      filter_upwards [hinv.eventually (Iio_mem_nhds hb)] with k hk
      exact lt_trans (hε k).2.1 hk
  have hεpos : ∀ᶠ k : ℕ in atTop, ε k ∈ Ioi 0 :=
    Filter.Eventually.of_forall fun k => (hε k).1
  refine ⟨ε, tendsto_nhdsWithin_iff.mpr ⟨hεzero, hεpos⟩, ?_⟩
  exact hε

end Critical2DKPZ.SmallScales

end
