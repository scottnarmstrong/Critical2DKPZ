/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.JointConvergence.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # Sub-sigma measurable representatives of L2 limits -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Critical2DKPZ.JointConvergence

set_option linter.style.haveILetI false in
/-- A rate-controlled family that is Cauchy in `L²` has a measurable limit with the same rate. -/
theorem exists_L2_limit_of_cauchy {Ω : Type*} [m0 : MeasurableSpace Ω] (m : MeasurableSpace Ω)
    (_hm : m ≤ m0) (P : @Measure Ω m0) [IsProbabilityMeasure P]
    (Y : ℝ → Ω → ℝ) (ε : ℝ → ℝ) (δ₁ : ℝ)
    (hY : ∀ δ ∈ Set.Ioo 0 δ₁, Measurable[m] (Y δ) ∧ MemLp (Y δ) 2 P)
    (hε : Tendsto ε (𝓝[>] 0) (𝓝 0)) (hε0 : ∀ δ ∈ Set.Ioo 0 δ₁, 0 ≤ ε δ)
    (hC : ∀ δ ∈ Set.Ioo 0 δ₁, ∀ δ' ∈ Set.Ioo 0 δ₁,
      @eLpNorm Ω ℝ _ _ m0 (fun ω => Y δ ω - Y δ' ω) 2 P ≤ ENNReal.ofReal (ε δ + ε δ')) :
    ∃ X : Ω → ℝ, Measurable[m] X ∧ ∀ δ ∈ Set.Ioo 0 δ₁,
      @eLpNorm Ω ℝ _ _ m0 (fun ω => Y δ ω - X ω) 2 P ≤ ENNReal.ofReal (ε δ) := by
  classical
  by_cases hδ₁ : 0 < δ₁
  · have hexists (n : ℕ) : ∃ d : ℝ, 0 < d ∧ d < δ₁ ∧ ε d < (1 / 2 : ℝ) ^ (n + 1) := by
      have hsmall : ∀ᶠ d : ℝ in 𝓝[>] 0, ε d < (1 / 2 : ℝ) ^ (n + 1) :=
        hε.eventually (Iio_mem_nhds (by positivity))
      have hbelow : ∀ᶠ d : ℝ in 𝓝[>] 0, d < δ₁ :=
        nhdsWithin_le_nhds (Iio_mem_nhds hδ₁)
      have hpos : ∀ᶠ d : ℝ in 𝓝[>] 0, 0 < d := by
        exact (show Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ) from self_mem_nhdsWithin)
      obtain ⟨d, hdpos, hdsmall, hdlt⟩ :=
        (hpos.and (hsmall.and hbelow)).exists
      exact ⟨d, hdpos, hdlt, hdsmall⟩
    choose d hdpos hdlt hdε using hexists
    have hdInt (n : ℕ) : d n ∈ Set.Ioo 0 δ₁ := ⟨hdpos n, hdlt n⟩
    have hepsNonneg (n : ℕ) : 0 ≤ ε (d n) := hε0 (d n) (hdInt n)
    have hpowT : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 0) := by
      have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) < 1)
      exact hpow.comp (tendsto_add_atTop_nat 1)
    have hepsT : Tendsto (fun n : ℕ => ε (d n)) atTop (𝓝 0) :=
      squeeze_zero hepsNonneg (fun n => (hdε n).le) hpowT
    let f : ℕ → Ω → ℝ := fun n ω => Y (d n) ω
    let B : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ n)
    have hBreal : Summable (fun n : ℕ => 2 * (1 / 2 : ℝ) ^ n) :=
      summable_geometric_two.mul_left 2
    have hBsum : ∑' n, B n = ENNReal.ofReal (∑' n, 2 * (1 / 2 : ℝ) ^ n) := by
      dsimp [B]
      exact (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hBreal).symm
    have hBfinite : ∑' n, B n ≠ ∞ := by
      rw [hBsum]
      exact ENNReal.ofReal_ne_top
    have hCauchy : ∀ N n m : ℕ, N ≤ n → N ≤ m →
        eLpNorm (f n - f m) 2 P < B N := by
      intro N n m hNn hNm
      have hpowN : (1 / 2 : ℝ) ^ (n + 1) ≤ (1 / 2 : ℝ) ^ (N + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have hpowM : (1 / 2 : ℝ) ^ (m + 1) ≤ (1 / 2 : ℝ) ^ (N + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have hsmall : ε (d n) + ε (d m) < 2 * (1 / 2 : ℝ) ^ N := by
        have hn : ε (d n) < (1 / 2 : ℝ) ^ (N + 1) := (hdε n).trans_le hpowN
        have hm : ε (d m) < (1 / 2 : ℝ) ^ (N + 1) := (hdε m).trans_le hpowM
        have hpower : 2 * (1 / 2 : ℝ) ^ (N + 1) = (1 / 2 : ℝ) ^ N := by
          rw [pow_succ]
          ring
        calc
          ε (d n) + ε (d m) < 2 * (1 / 2 : ℝ) ^ (N + 1) := by linarith
          _ = (1 / 2 : ℝ) ^ N := hpower
          _ ≤ 2 * (1 / 2 : ℝ) ^ N := by
            nlinarith [pow_nonneg (show 0 ≤ (1 / 2 : ℝ) by norm_num) N]
      have henn : ENNReal.ofReal (ε (d n) + ε (d m)) < B N := by
        change ENNReal.ofReal (ε (d n) + ε (d m)) <
          ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ N)
        rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
        exact hsmall
      calc
        eLpNorm (f n - f m) 2 P = eLpNorm (fun ω => Y (d n) ω - Y (d m) ω) 2 P := rfl
        _ ≤ ENNReal.ofReal (ε (d n) + ε (d m)) := hC (d n) (hdInt n) (d m) (hdInt m)
        _ < B N := henn
    have hAEexists : ∀ᵐ ω ∂P, ∃ x : ℝ, Tendsto (fun n => f n ω) atTop (𝓝 x) :=
      Lp.ae_tendsto_of_cauchy_eLpNorm
        (fun n => (hY (d n) (hdInt n)).2.aestronglyMeasurable)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hBfinite hCauchy
    have hfStrong (n : ℕ) : StronglyMeasurable[m] (f n) :=
      (hY (d n) (hdInt n)).1.stronglyMeasurable
    let X : Ω → ℝ := fun ω => limUnder atTop (f · ω)
    have hXStrong : StronglyMeasurable[m] X := by
      dsimp [X]
      exact StronglyMeasurable.limUnder hfStrong
    have hXm : Measurable[m] X := hXStrong.measurable
    have hAE : ∀ᵐ ω ∂P, Tendsto (f · ω) atTop (𝓝 (X ω)) := by
      filter_upwards [hAEexists] with ω hω
      obtain ⟨x, hx⟩ := hω
      dsimp [X]
      rw [hx.limUnder_eq]
      exact hx
    letI : MeasurableSpace Ω := m0
    have hXStrong0 : StronglyMeasurable[m0] X := hXStrong.mono _hm
    have hXsm : AEStronglyMeasurable X P := hXStrong0.aestronglyMeasurable
    have hrate (δ : ℝ) (hδ : δ ∈ Set.Ioo 0 δ₁) :
        eLpNorm (fun ω => Y δ ω - X ω) 2 P ≤ ENNReal.ofReal (ε δ) := by
      have hdiffAE : ∀ᵐ ω ∂P,
          Tendsto (fun n => Y δ ω - f n ω) atTop (𝓝 (Y δ ω - X ω)) := by
        filter_upwards [hAE] with ω hω
        exact Tendsto.sub tendsto_const_nhds hω
      have hdiffSM (n : ℕ) : AEStronglyMeasurable (fun ω => Y δ ω - f n ω) P :=
        (hY δ hδ).2.aestronglyMeasurable.sub (hY (d n) (hdInt n)).2.aestronglyMeasurable
      have hdiffLimitSM : AEStronglyMeasurable (fun ω => Y δ ω - X ω) P :=
        (hY δ hδ).2.aestronglyMeasurable.sub hXsm
      have hlower := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2) hdiffSM
        (fun ω => Y δ ω - X ω) hdiffLimitSM hdiffAE
      have hseqBound (n : ℕ) :
          eLpNorm (fun ω => Y δ ω - f n ω) 2 P ≤ ENNReal.ofReal (ε δ + ε (d n)) :=
        hC δ hδ (d n) (hdInt n)
      have hrhsT : Tendsto (fun n : ℕ => ENNReal.ofReal (ε δ + ε (d n))) atTop
          (𝓝 (ENNReal.ofReal (ε δ))) := by
        exact (ENNReal.continuous_ofReal.tendsto (ε δ)).comp
          (by simpa using Tendsto.const_add (ε δ) hepsT)
      calc
        eLpNorm (fun ω => Y δ ω - X ω) 2 P ≤
            atTop.liminf (fun n => eLpNorm (fun ω => Y δ ω - f n ω) 2 P) := hlower
        _ ≤ atTop.liminf (fun n => ENNReal.ofReal (ε δ + ε (d n))) :=
          Filter.liminf_le_liminf (Eventually.of_forall hseqBound)
        _ = ENNReal.ofReal (ε δ) := hrhsT.liminf_eq
    exact ⟨X, hXm, fun δ hδ => hrate δ hδ⟩
  · refine ⟨fun _ => 0, measurable_const, ?_⟩
    intro δ hδ
    exfalso
    exact hδ₁ (hδ.1.trans hδ.2)

end Critical2DKPZ.JointConvergence

end
