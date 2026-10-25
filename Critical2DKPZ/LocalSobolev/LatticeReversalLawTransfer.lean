/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-! L¹ closeness and a uniform integrable second-moment bound on the first random vector give asymptotically equal bounded continuous expectations. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology BoundedContinuousFunction

namespace Critical2DKPZ.LocalSobolev

/-- Uniform continuity on a compact ball, with a quadratic penalty outside the ball and
a linear penalty when the two arguments are separated. -/
private theorem bddContinuous_sub_le_quadratic_add_norm {k : ℕ}
    (g : (Fin k → ℝ) →ᵇ ℝ) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x y : Fin k → ℝ,
      |g x - g y| ≤ ε + η * ‖x‖ ^ 2 + A * ‖x - y‖ := by
  let M : ℝ := 2 * ‖g‖
  have hM : 0 ≤ M := by positivity
  let R : ℝ := max 1 (M / η) + 1
  have hR : 1 ≤ R := by dsimp [R]; linarith [le_max_left (1 : ℝ) (M / η)]
  have hMR : M ≤ η * R := by
    have hdiv : M / η ≤ R :=
      (le_max_right (1 : ℝ) (M / η)).trans (le_add_of_nonneg_right zero_le_one)
    simpa only [mul_comm] using (div_le_iff₀ hη).mp hdiv
  have huc := (isCompact_closedBall (0 : Fin k → ℝ) (R + 1)).uniformContinuousOn_of_continuous
    g.continuous.continuousOn
  obtain ⟨δ₀, hδ₀, hδg⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  let δ : ℝ := min δ₀ 1
  have hδ : 0 < δ := lt_min hδ₀ zero_lt_one
  refine ⟨M / δ, div_nonneg hM hδ.le, fun x y => ?_⟩
  have hbound : |g x - g y| ≤ M := by
    simpa only [Real.dist_eq] using g.dist_le_two_norm x y
  by_cases hx : ‖x‖ ≤ R
  · by_cases hxy : ‖x - y‖ < δ
    · have hxball : x ∈ Metric.closedBall (0 : Fin k → ℝ) (R + 1) := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using
          hx.trans (le_add_of_nonneg_right zero_le_one)
      have hyball : y ∈ Metric.closedBall (0 : Fin k → ℝ) (R + 1) := by
        rw [Metric.mem_closedBall, dist_zero_right]
        have hnorm : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
          calc
            ‖y‖ = ‖x - (x - y)‖ := by congr 1; abel
            _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le _ _
        have hd1 : δ ≤ 1 := min_le_right _ _
        linarith
      have hg : |g x - g y| < ε := by
        rw [← Real.dist_eq]
        apply hδg x hxball y hyball
        rw [dist_eq_norm]
        exact hxy.trans_le (min_le_left _ _)
      have hq : 0 ≤ η * ‖x‖ ^ 2 := mul_nonneg hη.le (sq_nonneg _)
      have hl : 0 ≤ M / δ * ‖x - y‖ :=
        mul_nonneg (div_nonneg hM hδ.le) (norm_nonneg _)
      linarith only [hg, hq, hl]
    · have hfar : δ ≤ ‖x - y‖ := le_of_not_gt hxy
      have hpenalty : M ≤ M / δ * ‖x - y‖ := by
        calc
          M = M / δ * δ := (div_mul_cancel₀ M hδ.ne').symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hfar (div_nonneg hM hδ.le)
      exact hbound.trans (hpenalty.trans (le_add_of_nonneg_left
        (add_nonneg hε.le (mul_nonneg hη.le (sq_nonneg _)))))
  · have hnorm : 1 ≤ ‖x‖ := hR.trans (le_of_not_ge hx)
    have hsquare : ‖x‖ ≤ ‖x‖ ^ 2 := by nlinarith
    have hpenalty : M ≤ η * ‖x‖ ^ 2 :=
      hMR.trans (mul_le_mul_of_nonneg_left
        ((le_of_not_ge hx).trans hsquare) hη.le)
    have hp : 0 ≤ M / δ * ‖x - y‖ := mul_nonneg (div_nonneg hM hδ.le) (norm_nonneg _)
    linarith

/-- A uniformly bounded, integrable second moment and L1 closeness transfer expectations
of every bounded continuous test. -/
theorem tendsto_integral_bddContinuous_sub_of_L2_tightness
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] (X Y : ℕ → Ω → Fin k → ℝ)
    (hX : ∀ N, AEMeasurable (X N) P) (hY : ∀ N, AEMeasurable (Y N) P)
    (hsecond : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => ‖X N ω‖ ^ 2) P ∧ ∫ ω, ‖X N ω‖ ^ 2 ∂P ≤ C)
    (hclose : Tendsto (fun N : ℕ =>
      eLpNorm (fun ω => ‖X N ω - Y N ω‖) 1 P) atTop (𝓝 0))
    (g : (Fin k → ℝ) →ᵇ ℝ) :
    Tendsto (fun N : ℕ =>
      (∫ ω, g (X N ω) ∂P) - ∫ ω, g (Y N ω) ∂P) atTop (𝓝 0) := by
  have hD (N : ℕ) : AEStronglyMeasurable (fun ω => ‖X N ω - Y N ω‖) P :=
    ((hX N).sub (hY N)).norm.aestronglyMeasurable
  have hDfinite : ∀ᶠ N : ℕ in atTop,
      eLpNorm (fun ω => ‖X N ω - Y N ω‖) 1 P < ⊤ :=
    hclose.eventually (Iio_mem_nhds ENNReal.zero_lt_top)
  have hDint : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => ‖X N ω - Y N ω‖) P := by
    filter_upwards [hDfinite] with N hN
    exact memLp_one_iff_integrable.mp hN
  have hDnorm (N : ℕ) : (∫ ω, ‖X N ω - Y N ω‖ ∂P) =
      (eLpNorm (fun ω => ‖X N ω - Y N ω‖) 1 P).toReal := by
    rw [eLpNorm_one_eq_lintegral_enorm (hD N)]
    simpa only [norm_norm] using integral_norm_eq_lintegral_enorm (hD N)
  have hDzero : Tendsto (fun N : ℕ => ∫ ω, ‖X N ω - Y N ω‖ ∂P) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ← hDnorm, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hclose
  have hgint (F : Ω → Fin k → ℝ) (hF : AEMeasurable F P) :
      Integrable (fun ω => g (F ω)) P :=
    Integrable.of_bound (g.continuous.measurable.comp_aemeasurable hF).aestronglyMeasurable
      ‖g‖ (Filter.Eventually.of_forall fun ω => g.norm_coe_le_norm (F ω))
  obtain ⟨C, hC, hsecond⟩ := hsecond
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η : ℝ := ε / (4 * (C + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηC : η * C ≤ ε / 4 := by
    calc
      η * C ≤ η * (C + 1) := mul_le_mul_of_nonneg_left (by linarith) hη.le
      _ = ε / 4 := by
        have hCp : C + 1 ≠ 0 := ne_of_gt (by linarith)
        dsimp [η]
        field_simp
  obtain ⟨A, _, hbound⟩ := bddContinuous_sub_le_quadratic_add_norm g
    (by linarith : 0 < ε / 4) hη
  have hAzero : Tendsto (fun N : ℕ => A * ∫ ω, ‖X N ω - Y N ω‖ ∂P)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hDzero.const_mul A
  have hAsmall := (tendsto_order.mp hAzero).2 (ε / 4) (by linarith)
  filter_upwards [hsecond, hDint, hAsmall] with N hN hDN hAN
  have hGX := hgint (X N) (hX N)
  have hGY := hgint (Y N) (hY N)
  have hqint := hN.1.const_mul η
  have hlint := hDN.const_mul A
  have hbase : Integrable (fun ω => ε / 4 + η * ‖X N ω‖ ^ 2) P :=
    (integrable_const (ε / 4)).add hqint
  have hb := integral_mono_ae (hGX.sub hGY).abs
    (((integrable_const (ε / 4)).add hqint).add hlint)
    (Filter.Eventually.of_forall fun ω => hbound (X N ω) (Y N ω))
  have hrhs : (∫ ω, ε / 4 + η * ‖X N ω‖ ^ 2 + A * ‖X N ω - Y N ω‖ ∂P) =
      ε / 4 + η * (∫ ω, ‖X N ω‖ ^ 2 ∂P) +
        A * (∫ ω, ‖X N ω - Y N ω‖ ∂P) := by
    rw [integral_add hbase hlint,
      integral_add (integrable_const (ε / 4)) hqint,
      integral_const_mul, integral_const_mul]
    simp
  simp only [Pi.add_apply, Pi.sub_apply] at hb
  rw [hrhs] at hb
  have hquad : η * (∫ ω, ‖X N ω‖ ^ 2 ∂P) ≤ η * C :=
    mul_le_mul_of_nonneg_left hN.2 hη.le
  have hi : |(∫ ω, g (X N ω) ∂P) - ∫ ω, g (Y N ω) ∂P| ≤
      ∫ ω, |g (X N ω) - g (Y N ω)| ∂P := by
    rw [← integral_sub hGX hGY]
    exact abs_integral_le_integral_abs
  have hfinal : |(∫ ω, g (X N ω) ∂P) - ∫ ω, g (Y N ω) ∂P| < ε := by
    linarith only [hi, hb, hquad, hηC, hAN, hε]
  simpa only [Real.dist_eq, sub_zero] using hfinal

end Critical2DKPZ.LocalSobolev

end
