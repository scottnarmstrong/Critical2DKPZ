/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonFourthNormModel
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonVarianceScale
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonCellScale
import Mathlib.Tactic

/-! # Vanishing quasi-critical coefficients of the fourth-moment remainder -/

@[expose] public noncomputable section

open Filter Critical2DKPZ.MomentBounds
open scoped Topology

namespace Critical2DKPZ.Extensions.GffTangent

private theorem tendsto_fourth_weight_exp (C : ℝ) {m : ℕ → ℕ} {c : ℝ}
    (hm : Tendsto (fun N : ℕ => (m N : ℝ) / N) atTop (𝓝 c)) :
    Tendsto (fun N => Real.exp (C * fourthWeightScale N ^ 2 * m N))
      atTop (𝓝 (Real.exp (C * (2 * c)))) := by
  have h := (Real.continuous_exp.tendsto (C * (2 * c))).comp
    ((tendsto_fourthWeightScale_sq_mul hm).const_mul C)
  simpa only [mul_assoc, Function.comp_def] using h

/-- The free-operator cost has a finite macroscopic-window limit. -/
theorem tendsto_fourthFreeCost {m : ℕ → ℕ} {c : ℝ}
    (hm : Tendsto (fun N : ℕ => (m N : ℝ) / N) atTop (𝓝 c)) :
    Tendsto (fun N => fourthFreeCost (fourthWeightScale N) (m N)) atTop
      (𝓝 (4 * fourthFreeConstant * Real.exp (fourthFreeConstant * (2 * c)))) :=
  (tendsto_fourth_weight_exp fourthFreeConstant hm).const_mul _

/-- Multiplication by l*sigmaSq makes the interaction cost converge to a
finite value, even though the unscaled resolvent diverges. -/
theorem tendsto_quasiCritical_scaled_fourthInteractionCost (l β : ℕ → ℝ)
    (hl : Tendsto l atTop atTop)
    (hratio : Tendsto (fun N => l N / Real.log (N : ℝ)) atTop (𝓝 0))
    (hβ : ∀ᶠ N : ℕ in atTop, 0 < β N)
    (hσ : ∀ᶠ N : ℕ in atTop, Polymer.sigmaSq (β N) = criticalSigmaSq (-l N) N)
    {m : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hm : Tendsto (fun N : ℕ => (m N : ℝ) / N) atTop (𝓝 c)) :
    Tendsto (fun N => l N * Polymer.sigmaSq (β N) *
      fourthInteractionCost (fourthWeightScale N) (m N) (β N)) atTop
      (𝓝 (fourthInteractionConstant * Real.exp (fourthInteractionConstant * (2 * c)) * Real.pi)) := by
  have he := (tendsto_fourth_weight_exp fourthInteractionConstant hm).const_mul fourthInteractionConstant
  have hg := tendsto_quasiCritical_geometric_prefactor_macroscopic l β hl hratio hβ hσ hc hm
  have ho := tendsto_quasiCritical_sigma_overlap_macroscopic l β hratio hσ hc hm
  have h := (tendsto_quasiCritical_l_sigma_zero l β hratio hσ).add ((he.mul hg).mul ho)
  simp only [zero_add, mul_one] at h
  apply h.congr'
  filter_upwards [] with N
  unfold fourthInteractionCost
  ring

/-- The geometric ratio of the fourth-order run series tends to zero. -/
theorem tendsto_quasiCritical_fourth_run_ratio (l β : ℕ → ℝ)
    (hl : Tendsto l atTop atTop)
    (hratio : Tendsto (fun N => l N / Real.log (N : ℝ)) atTop (𝓝 0))
    (hβ : ∀ᶠ N : ℕ in atTop, 0 < β N)
    (hσ : ∀ᶠ N : ℕ in atTop, Polymer.sigmaSq (β N) = criticalSigmaSq (-l N) N)
    {m : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hm : Tendsto (fun N : ℕ => (m N : ℝ) / N) atTop (𝓝 c)) :
    Tendsto (fun N =>
      (ccr25GaussianFiniteWordOperatorScale 4
        (fourthInteractionCost (fourthWeightScale N) (m N) (β N)) * Polymer.sigmaSq (β N)) *
          fourthFreeCost (fourthWeightScale N) (m N)) atTop (𝓝 0) := by
  let G := (max 1 (ccr25GaussianMomentUniformConstant 4)) ^ 4 * (2 ^ (4 * 4) : ℝ)
  have hu := tendsto_quasiCritical_scaled_fourthInteractionCost l β hl hratio hβ hσ hc hm
  have h := ((hu.div_atTop hl).mul (tendsto_fourthFreeCost hm)).const_mul G
  simp only [zero_mul, mul_zero] at h
  apply h.congr'
  filter_upwards [hl.eventually_gt_atTop 0] with N hlN
  dsimp only [ccr25GaussianFiniteWordOperatorScale, G]
  field_simp [hlN.ne']

/-- The three normalized remainder coefficients after factoring out the
boundary-cost product. The leading disjoint-pair term is kept separate. -/
def fourthRemainderCoefficient (l β : ℝ) (N L : ℕ) : ℝ :=
  let σ := Polymer.sigmaSq β
  let U := fourthInteractionCost (fourthWeightScale N) L β
  let Q := fourthFreeCost (fourthWeightScale N) L
  let A := ccr25GaussianFiniteWordOperatorScale 4 U
  (l * σ * A) * (l * σ) +
    (2 : ℝ) ^ 32 * (max 1 (ccr25GaussianMomentUniformConstant 4)) ^ 8 *
      (l * σ * U) ^ 2 * Real.sqrt σ * Q +
    ((l * σ * A) ^ 3 * Q ^ 2 / l) / (1 - (A * σ) * Q)

/-- All normalized remainder coefficients vanish in the actual moving
quasi-critical regime on every fixed positive macroscopic window. -/
theorem tendsto_fourthRemainderCoefficient_zero (l β : ℕ → ℝ)
    (hl : Tendsto l atTop atTop)
    (hratio : Tendsto (fun N => l N / Real.log (N : ℝ)) atTop (𝓝 0))
    (hβ : ∀ᶠ N : ℕ in atTop, 0 < β N)
    (hσ : ∀ᶠ N : ℕ in atTop, Polymer.sigmaSq (β N) = criticalSigmaSq (-l N) N)
    {m : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hm : Tendsto (fun N : ℕ => (m N : ℝ) / N) atTop (𝓝 c)) :
    Tendsto (fun N => fourthRemainderCoefficient (l N) (β N) N (m N)) atTop (𝓝 0) := by
  let G := (max 1 (ccr25GaussianMomentUniformConstant 4)) ^ 4 * (2 ^ (4 * 4) : ℝ)
  have hu := tendsto_quasiCritical_scaled_fourthInteractionCost l β hl hratio hβ hσ hc hm
  have ha := hu.mul_const G
  have ha' : Tendsto (fun N => l N * Polymer.sigmaSq (β N) *
      ccr25GaussianFiniteWordOperatorScale 4
        (fourthInteractionCost (fourthWeightScale N) (m N) (β N))) atTop
      (𝓝 ((fourthInteractionConstant * Real.exp (fourthInteractionConstant * (2 * c)) * Real.pi) * G)) := by
    apply ha.congr'
    filter_upwards [] with N
    dsimp only [ccr25GaussianFiniteWordOperatorScale, G]
    ring
  have hq := tendsto_fourthFreeCost hm
  have hσzero := tendsto_quasiCritical_sigma_zero l β hratio hσ
  have hsqrt : Tendsto (fun N => Real.sqrt (Polymer.sigmaSq (β N))) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hσzero.sqrt
  have hfirst := ha'.mul (tendsto_quasiCritical_l_sigma_zero l β hratio hσ)
  have htwo := (((hu.pow 2).mul hsqrt).mul hq).const_mul
    ((2 : ℝ) ^ 32 * (max 1 (ccr25GaussianMomentUniformConstant 4)) ^ 8)
  have hratio4 := tendsto_quasiCritical_fourth_run_ratio l β hl hratio hβ hσ hc hm
  have hden : Tendsto (fun N => 1 -
      (ccr25GaussianFiniteWordOperatorScale 4
        (fourthInteractionCost (fourthWeightScale N) (m N) (β N)) * Polymer.sigmaSq (β N)) *
        fourthFreeCost (fourthWeightScale N) (m N)) atTop (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hratio4
  have htail := (((ha'.pow 3).mul (hq.pow 2)).div_atTop hl).div hden one_ne_zero
  have h := (hfirst.add htwo).add htail
  simpa only [fourthRemainderCoefficient, mul_zero, zero_mul, zero_div, add_zero, mul_assoc, Pi.div_def] using h

end Critical2DKPZ.Extensions.GffTangent
