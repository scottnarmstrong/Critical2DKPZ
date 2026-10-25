/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonFourthAsymptotic
import Mathlib.Tactic

/-! # Signed cell profiles and the sharp fourth-moment bound -/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Critical2DKPZ.Extensions.GffTangent

/-- A difference has fourth power bounded by eight times the two fourth powers. -/
theorem sub_fourth_le (x y : ℝ) : (x - y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by
  have h : 0 ≤ (x + y) ^ 2 * (2 * (x ^ 2 + y ^ 2) + 5 * (x - y) ^ 2) := by positivity
  nlinarith only [h]

/-- The finite entrance pairing is linear in its signed spatial profile. -/
theorem finiteEntranceFluctuation_sub (β c : ℝ) (a n : ℕ) (S : Finset Site)
    (φ ψ : Site → ℝ) (ω : Disorder) :
    finiteEntranceFluctuation β c a n S (fun w => φ w - ψ w) ω =
      finiteEntranceFluctuation β c a n S φ ω - finiteEntranceFluctuation β c a n S ψ ω := by
  simp only [finiteEntranceFluctuation, sub_mul, Finset.sum_sub_distrib, mul_sub]
  ring

/-- Fourth moments of the actual signed cell profile reduce to its two
nonnegative parts; signs are split after integrating over each exact cell. -/
theorem integral_fourth_signedCellProfile_le (N : ℕ) (f : TestFn) (β c : ℝ) (L : ℕ) :
    (∫ ω, finiteEntranceFluctuation β c 0 L (fixedHorizonCellSites N f)
      (signedCellProfile N f) ω ^ 4 ∂disorderLaw) ≤
    8 * ((∫ ω, finiteEntranceFluctuation β c 0 L (fixedHorizonCellSites N f)
      (positiveCellProfile N f) ω ^ 4 ∂disorderLaw) +
      ∫ ω, finiteEntranceFluctuation β c 0 L (fixedHorizonCellSites N f)
        (negativeCellProfile N f) ω ^ 4 ∂disorderLaw) := by
  have hpos := (memLp_finiteEntranceFluctuation β c 0 L (fixedHorizonCellSites N f)
    (positiveCellProfile N f) 4 (by norm_num)).integrable_norm_pow'
  have hneg := (memLp_finiteEntranceFluctuation β c 0 L (fixedHorizonCellSites N f)
    (negativeCellProfile N f) 4 (by norm_num)).integrable_norm_pow'
  have hsigned := (memLp_finiteEntranceFluctuation β c 0 L (fixedHorizonCellSites N f)
    (signedCellProfile N f) 4 (by norm_num)).integrable_norm_pow'
  simp only [Real.norm_eq_abs, Even.pow_abs (by decide : Even 4)] at hpos hneg hsigned
  rw [← integral_add hpos hneg, ← integral_const_mul]
  apply integral_mono hsigned ((hpos.add hneg).const_mul 8)
  intro ω
  have he : signedCellProfile N f = fun w => positiveCellProfile N f w - negativeCellProfile N f w := by
    funext w
    exact (positiveCellProfile_sub_negativeCellProfile N f w).symm
  dsimp only [Pi.add_apply]
  rw [he, finiteEntranceFluctuation_sub]
  exact sub_fourth_le _ _

/-- The signed fourth-moment leading constant is uniform in the positive
macroscopic window length. This is the model estimate used by the CCR array. -/
theorem eventually_fourth_signed_cell_profile_le (f : TestFn)
    {Cf : ℝ} (hCf : 0 ≤ Cf) (hfC : ∀ x : Plane, |f x| ≤ Cf)
    (l β : ℕ → ℝ) (hl : Tendsto l atTop atTop)
    (hratio : Tendsto (fun N => l N / Real.log (N : ℝ)) atTop (𝓝 0))
    (hβ : ∀ᶠ N : ℕ in atTop, 0 < β N)
    (hσ : ∀ᶠ N : ℕ in atTop, Polymer.sigmaSq (β N) = criticalSigmaSq (-l N) N)
    {m : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hm : Tendsto (fun N : ℕ => (m N : ℝ) / N) atTop (𝓝 c))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∫ ω, finiteEntranceFluctuation (β N) (Real.sqrt (l N)) 0 (m N)
        (fixedHorizonCellSites N f) (signedCellProfile N f) ω ^ 4 ∂disorderLaw) ≤
      (16 * ((2 : ℝ) ^ 32 * Real.pi ^ 2 * (4 * Cf * ∫ x : Plane, |f x|) ^ 2)) * c ^ 2 + ε := by
  have hdom := positive_negative_cell_profile_domination
  have hp := eventually_fourth_positive_cell_profile_le f hCf hfC
    (fun N => positiveCellProfile N f) (fun N w => (hdom N f w).1.1)
    (fun N w => (hdom N f w).1.2) l β hl hratio hβ hσ hc hm (ε := ε / 16) (by positivity)
  have hn := eventually_fourth_positive_cell_profile_le f hCf hfC
    (fun N => negativeCellProfile N f) (fun N w => (hdom N f w).2.1)
    (fun N w => (hdom N f w).2.2) l β hl hratio hβ hσ hc hm (ε := ε / 16) (by positivity)
  filter_upwards [hp, hn] with N hpN hnN
  have h := integral_fourth_signedCellProfile_le N f (β N) (Real.sqrt (l N)) (m N)
  linarith only [h, hpN, hnN]

end Critical2DKPZ.Extensions.GffTangent
