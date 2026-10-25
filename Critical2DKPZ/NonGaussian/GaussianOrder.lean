/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.EhrhardType.NormalCDF
public import Critical2DKPZ.EhrhardType.ConvexSublevels
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Stochastic comparison of monotone Gaussian representatives -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open Critical2DKPZ.EhrhardType
open scoped Topology

namespace Critical2DKPZ.NonGaussian

/-- Stochastic order of monotone Gaussian images gives pointwise order when the
upper representative is continuous. Constants are included. -/
theorem monotone_le_of_standardGaussian_sublevel_le {f g : ℝ → ℝ}
    (hf : Monotone f) (hg : Monotone g) (hgc : Continuous g)
    (horder : ∀ a : ℝ, ((gaussianReal 0 1).map g) (Iio a) ≤
      ((gaussianReal 0 1).map f) (Iio a)) :
    ∀ z, f z ≤ g z := by
  intro z
  by_contra hz
  obtain ⟨a, hga, haf⟩ := exists_between (lt_of_not_ge hz)
  have hn : ∀ᶠ b in 𝓝 z, g b < a := (isOpen_lt hgc continuous_const).mem_nhds hga
  obtain ⟨b, hzb, hba⟩ := hn.exists_gt
  have hleft : (gaussianReal 0 1) (Iio b) ≤ ((gaussianReal 0 1).map g) (Iio a) := by
    rw [Measure.map_apply hg.measurable measurableSet_Iio]
    apply measure_mono
    intro x hx
    exact (hg (le_of_lt hx)).trans_lt hba
  have hright : ((gaussianReal 0 1).map f) (Iio a) ≤ (gaussianReal 0 1) (Iio z) := by
    rw [Measure.map_apply hf.measurable measurableSet_Iio]
    apply measure_mono
    intro x hx
    by_contra hxz
    have hzx : z ≤ x := le_of_not_gt hxz
    exact (haf.trans_le (hf hzx)).not_ge hx.le
  have hstrict : (gaussianReal 0 1) (Iio z) < (gaussianReal 0 1) (Iio b) := by
    apply (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
    rw [strictCDF_standardGaussian, strictCDF_standardGaussian]
    exact strictMono_standardGaussian_cdf hzb
  exact hstrict.not_ge (hleft.trans ((horder a).trans hright))

/-- A finite convex function lying below an affine function is affine with the same slope. -/
theorem eq_affine_of_convex_bounded_above_sub {h : ℝ → ℝ}
    (hc : ConvexOn ℝ univ h) (s K : ℝ) (hb : ∀ x, h x ≤ s * x + K) :
    ∀ x, h x = s * x + h 0 := by
  have hlinear : ConcaveOn ℝ univ (fun x : ℝ => s * x) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ _
    simp only [smul_eq_mul]
    exact le_of_eq (by ring)
  have hd : ConvexOn ℝ univ (fun x => h x - s * x) := hc.sub hlinear
  have hconst : ∀ x, h x - s * x = h 0 - s * 0 := by
    by_contra hn
    obtain ⟨x, hx⟩ := exists_lt_convex_of_nonconstant hd hn K
    linarith only [hb x, hx]
  intro x
  have hx := hconst x
  linarith only [hx]

end Critical2DKPZ.NonGaussian

end
