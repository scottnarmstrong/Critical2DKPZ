/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.FirstWindowGaussianLimit
public import Critical2DKPZ.Extensions.ScaleLimit.L2ErrorSum
public import Critical2DKPZ.Extensions.ScaleLimit.SquareTail
import Mathlib.Tactic

/-! # Gaussian window limits at all nonnegative start times -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace Critical2DKPZ.Extensions.ScaleLimit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {D : Ω → Distr} {ν : Measure Plane}

/-- Positive and first windows have the same Gaussian increment limit. -/
theorem window_gaussian_limit_nonneg (hD : StationarySpectralData P D ν)
    (φ : TestFn) (hφ : (∫ y, φ y) = 1) (x : Plane)
    (hfdd : ∀ I : Finset ℝ≥0, (∀ s ∈ I, 0 < s) → TendstoInDistribution
      (fun (L : Set.Ioi (0 : ℝ)) ω (i : I) => scaledPairing (D ω) φ x L (i.1 : ℝ))
      atTop id (fun _ => P) (BrownianReal.projectiveFamily I))
    (hvar : ∀ s : ℝ, 0 < s → Tendsto (fun L : Set.Ioi (0 : ℝ) =>
      ∫ ω, scaledPairing (D ω) φ x L s ^ 2 ∂P) atTop (𝓝 s))
    (hinc : ∀ s t : ℝ, 0 < s → s < t → Tendsto (fun L : Set.Ioi (0 : ℝ) =>
      ∫ ω, (scaledPairing (D ω) φ x L t - scaledPairing (D ω) φ x L s) ^ 2 ∂P)
      atTop (𝓝 (t - s)))
    {R s t : ℝ} (hR : 0 < R) (hs : 0 ≤ s) (hst : s < t) :
    TendstoInDistribution (bandWindowVariable hD R s t x) atTop id (fun _ => P)
      (gaussianReal 0 (Real.toNNReal (t - s))) ∧
      Tendsto (fun L => ∫ ω, bandWindowVariable hD R s t x L ω ^ 2 ∂P)
        atTop (𝓝 (t - s)) := by
  rcases hs.eq_or_lt with h0 | hs
  · subst s
    simpa only [sub_zero] using first_window_gaussian_limit hD φ hφ x hfdd hvar hR hst
  · exact window_gaussian_limit hD φ hφ x hfdd hinc hR hs hst

/-- The source truncated window moment limit also holds at start time zero. -/
theorem window_squareTail_tendsto_nonneg (hD : StationarySpectralData P D ν)
    (φ : TestFn) (hφ : (∫ y, φ y) = 1) (x : Plane)
    (hfdd : ∀ I : Finset ℝ≥0, (∀ s ∈ I, 0 < s) → TendstoInDistribution
      (fun (L : Set.Ioi (0 : ℝ)) ω (i : I) => scaledPairing (D ω) φ x L (i.1 : ℝ))
      atTop id (fun _ => P) (BrownianReal.projectiveFamily I))
    (hvar : ∀ s : ℝ, 0 < s → Tendsto (fun L : Set.Ioi (0 : ℝ) =>
      ∫ ω, scaledPairing (D ω) φ x L s ^ 2 ∂P) atTop (𝓝 s))
    (hinc : ∀ s t : ℝ, 0 < s → s < t → Tendsto (fun L : Set.Ioi (0 : ℝ) =>
      ∫ ω, (scaledPairing (D ω) φ x L t - scaledPairing (D ω) φ x L s) ^ 2 ∂P)
      atTop (𝓝 (t - s)))
    {R s t q : ℝ} (hR : 0 < R) (hs : 0 ≤ s) (hst : s < t) (hq : 0 < q) :
    Tendsto (fun L => ∫ ω, squareTail q (bandWindowVariable hD R s t x L ω) ∂P) atTop
      (𝓝 (∫ y : ℝ, squareTail q y ∂gaussianReal 0 (Real.toNNReal (t - s)))) := by
  obtain ⟨hlaw, h2⟩ := window_gaussian_limit_nonneg hD φ hφ x hfdd hvar hinc hR hs hst
  have h2' : Tendsto (fun L => ∫ ω, bandWindowVariable hD R s t x L ω ^ 2 ∂P) atTop
      (𝓝 ((Real.toNNReal (t - s) : ℝ≥0) : ℝ)) := by
    rw [Real.toNNReal_of_nonneg (sub_pos.mpr hst).le]
    exact h2
  have hh := truncated_second_moment_tendsto P
    (fun L => (bandWindowVariable_memLp hD R s t x L).aemeasurable)
    (fun L => (bandWindowVariable_memLp hD R s t x L).integrable_sq) hlaw h2' hq
  exact hh

end Critical2DKPZ.Extensions.ScaleLimit
