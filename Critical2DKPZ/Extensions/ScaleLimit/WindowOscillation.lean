/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.WindowGaussianAllTimes
public import Critical2DKPZ.Extensions.ScaleLimit.WindowProbabilityBound
public import Critical2DKPZ.Extensions.ScaleLimit.GaussianTailScaling
public import Critical2DKPZ.Extensions.ScaleLimit.L2ErrorSum
public import Critical2DKPZ.Extensions.ScaleLimit.SquareTail
import Mathlib.Tactic

/-! # Uniform window oscillation bounds -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace Critical2DKPZ.Extensions.ScaleLimit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {D : Ω → Distr} {ν : Measure Plane}

/-- The scale limit is taken before sending the auxiliary band separation
to infinity. The Gaussian variance form applies to the first window as well. -/
theorem window_oscillation_variance (hD : StationarySpectralData P D ν)
    (φ : TestFn) (hφ : (∫ y, φ y) = 1) (x : Plane)
    (hfdd : ∀ I : Finset ℝ≥0, (∀ s ∈ I, 0 < s) → TendstoInDistribution
      (fun (L : Set.Ioi (0 : ℝ)) ω (i : I) => scaledPairing (D ω) φ x L (i.1 : ℝ))
      atTop id (fun _ => P) (BrownianReal.projectiveFamily I))
    (hvar : ∀ s : ℝ, 0 < s → Tendsto (fun L : Set.Ioi (0 : ℝ) =>
      ∫ ω, scaledPairing (D ω) φ x L s ^ 2 ∂P) atTop (𝓝 s))
    (hinc : ∀ s t : ℝ, 0 < s → s < t → Tendsto (fun L : Set.Ioi (0 : ℝ) =>
      ∫ ω, (scaledPairing (D ω) φ x L t - scaledPairing (D ω) φ x L s) ^ 2 ∂P)
      atTop (𝓝 (t - s)))
    : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ s t η : ℝ, 0 ≤ s → s < t → 0 < η →
      limsup (fun L : Set.Ioi (0 : ℝ) => P (windowOscillationEvent
        (fun r ω => scaledPairing (D ω) φ x L r) s t η)) atTop ≤
        ENNReal.ofReal ((C / η ^ 2) *
          ∫ y : ℝ, squareTail (c * η) y ∂gaussianReal 0 (Real.toNNReal (t - s))) := by
  obtain ⟨Cm, c, Cr, hCm, hc, hCr, hprob⟩ := window_probability_bound hD φ hφ x
  refine ⟨36 * Cm, c / 6, by positivity, by positivity, ?_⟩
  intro s t η hs hst hη
  let q := (c / 6) * η
  have hq : 0 < q := mul_pos (div_pos hc (by norm_num)) hη
  have hqeq : c * η / 6 = q := by dsimp [q]; ring
  let B := ENNReal.ofReal ((36 * Cm / η ^ 2) *
    ∫ y : ℝ, squareTail q y ∂gaussianReal 0 (Real.toNNReal (t - s)))
  let A := fun L : Set.Ioi (0 : ℝ) => P (windowOscillationEvent
    (fun r ω => scaledPairing (D ω) φ x L r) s t η)
  let e := fun R : ℝ => ENNReal.ofReal (36 * (Cr * R⁻¹ ^ 2 * t) / η ^ 2)
  have hb (R : ℝ) (hR : 0 < R) : limsup A atTop ≤ B + e R + e R := by
    have ht := window_squareTail_tendsto_nonneg hD φ hφ x hfdd hvar hinc hR hs hst hq
    have ht' : Tendsto (fun L : Set.Ioi (0 : ℝ) => ENNReal.ofReal
        ((36 * Cm / η ^ 2) * (∫ ω, squareTail q (bandWindowVariable hD R s t x L ω) ∂P)))
        atTop (𝓝 B) := ENNReal.continuous_ofReal.tendsto _ |>.comp (ht.const_mul _)
    have hf := (ht'.add_const (e R)).add_const (e R)
    have hbound := hprob R s t η hR hs hst hη
    simp_rw [hqeq] at hbound
    have hh := limsup_le_limsup hbound
    rw [hf.limsup_eq] at hh
    exact hh
  have hR : Tendsto (fun R : Set.Ioi (0 : ℝ) => (R : ℝ)) atTop atTop :=
    tendsto_Ioi_atTop.mp tendsto_id
  have hi := tendsto_inv_atTop_zero.comp hR
  have heReal : Tendsto (fun R : Set.Ioi (0 : ℝ) => 36 * (Cr * (R : ℝ)⁻¹ ^ 2 * t) / η ^ 2)
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, zero_div] using
      (((hi.pow 2).const_mul Cr).mul_const t).const_mul 36 |>.div_const (η ^ 2)
  have he : Tendsto (fun R : Set.Ioi (0 : ℝ) => e R) atTop (𝓝 0) := by
    have hh := (ENNReal.continuous_ofReal.tendsto 0).comp heReal
    change Tendsto (fun R : Set.Ioi (0 : ℝ) => ENNReal.ofReal
      (36 * (Cr * (R : ℝ)⁻¹ ^ 2 * t) / η ^ 2)) atTop (𝓝 (ENNReal.ofReal 0)) at hh
    rw [ENNReal.ofReal_zero] at hh
    exact hh
  have hlim : Tendsto (fun R : Set.Ioi (0 : ℝ) => B + e R + e R) atTop (𝓝 B) := by
    simpa only [add_zero] using (tendsto_const_nhds.add he).add he
  exact ge_of_tendsto hlim (Eventually.of_forall fun (R : Set.Ioi (0 : ℝ)) => hb R R.property)

/-- The one-window estimate with a standard Gaussian square tail and the
explicit window-length prefactor. This includes the window starting at zero. -/
theorem window_oscillation (hD : StationarySpectralData P D ν)
    (φ : TestFn) (hφ : (∫ y, φ y) = 1) (x : Plane)
    (hfdd : ∀ I : Finset ℝ≥0, (∀ s ∈ I, 0 < s) → TendstoInDistribution
      (fun (L : Set.Ioi (0 : ℝ)) ω (i : I) => scaledPairing (D ω) φ x L (i.1 : ℝ))
      atTop id (fun _ => P) (BrownianReal.projectiveFamily I))
    (hvar : ∀ s : ℝ, 0 < s → Tendsto (fun L : Set.Ioi (0 : ℝ) =>
      ∫ ω, scaledPairing (D ω) φ x L s ^ 2 ∂P) atTop (𝓝 s))
    (hinc : ∀ s t : ℝ, 0 < s → s < t → Tendsto (fun L : Set.Ioi (0 : ℝ) =>
      ∫ ω, (scaledPairing (D ω) φ x L t - scaledPairing (D ω) φ x L s) ^ 2 ∂P)
      atTop (𝓝 (t - s)))
    : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ s t η : ℝ, 0 ≤ s → s < t → 0 < η →
      limsup (fun L : Set.Ioi (0 : ℝ) => P (windowOscillationEvent
        (fun r ω => scaledPairing (D ω) φ x L r) s t η)) atTop ≤
        ENNReal.ofReal (C * (t - s) / η ^ 2 *
          ∫ y : ℝ, squareTail (c * η / Real.sqrt (t - s)) y ∂gaussianReal 0 1) := by
  obtain ⟨C, c, hC, hc, hb⟩ := window_oscillation_variance hD φ hφ x hfdd hvar hinc
  refine ⟨C, c, hC, hc, ?_⟩
  intro s t η hs hst hη
  have hh := hb s t η hs hst hη
  rw [gaussian_squareTail_scaling (sub_pos.mpr hst) (c * η)] at hh
  convert hh using 1
  congr 1
  ring

end Critical2DKPZ.Extensions.ScaleLimit
