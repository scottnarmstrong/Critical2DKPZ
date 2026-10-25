/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.WindowGaussianLimit
public import Critical2DKPZ.Extensions.ScaleLimit.L2ErrorSum
public import Critical2DKPZ.Extensions.ScaleLimit.SquareTail
import Mathlib.Tactic

/-! # The Gaussian band limit in the first window -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace Critical2DKPZ.Extensions.ScaleLimit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {D : Ω → Distr} {ν : Measure Plane}

/-- The positive-time finite-dimensional limit supplies each one-time limit. -/
theorem tested_single_time_limit (φ : TestFn) (x : Plane)
    (hfdd : ∀ I : Finset ℝ≥0, (∀ s ∈ I, 0 < s) → TendstoInDistribution
      (fun (L : Set.Ioi (0 : ℝ)) ω (i : I) => scaledPairing (D ω) φ x L (i.1 : ℝ))
      atTop id (fun _ => P) (BrownianReal.projectiveFamily I))
    {t : ℝ} (ht : 0 < t) :
    TendstoInDistribution (fun (L : Set.Ioi (0 : ℝ)) ω => scaledPairing (D ω) φ x L t)
      atTop id (fun _ => P) (gaussianReal 0 (Real.toNNReal t)) := by
  let tn : ℝ≥0 := ⟨t, ht.le⟩
  let I : Finset ℝ≥0 := {tn}
  let ti : I := ⟨tn, by simp [I]⟩
  have hI : ∀ z ∈ I, 0 < z := by
    intro z hz
    have hz' : z = tn := Finset.mem_singleton.mp hz
    subst z
    exact ht
  have hh := brownian_coordinate_limit I ti (hfdd I hI)
  change TendstoInDistribution (fun (L : Set.Ioi (0 : ℝ)) ω => scaledPairing (D ω) φ x L t)
    atTop id (fun _ => P) (gaussianReal 0 tn) at hh
  have heq : tn = Real.toNNReal t := by rw [Real.toNNReal_of_nonneg ht.le]; rfl
  rw [heq] at hh
  exact hh

/-- In the zero window only the upper endpoint needs shape comparison.
The coarse band at radius `R/e` is fixed and negligible in normalized L2. -/
theorem first_band_window_error_tendsto (hD : StationarySpectralData P D ν)
    (φ : TestFn) (hφ : (∫ z, φ z) = 1) (x : Plane)
    {R t : ℝ} (hR : 0 < R) (ht : 0 < t) :
    Tendsto (fun L : Set.Ioi (0 : ℝ) => ∫ ω,
      (bandWindowVariable hD R 0 t x L ω - scaledPairing (D ω) φ x L t) ^ 2 ∂P) atTop (𝓝 0) := by
  let E := bandShapeError hD φ R⁻¹ t x
  let B := fun (L : Set.Ioi (0 : ℝ)) ω => (Real.sqrt (L : ℝ))⁻¹ *
    bandField hD (R * Real.exp (-1)) x ω
  have hE (L) : MemLp (E L) 2 P := bandShapeError_memLp hD φ R⁻¹ t x L
  have hE2 : Tendsto (fun L => ∫ ω, E L ω ^ 2 ∂P) atTop (𝓝 0) :=
    shape_second_statement hD φ hφ x (inv_pos.mpr hR) ht
  obtain ⟨hB, hB2⟩ := normalized_fixed_L2_limit P
    (bandField hD (R * Real.exp (-1)) x) (bandField_memLp hD _ _)
  have hh := integral_sq_sub_tendsto_zero P hE hB hE2 hB2
  apply hh.congr
  intro L
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => by
    dsimp [E, B, bandShapeError, bandWindowVariable, scaledPairing]
    rw [show scaleRadius (L : ℝ) 0 = Real.exp (-1) by simp [scaleRadius]]
    ring

/-- The first-window band variable has the Gaussian one-time limit and its
second-moment limit, under exactly the source one-time hypotheses. -/
theorem first_window_gaussian_limit (hD : StationarySpectralData P D ν)
    (φ : TestFn) (hφ : (∫ z, φ z) = 1) (x : Plane)
    (hfdd : ∀ I : Finset ℝ≥0, (∀ s ∈ I, 0 < s) → TendstoInDistribution
      (fun (L : Set.Ioi (0 : ℝ)) ω (i : I) => scaledPairing (D ω) φ x L (i.1 : ℝ))
      atTop id (fun _ => P) (BrownianReal.projectiveFamily I))
    (hvar : ∀ s : ℝ, 0 < s → Tendsto (fun L : Set.Ioi (0 : ℝ) =>
      ∫ ω, scaledPairing (D ω) φ x L s ^ 2 ∂P) atTop (𝓝 s))
    {R t : ℝ} (hR : 0 < R) (ht : 0 < t) :
    TendstoInDistribution (bandWindowVariable hD R 0 t x) atTop id (fun _ => P)
      (gaussianReal 0 (Real.toNNReal t)) ∧
      Tendsto (fun L => ∫ ω, bandWindowVariable hD R 0 t x L ω ^ 2 ∂P) atTop (𝓝 t) := by
  let X := fun (L : Set.Ioi (0 : ℝ)) ω => scaledPairing (D ω) φ x L t
  let Y := bandWindowVariable hD R 0 t x
  have hX (L) : MemLp (X L) 2 P := spectral_scaledPairing_memLp hD φ x L t
  have hY (L) : MemLp (Y L) 2 P := bandWindowVariable_memLp hD R 0 t x L
  have herr := first_band_window_error_tendsto hD φ hφ x hR ht
  have hm (L) : MemLp (fun ω => Y L ω - X L ω) 2 P := (hY L).sub (hX L)
  have hprob : TendstoInMeasure P (Y - X) atTop 0 :=
    tendstoInMeasure_zero_of_integral_sq_tendsto hm herr
  exact ⟨tendstoInDistribution_of_tendstoInMeasure_sub Y id
      (tested_single_time_limit φ x hfdd ht) hprob (fun L => (hY L).aemeasurable),
    integral_sq_tendsto_of_L2_perturbation ht.le hX hY (hvar t ht) herr⟩

end Critical2DKPZ.Extensions.ScaleLimit
