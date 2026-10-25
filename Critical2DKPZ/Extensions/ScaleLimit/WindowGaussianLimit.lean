/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BandShapeComparison
public import Critical2DKPZ.Extensions.ScaleLimit.L2Perturbation
public import Critical2DKPZ.Extensions.ScaleLimit.BrownianIncrementLimit
public import Critical2DKPZ.Extensions.ScaleLimit.GaussianSquareTails

/-! # The normalized band variable and its approximation by a tested increment -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {D : Ω → Distr} {ν : Measure Plane}

/-- The normalized band difference in a fixed positive-time window. -/
def bandWindowVariable (hD : StationarySpectralData P D ν) (R s t : ℝ) (x : Plane)
    (L : Set.Ioi (0 : ℝ)) (ω : Ω) : ℝ :=
  (Real.sqrt (L : ℝ))⁻¹ *
    (bandField hD (R⁻¹ * scaleRadius L t) x ω - bandField hD (R * scaleRadius L s) x ω)

/-- The normalized error of one band endpoint compared with the original test. -/
def bandShapeError (hD : StationarySpectralData P D ν) (φ : TestFn) (κ s : ℝ) (x : Plane)
    (L : Set.Ioi (0 : ℝ)) (ω : Ω) : ℝ :=
  (Real.sqrt (L : ℝ))⁻¹ *
    (bandField hD (κ * scaleRadius L s) x ω - D ω (φ.dilate (scaleRadius L s) x))

/-- The scaled pairing is square integrable under the spectral data. -/
theorem spectral_scaledPairing_memLp (hD : StationarySpectralData P D ν)
    (φ : TestFn) (x : Plane) (L : Set.Ioi (0 : ℝ)) (s : ℝ) :
    MemLp (fun ω => scaledPairing (D ω) φ x L s) 2 P := by
  simpa only [scaledPairing, div_eq_mul_inv, mul_comm] using
    (hD.memLp (φ.dilate (scaleRadius L s) x)).const_mul ((Real.sqrt (L : ℝ))⁻¹)

theorem bandWindowVariable_memLp (hD : StationarySpectralData P D ν)
    (R s t : ℝ) (x : Plane) (L : Set.Ioi (0 : ℝ)) :
    MemLp (bandWindowVariable hD R s t x L) 2 P :=
  ((bandField_memLp hD _ x).sub (bandField_memLp hD _ x)).const_mul _

theorem bandShapeError_memLp (hD : StationarySpectralData P D ν)
    (φ : TestFn) (κ s : ℝ) (x : Plane) (L : Set.Ioi (0 : ℝ)) :
    MemLp (bandShapeError hD φ κ s x L) 2 P :=
  ((bandField_memLp hD _ x).sub (hD.memLp _)).const_mul _

/-- The normalized band increment differs from the tested increment by a
quantity tending to zero in L2. The two shape parameters are fixed before L. -/
theorem band_window_error_tendsto (hD : StationarySpectralData P D ν)
    (φ : TestFn) (hφ : (∫ y, φ y) = 1) (x : Plane)
    {R s t : ℝ} (hR : 0 < R) (hs : 0 < s) (ht : 0 < t) :
    Tendsto (fun L : Set.Ioi (0 : ℝ) => ∫ ω,
      (bandWindowVariable hD R s t x L ω -
        (scaledPairing (D ω) φ x L t - scaledPairing (D ω) φ x L s)) ^ 2 ∂P)
      atTop (𝓝 0) := by
  let E := bandShapeError hD φ R⁻¹ t x
  let F := bandShapeError hD φ R s x
  have hE : Tendsto (fun L => ∫ ω, E L ω ^ 2 ∂P) atTop (𝓝 0) :=
    shape_second_statement hD φ hφ x (inv_pos.mpr hR) ht
  have hF : Tendsto (fun L => ∫ ω, F L ω ^ 2 ∂P) atTop (𝓝 0) :=
    shape_second_statement hD φ hφ x hR hs
  have hup := (hE.const_mul 2).add (hF.const_mul 2)
  apply squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _) ?_
    (by simpa only [mul_zero, add_zero] using hup)
  intro L
  have hEi : Integrable (fun ω => E L ω ^ 2) P := (bandShapeError_memLp hD φ _ _ x L).integrable_sq
  have hFi : Integrable (fun ω => F L ω ^ 2) P := (bandShapeError_memLp hD φ _ _ x L).integrable_sq
  have htest : MemLp (fun ω => scaledPairing (D ω) φ x L t -
      scaledPairing (D ω) φ x L s) 2 P :=
    (spectral_scaledPairing_memLp hD φ x L t).sub (spectral_scaledPairing_memLp hD φ x L s)
  have herr := ((bandWindowVariable_memLp hD R s t x L).sub htest).integrable_sq
  have hmajor : Integrable (fun ω => 2 * E L ω ^ 2 + 2 * F L ω ^ 2) P :=
    (hEi.const_mul 2).add (hFi.const_mul 2)
  calc
    _ ≤ ∫ ω, 2 * E L ω ^ 2 + 2 * F L ω ^ 2 ∂P := by
      apply integral_mono_ae herr hmajor
      exact Eventually.of_forall fun ω => by
        change (bandWindowVariable hD R s t x L ω -
          (scaledPairing (D ω) φ x L t - scaledPairing (D ω) φ x L s)) ^ 2 ≤
            2 * E L ω ^ 2 + 2 * F L ω ^ 2
        have heq : bandWindowVariable hD R s t x L ω -
            (scaledPairing (D ω) φ x L t - scaledPairing (D ω) φ x L s) = E L ω - F L ω := by
          dsimp [E, F, bandShapeError, bandWindowVariable, scaledPairing]
          ring
        rw [heq]
        nlinarith only [sq_nonneg (E L ω + F L ω)]
    _ = _ := by
      rw [integral_add (hEi.const_mul 2) (hFi.const_mul 2), integral_const_mul, integral_const_mul]

/-- The source finite-dimensional convergence gives the Gaussian law of each
positive-time tested increment, on the real positive L filter. -/
theorem tested_window_increment_limit (φ : TestFn) (x : Plane)
    (hfdd : ∀ I : Finset ℝ≥0, (∀ s ∈ I, 0 < s) → TendstoInDistribution
      (fun (L : Set.Ioi (0 : ℝ)) ω (i : I) => scaledPairing (D ω) φ x L (i.1 : ℝ))
      atTop id (fun _ => P) (BrownianReal.projectiveFamily I))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    TendstoInDistribution (fun (L : Set.Ioi (0 : ℝ)) ω =>
      scaledPairing (D ω) φ x L t - scaledPairing (D ω) φ x L s) atTop id
      (fun _ => P) (gaussianReal 0 (Real.toNNReal (t - s))) := by
  let sn : ℝ≥0 := ⟨s, hs.le⟩
  let tn : ℝ≥0 := ⟨t, (hs.trans hst).le⟩
  let I : Finset ℝ≥0 := {sn, tn}
  let si : I := ⟨sn, by simp [I]⟩
  let ti : I := ⟨tn, by simp [I]⟩
  have hI : ∀ z ∈ I, 0 < z := by
    intro z hz
    simp only [I, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hs
    · exact hs.trans hst
  have hdist : nndist tn sn = Real.toNNReal (t - s) := by
    apply NNReal.coe_injective
    rw [coe_nndist, NNReal.dist_eq, Real.toNNReal_of_nonneg (sub_pos.mpr hst).le]
    exact abs_of_pos (sub_pos.mpr hst)
  have hh := brownian_increment_limit I ti si (hfdd I hI)
  change TendstoInDistribution (fun (L : Set.Ioi (0 : ℝ)) ω =>
    scaledPairing (D ω) φ x L t - scaledPairing (D ω) φ x L s) atTop id
    (fun _ => P) (gaussianReal 0 (nndist tn sn)) at hh
  rw [hdist] at hh
  exact hh

/-- The full positive-window Gaussian limit, including convergence of its
second moment. The only probabilistic hypotheses are the source finite-
dimensional limit and the source tested-increment moment limit. -/
theorem window_gaussian_limit (hD : StationarySpectralData P D ν)
    (φ : TestFn) (hφ : (∫ y, φ y) = 1) (x : Plane)
    (hfdd : ∀ I : Finset ℝ≥0, (∀ s ∈ I, 0 < s) → TendstoInDistribution
      (fun (L : Set.Ioi (0 : ℝ)) ω (i : I) => scaledPairing (D ω) φ x L (i.1 : ℝ))
      atTop id (fun _ => P) (BrownianReal.projectiveFamily I))
    (hinc : ∀ s t : ℝ, 0 < s → s < t → Tendsto (fun L : Set.Ioi (0 : ℝ) =>
      ∫ ω, (scaledPairing (D ω) φ x L t - scaledPairing (D ω) φ x L s) ^ 2 ∂P)
      atTop (𝓝 (t - s)))
    {R s t : ℝ} (hR : 0 < R) (hs : 0 < s) (hst : s < t) :
    TendstoInDistribution (bandWindowVariable hD R s t x) atTop id (fun _ => P)
      (gaussianReal 0 (Real.toNNReal (t - s))) ∧
      Tendsto (fun L => ∫ ω, bandWindowVariable hD R s t x L ω ^ 2 ∂P)
        atTop (𝓝 (t - s)) := by
  let X := fun (L : Set.Ioi (0 : ℝ)) ω =>
    scaledPairing (D ω) φ x L t - scaledPairing (D ω) φ x L s
  let Y := bandWindowVariable hD R s t x
  have hX (L) : MemLp (X L) 2 P :=
    (spectral_scaledPairing_memLp hD φ x L t).sub (spectral_scaledPairing_memLp hD φ x L s)
  have hY (L) : MemLp (Y L) 2 P := bandWindowVariable_memLp hD R s t x L
  have herr := band_window_error_tendsto hD φ hφ x hR hs (hs.trans hst)
  have hm (L) : MemLp (fun ω => Y L ω - X L ω) 2 P := (hY L).sub (hX L)
  have hprob : TendstoInMeasure P (Y - X) atTop 0 :=
    tendstoInMeasure_zero_of_integral_sq_tendsto hm herr
  exact ⟨tendstoInDistribution_of_tendstoInMeasure_sub Y id
      (tested_window_increment_limit φ x hfdd hs hst) hprob (fun L => (hY L).aemeasurable),
    integral_sq_tendsto_of_L2_perturbation (sub_pos.mpr hst).le hX hY (hinc s t hs hst) herr⟩


end Critical2DKPZ.Extensions.ScaleLimit
