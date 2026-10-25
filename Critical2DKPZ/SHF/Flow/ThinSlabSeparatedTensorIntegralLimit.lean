/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabSeparatedKernelMeasure

/-! # Convergence of separated four-replica tensor integrals -/

@[expose] public noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.DeltaBose
open scoped CompactlySupported Topology

namespace Critical2DKPZ.SHF.Flow

/-- Separated four-replica tensor moments converge to the two-block kernel integral, with eventual integrability supplied by `eventually_slabSeparatedTensorMass_sq_bound`. -/
theorem tendsto_slabSeparatedTensorIntegral (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s t r u : ℝ} (hs : 0 ≤ s) (hst : s < t) (htr : t < r) (hru : r < u)
    (φ : Fin 4 → C_c(Plane × Plane, ℝ)) :
    Tendsto
      (fun N => ∫ ω, ∫ q, slabCompactPiTensorTest φ q ∂
        (slabTwoBlockPiMeasure (polymerMeasure ϑ N s t ω)
          (polymerMeasure ϑ N r u ω)) ∂disorderLaw)
      atTop
      (𝓝 (slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r)
        (slabCompactPiTensorTest φ))) := by
  let φ₁ : Fin 2 → C_c(Plane × Plane, ℝ) := fun i => φ (i.castAdd 2)
  let φ₂ : Fin 2 → C_c(Plane × Plane, ℝ) := fun i => φ (i.natAdd 2)
  have hsource (N : ℕ) :
      (∫ ω, ∫ q, slabCompactPiTensorTest φ q ∂
        (slabTwoBlockPiMeasure (polymerMeasure ϑ N s t ω)
          (polymerMeasure ϑ N r u ω)) ∂disorderLaw) =
      ∫ ω,
        slabPairingTensorFunctional φ₁ (polymerRadonMeasure ϑ N s t ω) *
          slabPairingTensorFunctional φ₂ (polymerRadonMeasure ϑ N r u ω)
          ∂disorderLaw := by
    apply integral_congr_ae
    filter_upwards [] with ω
    have hμ : SigmaFinite (polymerMeasure ϑ N s t ω) :=
      @MeasureTheory.sigmaFinite_of_locallyFinite (Plane × Plane) _
        (polymerMeasure ϑ N s t ω) inferInstance inferInstance
        (isLocallyFiniteMeasure_polymerMeasure ϑ N s t ω)
    have hν : SigmaFinite (polymerMeasure ϑ N r u ω) :=
      @MeasureTheory.sigmaFinite_of_locallyFinite (Plane × Plane) _
        (polymerMeasure ϑ N r u ω) inferInstance inferInstance
        (isLocallyFiniteMeasure_polymerMeasure ϑ N r u ω)
    have hprod := integral_slabCompactPiTensorTest_twoBlock hμ hν φ
    have hpair₁ : slabPairingTensorFunctional φ₁
        (polymerRadonMeasure ϑ N s t ω) =
        ∏ i : Fin 2, ∫ p, φ₁ i p ∂polymerMeasure ϑ N s t ω := by
      simp [slabPairingTensorFunctional, RandomMeasure.vaguePairing, polymerRadonMeasure]
    have hpair₂ : slabPairingTensorFunctional φ₂
        (polymerRadonMeasure ϑ N r u ω) =
        ∏ i : Fin 2, ∫ p, φ₂ i p ∂polymerMeasure ϑ N r u ω := by
      simp [slabPairingTensorFunctional, RandomMeasure.vaguePairing, polymerRadonMeasure]
    rw [hpair₁, hpair₂]
    simpa only [φ₁, φ₂] using hprod
  have htensor := tendsto_slabSeparatedTensorMoment ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst htr hru φ₁ φ₂
  have htarget := integral_slabSeparatedMomentPiMeasure_tensor
    (ϑ - Real.eulerMascheroniConstant) (τ₁ := t - s) (τ₂ := u - r)
    (by linarith) (by linarith) φ
  rw [show (fun N => ∫ ω, ∫ q, slabCompactPiTensorTest φ q ∂
      (slabTwoBlockPiMeasure (polymerMeasure ϑ N s t ω)
        (polymerMeasure ϑ N r u ω)) ∂disorderLaw) =
      (fun N => ∫ ω,
        slabPairingTensorFunctional φ₁ (polymerRadonMeasure ϑ N s t ω) *
          slabPairingTensorFunctional φ₂ (polymerRadonMeasure ϑ N r u ω)
          ∂disorderLaw) from funext hsource]
  rw [htarget]
  exact htensor

end Critical2DKPZ.SHF.Flow

end
