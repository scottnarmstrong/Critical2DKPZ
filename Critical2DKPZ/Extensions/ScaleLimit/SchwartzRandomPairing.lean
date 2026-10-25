/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SchwartzPairingConstruction
public import Critical2DKPZ.Extensions.ScaleLimit.SchwartzTranslate
import Critical2DKPZ.Extensions.ScaleLimit.SchwartzPairingTranslation
import Critical2DKPZ.Extensions.ScaleLimit.LpTupleLaw

/-! # The stationary stochastic Schwartz extension

The stochastic Schwartz extension is constructed from stationary spectral data.
Its laws are obtained by passing the finite-family laws of translated compact
cutoffs to L² limits. No sample temperedness or spectral density is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {D : Ω → Distr} {ν : Measure Plane}

/-- The stochastic Schwartz pairing preserves all finite-family translation laws. -/
theorem schwartzPairing_stationary (hD : StationarySpectralData P D ν)
    (n : ℕ) (f : Fin n → SchwartzMap Plane ℝ) (z : Plane) :
    IdentDistrib (fun ω i => schwartzPairing hD (translateSchwartz z (f i)) ω)
      (fun ω i => schwartzPairing hD (f i) ω) P P := by
  apply identDistrib_lpTuple_limit
    (v := fun k i => testRandomLp hD ((Spectral.scaledCutoffTestFn k (f i)).dilate 1 z))
    (u := fun k i => testRandomLp hD (Spectral.scaledCutoffTestFn k (f i)))
  · intro k
    have hs := hD.stationary n (fun i => Spectral.scaledCutoffTestFn k (f i)) z
    have hL : (fun ω i => testRandomLp hD ((Spectral.scaledCutoffTestFn k (f i)).dilate 1 z) ω)
        =ᵐ[P] fun ω i => D ω ((Spectral.scaledCutoffTestFn k (f i)).dilate 1 z) := by
      have h := ae_all_iff.mpr (fun i : Fin n =>
        testRandomLp_coe hD ((Spectral.scaledCutoffTestFn k (f i)).dilate 1 z))
      exact h.mono fun ω hω => funext hω
    have hR : (fun ω i => testRandomLp hD (Spectral.scaledCutoffTestFn k (f i)) ω)
        =ᵐ[P] fun ω i => D ω (Spectral.scaledCutoffTestFn k (f i)) := by
      have h := ae_all_iff.mpr (fun i : Fin n =>
        testRandomLp_coe hD (Spectral.scaledCutoffTestFn k (f i)))
      exact h.mono fun ω hω => funext hω
    exact (IdentDistrib.of_ae_eq hs.aemeasurable_fst hL.symm).symm.trans
      (hs.trans (IdentDistrib.of_ae_eq hs.aemeasurable_snd hR.symm))
  · intro i
    exact schwartzPairing_translated_cutoff_tendsto hD (f i) z
  · intro i
    exact schwartzPairing_cutoff_tendsto hD (f i)

/-- The distribution has a linear stationary extension to all real Schwartz tests,
with its exact spectral covariance. -/
theorem exists_schwartz_extension (hD : StationarySpectralData P D ν) :
    ∃ E : SchwartzMap Plane ℝ →ₗ[ℝ] Lp ℝ 2 P,
      (∀ f : TestFn, (E (Spectral.testFnToRealSchwartz f) : Ω → ℝ) =ᵐ[P]
        fun ω => D ω f) ∧
      (∀ f g, (∫ ω, E f ω * E g ω ∂P) =
        ∫ ξ, (Spectral.fourierKPZ f ξ * star (Spectral.fourierKPZ g ξ)).re ∂ν) ∧
      (∀ (n : ℕ) (f : Fin n → SchwartzMap Plane ℝ) (z : Plane),
        IdentDistrib (fun ω i => E (translateSchwartz z (f i)) ω)
          (fun ω i => E (f i) ω) P P) := by
  refine ⟨(schwartzPairing hD).toLinearMap, ?_, schwartzPairing_covariance hD,
    schwartzPairing_stationary hD⟩
  intro f
  change (schwartzPairing hD (Spectral.testFnToRealSchwartz f) : Ω → ℝ) =ᵐ[P] _
  rw [schwartzPairing_test]
  exact testRandomLp_coe hD f

/-- A selected stochastic Schwartz extension with the three properties below. -/
def schwartzExt (hD : StationarySpectralData P D ν) :
    SchwartzMap Plane ℝ →ₗ[ℝ] Lp ℝ 2 P :=
  (exists_schwartz_extension hD).choose

/-- Agreement of the selected extension with the original compact-test pairing. -/
theorem schwartzExt_test (hD : StationarySpectralData P D ν) (f : TestFn) :
    (schwartzExt hD (Spectral.testFnToRealSchwartz f) : Ω → ℝ) =ᵐ[P] fun ω => D ω f :=
  (exists_schwartz_extension hD).choose_spec.1 f

/-- The selected extension has the exact angular spectral covariance. -/
theorem schwartzExt_covariance (hD : StationarySpectralData P D ν)
    (f g : SchwartzMap Plane ℝ) :
    (∫ ω, schwartzExt hD f ω * schwartzExt hD g ω ∂P) =
      ∫ ξ, (Spectral.fourierKPZ f ξ * star (Spectral.fourierKPZ g ξ)).re ∂ν :=
  (exists_schwartz_extension hD).choose_spec.2.1 f g

/-- The selected extension is jointly stationary for every finite family of tests. -/
theorem schwartzExt_stationary (hD : StationarySpectralData P D ν)
    (n : ℕ) (f : Fin n → SchwartzMap Plane ℝ) (z : Plane) :
    IdentDistrib (fun ω i => schwartzExt hD (translateSchwartz z (f i)) ω)
      (fun ω i => schwartzExt hD (f i) ω) P P :=
  (exists_schwartz_extension hD).choose_spec.2.2 n f z

end Critical2DKPZ.Extensions.ScaleLimit
