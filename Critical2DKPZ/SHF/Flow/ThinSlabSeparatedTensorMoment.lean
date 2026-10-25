/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.FiniteScaleBlocks
public import Critical2DKPZ.SHF.Flow.ThinSlabTensorTests
public import Critical2DKPZ.RandomMeasure.PlanePairInterface
import Critical2DKPZ.SHF.Flow.PiMomentConvergence

/-! Tensor moments of two polymer blocks converge to continuum kernel moments. -/

@[expose] public noncomputable section

open MeasureTheory Filter ProbabilityTheory
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.DeltaBose
open scoped CompactlySupported Topology

namespace Critical2DKPZ.SHF.Flow

/-- The two-replica tensor pairing as a continuous functional of a Radon measure. -/
def slabPairingTensorFunctional (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (μ : RandomMeasure.PlanePairRadonMeasure) : ℝ :=
  RandomMeasure.vaguePairing μ (φ 0) * RandomMeasure.vaguePairing μ (φ 1)

/-- Annealed tensor moments on two disjoint polymer slabs factor and converge to the product
of their two-replica moment-kernel integrals. The eventual integrability and mass domination
are supplied by `eventually_slabSeparatedTensorMass_sq_bound`. -/
theorem tendsto_slabSeparatedTensorMoment (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s t r u : ℝ} (hs : 0 ≤ s) (hst : s < t) (htr : t < r) (hru : r < u)
    (φ ψ : Fin 2 → C_c(Plane × Plane, ℝ)) :
    Tendsto
      (fun N => ∫ ω,
        slabPairingTensorFunctional φ (polymerRadonMeasure ϑ N s t ω) *
          slabPairingTensorFunctional ψ (polymerRadonMeasure ϑ N r u ω)
          ∂disorderLaw)
      atTop
      (nhds
        ((∫ x : Configuration 2, ∫ y : Configuration 2,
            (∏ i, φ i (x i, y i)) *
              (momentKernel 2 (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal) *
          (∫ x : Configuration 2, ∫ y : Configuration 2,
            (∏ i, ψ i (x i, y i)) *
              (momentKernel 2 (ϑ - Real.eulerMascheroniConstant) (u - r) x y).toReal))) := by
  let times : Fin 4 → ℝ := ![s, t, r, u]
  have htimes : StrictMono times := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [times] <;> linarith
  have hAcont : Continuous (slabPairingTensorFunctional φ) := by
    change Continuous (fun μ =>
      RandomMeasure.vaguePairing μ (φ 0) * RandomMeasure.vaguePairing μ (φ 1))
    exact (RandomMeasure.continuous_vaguePairing (φ 0)).mul
      (RandomMeasure.continuous_vaguePairing (φ 1))
  have hBcont : Continuous (slabPairingTensorFunctional ψ) := by
    change Continuous (fun μ =>
      RandomMeasure.vaguePairing μ (ψ 0) * RandomMeasure.vaguePairing μ (ψ 1))
    exact (RandomMeasure.continuous_vaguePairing (ψ 0)).mul
      (RandomMeasure.continuous_vaguePairing (ψ 1))
  have hAmeas (N : ℕ) : Measurable
      (fun ω => slabPairingTensorFunctional φ (polymerRadonMeasure ϑ N s t ω)) :=
    hAcont.measurable.comp (measurable_polymerRadonMeasure ϑ N s t)
  have hBmeas (N : ℕ) : Measurable
      (fun ω => slabPairingTensorFunctional ψ (polymerRadonMeasure ϑ N r u ω)) :=
    hBcont.measurable.comp (measurable_polymerRadonMeasure ϑ N r u)
  have hBlocks (N : ℕ) :=
    iIndepFun_polymerRadonMeasure_consecutive ϑ N 3 times htimes
  have hIndep (N : ℕ) :
      (fun ω => slabPairingTensorFunctional φ (polymerRadonMeasure ϑ N s t ω)) ⟂ᵢ[disorderLaw]
        (fun ω => slabPairingTensorFunctional ψ (polymerRadonMeasure ϑ N r u ω)) := by
    have h := (hBlocks N).indepFun (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide)
    have h' : (fun ω => polymerRadonMeasure ϑ N s t ω) ⟂ᵢ[disorderLaw]
        (fun ω => polymerRadonMeasure ϑ N r u ω) := by
      simpa [times] using h
    exact h'.comp hAcont.measurable hBcont.measurable
  let Fφ : C_c((Fin 2 → Plane × Plane), ℝ) := slabCompactPiTensorTest φ
  let Fψ : C_c((Fin 2 → Plane × Plane), ℝ) := slabCompactPiTensorTest ψ
  have hφPi := polymerMeasure_pi_moment_tendsto_of ϑ hPolymerMomentInput hFlatSixthMomentInput 2
    (by norm_num) (by norm_num) hs hst Fφ Fφ.continuous Fφ.hasCompactSupport
  have hψPi := polymerMeasure_pi_moment_tendsto_of ϑ hPolymerMomentInput hFlatSixthMomentInput 2
    (by norm_num) (by norm_num) (by linarith : 0 ≤ r) hru Fψ Fψ.continuous Fψ.hasCompactSupport
  have hφSource :
      (fun N => ∫ ω, slabPairingTensorFunctional φ
        (polymerRadonMeasure ϑ N s t ω) ∂disorderLaw) =
      (fun N => ∫ ω, ∫ q, Fφ q ∂
        (Measure.pi fun _ : Fin 2 => polymerMeasure ϑ N s t ω) ∂disorderLaw) := by
    funext N
    apply integral_congr_ae
    filter_upwards [] with ω
    have hSigma : SigmaFinite (polymerMeasure ϑ N s t ω) :=
      @MeasureTheory.sigmaFinite_of_locallyFinite (Plane × Plane) _
        (polymerMeasure ϑ N s t ω) inferInstance inferInstance
        (isLocallyFiniteMeasure_polymerMeasure ϑ N s t ω)
    have h := integral_slabCompactPiTensorTest
      (polymerMeasure ϑ N s t ω) hSigma φ
    have hpair : slabPairingTensorFunctional φ (polymerRadonMeasure ϑ N s t ω) =
        ∏ i, ∫ p, φ i p ∂polymerMeasure ϑ N s t ω := by
      simp [slabPairingTensorFunctional, RandomMeasure.vaguePairing, polymerRadonMeasure]
    have hinner : ∫ q, Fφ q ∂
        (Measure.pi fun _ : Fin 2 => polymerMeasure ϑ N s t ω) =
        ∏ i, ∫ p, φ i p ∂polymerMeasure ϑ N s t ω := by
      simpa only [Fφ, slabCompactPiTensorTest_apply] using h
    exact hpair.trans hinner.symm
  have hψSource :
      (fun N => ∫ ω, slabPairingTensorFunctional ψ
        (polymerRadonMeasure ϑ N r u ω) ∂disorderLaw) =
      (fun N => ∫ ω, ∫ q, Fψ q ∂
        (Measure.pi fun _ : Fin 2 => polymerMeasure ϑ N r u ω) ∂disorderLaw) := by
    funext N
    apply integral_congr_ae
    filter_upwards [] with ω
    have hSigma : SigmaFinite (polymerMeasure ϑ N r u ω) :=
      @MeasureTheory.sigmaFinite_of_locallyFinite (Plane × Plane) _
        (polymerMeasure ϑ N r u ω) inferInstance inferInstance
        (isLocallyFiniteMeasure_polymerMeasure ϑ N r u ω)
    have h := integral_slabCompactPiTensorTest
      (polymerMeasure ϑ N r u ω) hSigma ψ
    have hpair : slabPairingTensorFunctional ψ (polymerRadonMeasure ϑ N r u ω) =
        ∏ i, ∫ p, ψ i p ∂polymerMeasure ϑ N r u ω := by
      simp [slabPairingTensorFunctional, RandomMeasure.vaguePairing, polymerRadonMeasure]
    have hinner : ∫ q, Fψ q ∂
        (Measure.pi fun _ : Fin 2 => polymerMeasure ϑ N r u ω) =
        ∏ i, ∫ p, ψ i p ∂polymerMeasure ϑ N r u ω := by
      simpa only [Fψ, slabCompactPiTensorTest_apply] using h
    exact hpair.trans hinner.symm
  have hφLimit : Tendsto
      (fun N => ∫ ω, slabPairingTensorFunctional φ
        (polymerRadonMeasure ϑ N s t ω) ∂disorderLaw)
      atTop (nhds (∫ x : Configuration 2, ∫ y : Configuration 2,
        (∏ i, φ i (x i, y i)) *
          (momentKernel 2 (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal)) := by
    rw [hφSource]
    simpa only [Fφ, slabCompactPiTensorTest_apply] using hφPi
  have hψLimit : Tendsto
      (fun N => ∫ ω, slabPairingTensorFunctional ψ
        (polymerRadonMeasure ϑ N r u ω) ∂disorderLaw)
      atTop (nhds (∫ x : Configuration 2, ∫ y : Configuration 2,
        (∏ i, ψ i (x i, y i)) *
          (momentKernel 2 (ϑ - Real.eulerMascheroniConstant) (u - r) x y).toReal)) := by
    rw [hψSource]
    simpa only [Fψ, slabCompactPiTensorTest_apply] using hψPi
  have hfact (N : ℕ) :
      ∫ ω,
        slabPairingTensorFunctional φ (polymerRadonMeasure ϑ N s t ω) *
          slabPairingTensorFunctional ψ (polymerRadonMeasure ϑ N r u ω)
          ∂disorderLaw =
        (∫ ω, slabPairingTensorFunctional φ
          (polymerRadonMeasure ϑ N s t ω) ∂disorderLaw) *
        (∫ ω, slabPairingTensorFunctional ψ
          (polymerRadonMeasure ϑ N r u ω) ∂disorderLaw) := by
    exact (hIndep N).integral_fun_mul_eq_mul_integral
      (hAmeas N).aestronglyMeasurable (hBmeas N).aestronglyMeasurable
  have hfun :
      (fun N => ∫ ω,
        slabPairingTensorFunctional φ (polymerRadonMeasure ϑ N s t ω) *
          slabPairingTensorFunctional ψ (polymerRadonMeasure ϑ N r u ω)
          ∂disorderLaw) =
        (fun N => (∫ ω, slabPairingTensorFunctional φ
          (polymerRadonMeasure ϑ N s t ω) ∂disorderLaw) *
          (∫ ω, slabPairingTensorFunctional ψ
          (polymerRadonMeasure ϑ N r u ω) ∂disorderLaw)) := by
    funext N
    exact hfact N
  rw [hfun]
  exact hφLimit.mul hψLimit

end Critical2DKPZ.SHF.Flow

end
