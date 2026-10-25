/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SchwartzPairingContinuity
public import Critical2DKPZ.Extensions.ScaleLimit.JointLpRepresentative
public import Critical2DKPZ.Spectral.BochnerSchwartzSquareCone
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic

/-! # Jointly measurable stationary Schwartz fields

The stochastic Schwartz extension admits jointly measurable field versions.
The construction preserves finite-dimensional stationarity, including for
Schwartz differences. No pathwise smoothness is needed for the maximal inequality.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Exactly the three properties produced by the stochastic Schwartz extension. -/
def SchwartzExtensionSpec {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : Ω → Distr) (ν : Measure Plane) (E : SchwartzMap Plane ℝ →ₗ[ℝ] Lp ℝ 2 P) : Prop :=
  (∀ f : TestFn, (E (Spectral.testFnToRealSchwartz f) : Ω → ℝ) =ᵐ[P] fun ω => D ω f) ∧
  (∀ f g, (∫ ω, E f ω * E g ω ∂P) =
    ∫ ξ, (Spectral.fourierKPZ f ξ * star (Spectral.fourierKPZ g ξ)).re ∂ν) ∧
  (∀ (n : ℕ) (f : Fin n → SchwartzMap Plane ℝ) (z : Plane),
    IdentDistrib (fun ω i => E (translateSchwartz z (f i)) ω) (fun ω i => E (f i) ω) P P)

/-- Continuity of an `L²`-valued map implies convergence in measure of its representatives. -/
theorem tendstoInMeasure_of_continuous_Lp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Plane → Lp ℝ 2 P) (hf : Continuous f) (y₀ : Plane) :
    TendstoInMeasure P (fun y ω => f y ω) (𝓝 y₀) (fun ω => f y₀ ω) := by
  have hn : Tendsto (fun y => ‖f y - f y₀‖) (𝓝 y₀) (𝓝 0) := by
    simpa only [sub_self, norm_zero] using ((hf.continuousAt (x := y₀)).tendsto.sub_const (f y₀)).norm
  have he : Tendsto (fun y => eLpNorm ((f y : Ω → ℝ) - (f y₀ : Ω → ℝ)) 2 P)
      (𝓝 y₀) (𝓝 0) := by
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hn
    simp only [ENNReal.ofReal_zero] at hh
    convert hh using 1
    funext y
    rw [← eLpNorm_congr_ae (Lp.coeFn_sub (f y) (f y₀)), ← Lp.enorm_def]
    exact (ofReal_norm _).symm
  exact tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) he

/-- A Schwartz test has a jointly measurable stationary field version, continuous in probability. -/
theorem exists_schwartz_field {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Ω → Distr) (ν : Measure Plane)
    (hD : StationarySpectralData P D ν) (E : SchwartzMap Plane ℝ →ₗ[ℝ] Lp ℝ 2 P)
    (hE : SchwartzExtensionSpec P D ν E) (ψ : SchwartzMap Plane ℝ) :
    ∃ F : Plane → Ω → ℝ, Measurable (Function.uncurry F) ∧
      (∀ y, F y =ᵐ[P] fun ω => E (translateSchwartz y ψ) ω) ∧
      (∀ (n : ℕ) (y : Fin n → Plane) (z : Plane),
        IdentDistrib (fun ω i => F (y i + z) ω) (fun ω i => F (y i) ω) P P) ∧
      (∀ y₀, TendstoInMeasure P F (𝓝 y₀) (F y₀)) := by
  let : ν.HasTemperateGrowth := temperateGrowth_of_spectralData P D ν hD
  have hc := continuous_schwartzPairing_translate P ν E hE.2.1 ψ
  obtain ⟨F, hFm, hFeq⟩ := exists_jointlyMeasurable_Lp_version P _ hc
  refine ⟨F, hFm, hFeq, ?_, ?_⟩
  · intro n y z
    have hleft : (fun ω i => F (y i + z) ω) =ᵐ[P]
        (fun ω i => E (translateSchwartz (y i + z) ψ) ω) := by
      filter_upwards [ae_all_iff.mpr (fun i : Fin n => hFeq (y i + z))] with ω hω
      exact funext hω
    have hright : (fun ω i => F (y i) ω) =ᵐ[P]
        (fun ω i => E (translateSchwartz (y i) ψ) ω) := by
      filter_upwards [ae_all_iff.mpr (fun i : Fin n => hFeq (y i))] with ω hω
      exact funext hω
    have hs : IdentDistrib (fun ω i => E (translateSchwartz (y i + z) ψ) ω)
        (fun ω i => E (translateSchwartz (y i) ψ) ω) P P := by
      simpa only [translateSchwartz_add, add_comm z] using
        hE.2.2 n (fun i => translateSchwartz (y i) ψ) z
    have hmleft : AEMeasurable (fun ω i => F (y i + z) ω) P :=
      (Measurable.of_eval (fun i => hFm.of_uncurry_left)).aemeasurable
    have hmright : AEMeasurable (fun ω i => F (y i) ω) P :=
      (Measurable.of_eval (fun i => hFm.of_uncurry_left)).aemeasurable
    exact (IdentDistrib.of_ae_eq hmleft hleft).trans
      (hs.trans (IdentDistrib.of_ae_eq hmright hright).symm)
  · intro y₀
    exact (tendstoInMeasure_of_continuous_Lp P _ hc y₀).congr
      (fun y => (hFeq y).symm) (hFeq y₀).symm

/-- A chosen jointly measurable version of the Schwartz pairing field. -/
def schwartzFieldOfExtension {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Ω → Distr) (ν : Measure Plane)
    (hD : StationarySpectralData P D ν) (E : SchwartzMap Plane ℝ →ₗ[ℝ] Lp ℝ 2 P)
    (hE : SchwartzExtensionSpec P D ν E) (ψ : SchwartzMap Plane ℝ) : Plane → Ω → ℝ :=
  Classical.choose (exists_schwartz_field P D ν hD E hE ψ)

/-- Joint measurability of the chosen version. -/
theorem measurable_schwartzFieldOfExtension {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Ω → Distr) (ν : Measure Plane)
    (hD : StationarySpectralData P D ν) (E : SchwartzMap Plane ℝ →ₗ[ℝ] Lp ℝ 2 P)
    (hE : SchwartzExtensionSpec P D ν E) (ψ : SchwartzMap Plane ℝ) :
    Measurable (Function.uncurry (schwartzFieldOfExtension P D ν hD E hE ψ)) :=
  (Classical.choose_spec (exists_schwartz_field P D ν hD E hE ψ)).1

/-- Identification of the chosen version at each fixed spatial point. -/
theorem schwartzFieldOfExtension_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Ω → Distr) (ν : Measure Plane)
    (hD : StationarySpectralData P D ν) (E : SchwartzMap Plane ℝ →ₗ[ℝ] Lp ℝ 2 P)
    (hE : SchwartzExtensionSpec P D ν E) (ψ : SchwartzMap Plane ℝ) (y : Plane) :
    schwartzFieldOfExtension P D ν hD E hE ψ y =ᵐ[P] fun ω => E (translateSchwartz y ψ) ω :=
  (Classical.choose_spec (exists_schwartz_field P D ν hD E hE ψ)).2.1 y

/-- Finite-dimensional translation invariance of the chosen version. -/
theorem schwartzFieldOfExtension_stationary {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Ω → Distr) (ν : Measure Plane)
    (hD : StationarySpectralData P D ν) (E : SchwartzMap Plane ℝ →ₗ[ℝ] Lp ℝ 2 P)
    (hE : SchwartzExtensionSpec P D ν E) (ψ : SchwartzMap Plane ℝ)
    (n : ℕ) (y : Fin n → Plane) (z : Plane) :
    IdentDistrib (fun ω i => schwartzFieldOfExtension P D ν hD E hE ψ (y i + z) ω)
      (fun ω i => schwartzFieldOfExtension P D ν hD E hE ψ (y i) ω) P P :=
  (Classical.choose_spec (exists_schwartz_field P D ν hD E hE ψ)).2.2.1 n y z

/-- Continuity in probability of the chosen version. -/
theorem schwartzFieldOfExtension_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Ω → Distr) (ν : Measure Plane)
    (hD : StationarySpectralData P D ν) (E : SchwartzMap Plane ℝ →ₗ[ℝ] Lp ℝ 2 P)
    (hE : SchwartzExtensionSpec P D ν E) (ψ : SchwartzMap Plane ℝ) (y₀ : Plane) :
    TendstoInMeasure P (schwartzFieldOfExtension P D ν hD E hE ψ) (𝓝 y₀)
      (schwartzFieldOfExtension P D ν hD E hE ψ y₀) :=
  (Classical.choose_spec (exists_schwartz_field P D ν hD E hE ψ)).2.2.2 y₀

/-- The band field is the Schwartz field of the band kernel at the origin. -/
def bandFieldOfExtension {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Ω → Distr) (ν : Measure Plane)
    (hD : StationarySpectralData P D ν) (E : SchwartzMap Plane ℝ →ₗ[ℝ] Lp ℝ 2 P)
    (hE : SchwartzExtensionSpec P D ν E) (a : ℝ) : Plane → Ω → ℝ :=
  schwartzFieldOfExtension P D ν hD E hE (zetaScaled a 0)

/-- Identification of the band field at each fixed point. -/
theorem bandFieldOfExtension_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (D : Ω → Distr) (ν : Measure Plane)
    (hD : StationarySpectralData P D ν) (E : SchwartzMap Plane ℝ →ₗ[ℝ] Lp ℝ 2 P)
    (hE : SchwartzExtensionSpec P D ν E) (a : ℝ) (y : Plane) :
    bandFieldOfExtension P D ν hD E hE a y =ᵐ[P] fun ω => E (zetaScaled a y) ω := by
  change schwartzFieldOfExtension P D ν hD E hE (zetaScaled a 0) y =ᵐ[P] _
  have hh := schwartzFieldOfExtension_ae_eq P D ν hD E hE (zetaScaled a 0) y
  convert hh using 1
  rw [← zetaScaled_eq_translate a y]

end Critical2DKPZ.Extensions.ScaleLimit
