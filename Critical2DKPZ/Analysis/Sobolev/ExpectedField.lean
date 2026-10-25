/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.HeatMoments
public import Critical2DKPZ.Analysis.Sobolev.SpatialQuadratic

/-!
# Expected local Sobolev energy through two-point moments

Joint measurability and finite second moment of the localized L¹ norm justify the spatial
expectation interchange in the Gamma representation used in the proof of Lemma 6.4 of
*The Critical 2D KPZ Process*.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ

/-- A jointly measurable locally integrable field gives weakly measurable distributions. -/
theorem measurable_ofFun_evaluation {Ω : Type*} [MeasurableSpace Ω] {X : Ω → Plane → ℝ}
    (hX : Measurable (fun p : Ω × Plane => X p.1 p.2))
    (hXi : ∀ ω, LocallyIntegrable (X ω) volume) (φ : TestFn) :
    Measurable (fun ω => Distribution.ofFun (⊤ : TopologicalSpace.Opens Plane) (X ω) volume ⊤ φ) := by
  have hm : Measurable (fun p : Ω × Plane => φ p.2 * X p.1 p.2) :=
    (φ.continuous.measurable.comp measurable_snd).mul hX
  have he : (fun ω => Distribution.ofFun (⊤ : TopologicalSpace.Opens Plane) (X ω) volume ⊤ φ) =
      fun ω => ∫ x : Plane, φ x * X ω x := by
    funext ω
    simpa only [smul_eq_mul] using Distribution.ofFun_apply ((hXi ω).locallyIntegrableOn _)
  rw [he]
  exact hm.stronglyMeasurable.integral_prod_right.measurable

/-- The expected heat-damped Fourier energy equals its spatial two-point moment pairing. -/
theorem lintegral_heatDampedFourierEnergy_ofFun {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {X : Ω → Plane → ℝ}
    (hX : Measurable (fun p : Ω × Plane => X p.1 p.2))
    (hXi : ∀ ω, LocallyIntegrable (X ω) volume) (χ : TestFn)
    (hX2 : MemLp (fun ω => ∫ x : Plane, ‖χ x * X ω x‖) 2 μ)
    {u : ℝ} (hu : 0 < u) :
    (∫⁻ ω, heatDampedFourierEnergy u
      (Distribution.ofFun (⊤ : TopologicalSpace.Opens Plane) (X ω) volume ⊤) χ ∂μ) =
      ENNReal.ofReal (∫ p : Plane × Plane,
        (heatKernel (2 * u) (p.1 - p.2) * (χ p.1 * χ p.2) *
          ∫ ω, X ω p.1 * X ω p.2 ∂μ) ∂volume.prod volume) := by
  let F : Ω → Plane → ℝ := fun ω x => χ x * X ω x
  have hF : Measurable (fun p : Ω × Plane => F p.1 p.2) :=
    (χ.continuous.measurable.comp measurable_snd).mul hX
  have hF1 (ω : Ω) : Integrable (F ω) := by
    simpa only [smul_eq_mul] using (hXi ω).integrable_smul_left_of_hasCompactSupport
      χ.continuous χ.hasCompactSupport
  have hQ : Integrable (fun ω => spatialHeatQuadratic u (F ω)) μ :=
    (integrable_field_heat_product μ hF hF1 hX2 hu).integral_prod_left
  have hQnn : 0 ≤ᵐ[μ] (fun ω => spatialHeatQuadratic u (F ω)) :=
    Filter.Eventually.of_forall fun ω => spatialHeatQuadratic_nonneg hu (hF1 ω)
  simp_rw [heatDampedFourierEnergy_ofFun_eq_spatialHeatQuadratic hu (hXi _)]
  rw [← ofReal_integral_eq_lintegral_ofReal hQ hQnn]
  unfold spatialHeatQuadratic
  rw [integral_field_heat_quadratic μ hF hF1 hX2 hu]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with p
  have he : (fun ω => F ω p.1 * F ω p.2) =
      fun ω => (χ p.1 * χ p.2) * (X ω p.1 * X ω p.2) := by
    funext ω
    dsimp only [F]
    ring
  rw [he, integral_const_mul]
  ring

/-- The expected local negative Sobolev energy equals a Gamma mixture of spatial two-point moments. -/
theorem lintegral_localNegSobolevSq_ofFun_eq_moment_representation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] {X : Ω → Plane → ℝ}
    (hX : Measurable (fun p : Ω × Plane => X p.1 p.2))
    (hXi : ∀ ω, LocallyIntegrable (X ω) volume) (χ : TestFn)
    (hX2 : MemLp (fun ω => ∫ x : Plane, ‖χ x * X ω x‖) 2 μ)
    {a : ℝ} (ha : 0 < a) :
    (∫⁻ ω, localNegSobolevSq a
      (Distribution.ofFun (⊤ : TopologicalSpace.Opens Plane) (X ω) volume ⊤) χ ∂μ) =
      ENNReal.ofReal (Real.Gamma a)⁻¹ *
        ∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (u ^ (a - 1) * Real.exp (-u)) *
          ENNReal.ofReal (∫ p : Plane × Plane,
            (heatKernel (2 * u) (p.1 - p.2) * (χ p.1 * χ p.2) *
              ∫ ω, X ω p.1 * X ω p.2 ∂μ) ∂volume.prod volume) := by
  rw [lintegral_localNegSobolevSq_eq_gamma_mixture μ
    (measurable_ofFun_evaluation hX hXi) ha χ]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [lintegral_heatDampedFourierEnergy_ofFun μ hX hXi χ hX2 hu]

/-- For a centered random field, the two-point moment is exactly its covariance. -/
theorem lintegral_localNegSobolevSq_ofFun_eq_covariance_representation
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] {X : Ω → Plane → ℝ}
    (hX : Measurable (fun p : Ω × Plane => X p.1 p.2))
    (hXi : ∀ ω, LocallyIntegrable (X ω) volume) (χ : TestFn)
    (hX2 : MemLp (fun ω => ∫ x : Plane, ‖χ x * X ω x‖) 2 μ)
    (hzero : ∀ x : Plane, (∫ ω, X ω x ∂μ) = 0) {a : ℝ} (ha : 0 < a) :
    (∫⁻ ω, localNegSobolevSq a
      (Distribution.ofFun (⊤ : TopologicalSpace.Opens Plane) (X ω) volume ⊤) χ ∂μ) =
      ENNReal.ofReal (Real.Gamma a)⁻¹ *
        ∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (u ^ (a - 1) * Real.exp (-u)) *
          ENNReal.ofReal (∫ p : Plane × Plane,
            (heatKernel (2 * u) (p.1 - p.2) * (χ p.1 * χ p.2) *
              ProbabilityTheory.covariance (fun ω => X ω p.1) (fun ω => X ω p.2) μ)
                ∂volume.prod volume) := by
  simp_rw [ProbabilityTheory.covariance, hzero, sub_zero]
  exact lintegral_localNegSobolevSq_ofFun_eq_moment_representation μ hX hXi χ hX2 ha

end Critical2DKPZ

end
