/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.ExpectedField
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Joint measurability and uniform pointwise second moments control localized L¹ second moments and justify the covariance representation. -/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ

/-- Uniform pointwise second moments control the absolute two-point moment. -/
theorem lintegral_norm_mul_le_second_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {X Y : Ω → ℝ} (hX : Measurable X)
    {C : ℝ≥0∞} (hXC : (∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂μ) ≤ C)
    (hYC : (∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂μ) ≤ C) :
    (∫⁻ ω, ENNReal.ofReal (‖X ω * Y ω‖) ∂μ) ≤ C + C := by
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (X ω ^ 2) + ENNReal.ofReal (Y ω ^ 2) ∂μ := by
      apply lintegral_mono
      intro ω
      change ENNReal.ofReal (‖X ω * Y ω‖) ≤ ENNReal.ofReal (X ω ^ 2) + ENNReal.ofReal (Y ω ^ 2)
      rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      rw [Real.norm_eq_abs, abs_mul]
      have hsq := sq_nonneg (|X ω| - |Y ω|)
      have hxy := mul_nonneg (abs_nonneg (X ω)) (abs_nonneg (Y ω))
      nlinarith only [hsq, hxy, sq_abs (X ω), sq_abs (Y ω)]
    _ = (∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂μ) +
        ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂μ :=
      lintegral_add_left (hX.pow_const 2).ennreal_ofReal _
    _ ≤ _ := add_le_add hXC hYC

/-- The localized L¹ norm has finite second moment under a uniform pointwise second-moment bound. -/
theorem memLp_localized_L1_norm_of_uniform_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {X : Ω → Plane → ℝ}
    (hX : Measurable (fun p : Ω × Plane => X p.1 p.2))
    (hXi : ∀ ω, LocallyIntegrable (X ω) volume) (χ : TestFn)
    {C : ℝ≥0∞} (hC : C < ⊤)
    (hXC : ∀ x : Plane, (∫⁻ ω, ENNReal.ofReal (X ω x ^ 2) ∂μ) ≤ C) :
    MemLp (fun ω => ∫ x : Plane, ‖χ x * X ω x‖) 2 μ := by
  have hm : Measurable (fun p : Ω × Plane => ‖χ p.2 * X p.1 p.2‖) :=
    ((χ.continuous.measurable.comp measurable_snd).mul hX).norm
  have hi (ω : Ω) : Integrable (fun x => χ x * X ω x) := by
    simpa only [smul_eq_mul] using (hXi ω).integrable_smul_left_of_hasCompactSupport
      χ.continuous χ.hasCompactSupport
  have he (ω : Ω) : ENNReal.ofReal ((∫ x : Plane, ‖χ x * X ω x‖) ^ 2) =
      ∫⁻ p : Plane × Plane,
        ENNReal.ofReal (‖χ p.1 * X ω p.1‖) * ENNReal.ofReal (‖χ p.2 * X ω p.2‖)
          ∂volume.prod volume := by
    rw [ENNReal.ofReal_pow (integral_nonneg fun _ => norm_nonneg _), pow_two,
      ofReal_integral_eq_lintegral_ofReal (hi ω).norm
        (Filter.Eventually.of_forall fun _ => norm_nonneg _)]
    exact (lintegral_prod_mul ((hm.comp measurable_prodMk_left).ennreal_ofReal.aemeasurable)
      ((hm.comp measurable_prodMk_left).ennreal_ofReal.aemeasurable)).symm
  have hmp : Measurable (fun p : Ω × (Plane × Plane) =>
      ENNReal.ofReal (‖χ p.2.1 * X p.1 p.2.1‖) *
        ENNReal.ofReal (‖χ p.2.2 * X p.1 p.2.2‖)) :=
    ((hm.comp (measurable_fst.prodMk measurable_snd.fst)).ennreal_ofReal).mul
      ((hm.comp (measurable_fst.prodMk measurable_snd.snd)).ennreal_ofReal)
  have hb (p : Plane × Plane) :
      (∫⁻ ω, ENNReal.ofReal (‖χ p.1 * X ω p.1‖) *
        ENNReal.ofReal (‖χ p.2 * X ω p.2‖) ∂μ) ≤
        (ENNReal.ofReal ‖χ p.1‖ * ENNReal.ofReal ‖χ p.2‖) * (C + C) := by
    have hf : (fun ω => ENNReal.ofReal (‖χ p.1 * X ω p.1‖) *
        ENNReal.ofReal (‖χ p.2 * X ω p.2‖)) =
        fun ω => (ENNReal.ofReal ‖χ p.1‖ * ENNReal.ofReal ‖χ p.2‖) *
          ENNReal.ofReal ‖X ω p.1 * X ω p.2‖ := by
      funext ω
      simp only [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
      ring
    rw [hf, lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
    exact mul_le_mul' le_rfl (lintegral_norm_mul_le_second_moments μ
      (hX.comp measurable_prodMk_right) (hXC p.1) (hXC p.2))
  have hχm := χ.continuous.norm.measurable.ennreal_ofReal
  have hχfin : (∫⁻ x : Plane, ENNReal.ofReal ‖χ x‖) < ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (χ.continuous.integrable_of_hasCompactSupport χ.hasCompactSupport).norm
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)]
    exact ENNReal.ofReal_lt_top
  have hfin : (∫⁻ ω, ENNReal.ofReal ((∫ x : Plane, ‖χ x * X ω x‖) ^ 2) ∂μ) < ⊤ := by
    simp_rw [he]
    rw [lintegral_lintegral_swap hmp.aemeasurable]
    apply lt_of_le_of_lt (lintegral_mono hb)
    rw [lintegral_mul_const' _ _ (ENNReal.add_lt_top.mpr ⟨hC, hC⟩).ne,
      lintegral_prod_mul hχm.aemeasurable hχm.aemeasurable]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hχfin hχfin) (ENNReal.add_lt_top.mpr ⟨hC, hC⟩)
  apply (memLp_two_iff_integrable_sq
    hm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable).mpr
  exact (lintegral_ofReal_ne_top_iff_integrable
    (hm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable.pow 2)
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)).mp hfin.ne

/-- A jointly measurable centred field with uniformly bounded pointwise second moments has expected local Sobolev energy given by its spatial covariance pairing. -/
theorem lintegral_localNegSobolevSq_ofFun_eq_covariance_of_uniform_second_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] {X : Ω → Plane → ℝ}
    (hX : Measurable (fun p : Ω × Plane => X p.1 p.2))
    (hXi : ∀ ω, LocallyIntegrable (X ω) volume) (χ : TestFn)
    {C : ℝ≥0∞} (hC : C < ⊤)
    (hXC : ∀ x : Plane, (∫⁻ ω, ENNReal.ofReal (X ω x ^ 2) ∂μ) ≤ C)
    (hzero : ∀ x : Plane, (∫ ω, X ω x ∂μ) = 0) {a : ℝ} (ha : 0 < a) :
    (∫⁻ ω, localNegSobolevSq a
      (Distribution.ofFun (⊤ : TopologicalSpace.Opens Plane) (X ω) volume ⊤) χ ∂μ) =
      ENNReal.ofReal (Real.Gamma a)⁻¹ *
        ∫⁻ u : ℝ in Ioi 0, ENNReal.ofReal (u ^ (a - 1) * Real.exp (-u)) *
          ENNReal.ofReal (∫ p : Plane × Plane,
            (heatKernel (2 * u) (p.1 - p.2) * (χ p.1 * χ p.2) *
              ProbabilityTheory.covariance (fun ω => X ω p.1) (fun ω => X ω p.2) μ)
                ∂volume.prod volume) := by
  exact lintegral_localNegSobolevSq_ofFun_eq_covariance_representation μ hX hXi χ
    (memLp_localized_L1_norm_of_uniform_second_moment μ hX hXi χ hC hXC) hzero ha

end Critical2DKPZ

end
