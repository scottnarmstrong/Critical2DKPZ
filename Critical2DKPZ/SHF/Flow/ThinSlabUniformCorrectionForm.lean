/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.TwoParticleEndpointForms

/-! # Uniform logarithmic bounds for the endpoint correction -/

@[expose] public noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.DeltaBose
open scoped ENNReal Topology

namespace Critical2DKPZ.SHF.Flow

/-- The constant in the endpoint correction bound is uniform in both outer durations, the
slab width, the parameter below `B`, and the endpoint functions. -/
theorem exists_slabMomentKernelTwo_uniform_correction_endpoint_bound (B T : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (θ r t v : ℝ), θ ≤ B →
      0 ≤ r → r ≤ T → 0 ≤ t → t ≤ T → 0 < v → v ≤ 1 / 2 →
      ∀ f g : Configuration 2 → ℝ≥0∞, Measurable f → Measurable g →
      slabMomentKernelTwoCorrectionEndpointForm θ r v t f g ≤
        C * ENNReal.ofReal (1 / (1 + Real.log v⁻¹)) *
          (∫⁻ x : Configuration 2, f x ^ 2) ^ (1 / 2 : ℝ) *
          (∫⁻ x : Configuration 2, g x ^ 2) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := exists_twoParticle_weighted_cancellation_bound B 0 T (by norm_num)
  refine ⟨C, hC, fun θ r t v hθ hr hrT ht htT hv hvhalf f g hf hg => ?_⟩
  let A : Configuration 2 → ℝ≥0∞ := fun x =>
    twoParticleWeightedAction θ 0 r
      (twoParticleCorrectionWeightedAction θ 0 v (twoParticleWeightedAction θ 0 t f)) x
  have hA : Measurable A := by
    dsimp [A]
    exact measurable_twoParticleWeightedAction θ 0 r
      (measurable_twoParticleCorrectionWeightedAction θ 0 v
        (measurable_twoParticleWeightedAction θ 0 t hf))
  have hsq := hbound θ r t v hθ hr hrT ht htT hv hvhalf f hf
  have hroot :
      (∫⁻ x : Configuration 2, A x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        C * ENNReal.ofReal (1 / (1 + Real.log v⁻¹)) *
          (∫⁻ x : Configuration 2, f x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ ((C * ENNReal.ofReal (1 / (1 + Real.log v⁻¹))) ^ 2 *
          ∫⁻ x : Configuration 2, f x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        apply ENNReal.monotone_rpow_of_nonneg (by norm_num)
        simpa only [ENNReal.rpow_two] using hsq
      _ = C * ENNReal.ofReal (1 / (1 + Real.log v⁻¹)) *
          (∫⁻ x : Configuration 2, f x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        rw [← ENNReal.rpow_natCast_mul]
        norm_num
  have hHolder :
      (∫⁻ x : Configuration 2, A x * g x) ≤
        (∫⁻ x : Configuration 2, A x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫⁻ x : Configuration 2, g x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
      hA.aemeasurable hg.aemeasurable
  have hbound' :
      (∫⁻ x : Configuration 2, A x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫⁻ x : Configuration 2, g x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
        C * ENNReal.ofReal (1 / (1 + Real.log v⁻¹)) *
          (∫⁻ x : Configuration 2, f x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫⁻ x : Configuration 2, g x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_right hroot (by positivity)
  have hresult := hHolder.trans (by simpa only [ENNReal.rpow_two] using hbound')
  calc
    slabMomentKernelTwoCorrectionEndpointForm θ r v t f g =
        ∫⁻ x : Configuration 2, A x * g x := by
      unfold slabMomentKernelTwoCorrectionEndpointForm
      apply lintegral_congr
      intro x
      exact mul_comm _ _
    _ ≤ _ := hresult


/-- For fixed finite square norms, the collision correction tends to zero uniformly over both
outer durations in a bounded window and all parameters below `B`. -/
theorem slabMomentKernelTwo_correction_endpoint_uniformly_small (B T : ℝ)
    {f g : Configuration 2 → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hf2 : (∫⁻ x, f x ^ 2) ≠ ⊤) (hg2 : (∫⁻ x, g x ^ 2) ≠ ⊤) :
    ∀ ε : ℝ, 0 < ε → ∃ v₀ > 0, ∀ θ r t v : ℝ, θ ≤ B →
      0 ≤ r → r ≤ T → 0 ≤ t → t ≤ T → 0 < v → v < v₀ →
      slabMomentKernelTwoCorrectionEndpointForm θ r v t f g ≤ ENNReal.ofReal ε := by
  obtain ⟨C, hC, hbound⟩ := exists_slabMomentKernelTwo_uniform_correction_endpoint_bound B T
  let F : ℝ≥0∞ := (∫⁻ x, f x ^ 2) ^ (1 / 2 : ℝ)
  let G : ℝ≥0∞ := (∫⁻ x, g x ^ 2) ^ (1 / 2 : ℝ)
  have hF : F ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hf2
  have hG : G ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hg2
  have hlog : Tendsto (fun v : ℝ => ENNReal.ofReal (1 / (1 + Real.log v⁻¹)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp tendsto_slab_inverseLog_nhdsGT_zero
  have hlimit : Tendsto
      (fun v : ℝ => C * ENNReal.ofReal (1 / (1 + Real.log v⁻¹)) * F * G)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      ENNReal.Tendsto.mul_const
        (ENNReal.Tendsto.mul_const (ENNReal.Tendsto.const_mul hlog (Or.inr hC))
          (Or.inr hF)) (Or.inr hG)
  intro ε hε
  have hsmall := hlimit.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))
  obtain ⟨v₁, hv₁, hinterval⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hsmall
  refine ⟨min v₁ (1 / 2), lt_min hv₁ (by norm_num), ?_⟩
  intro θ r t v hθ hr hrT ht htT hv hv₀
  have hv₁' : v < v₁ := hv₀.trans_le (min_le_left _ _)
  have hvhalf : v ≤ 1 / 2 := hv₀.le.trans (min_le_right _ _)
  exact (hbound θ r t v hθ hr hrT ht htT hv hvhalf f g hf hg).trans
    (hinterval ⟨hv, hv₁'⟩).le

end Critical2DKPZ.SHF.Flow

end
