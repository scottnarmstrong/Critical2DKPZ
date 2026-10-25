/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.TwoIncrementNonlinearLimits
public import Critical2DKPZ.SHF.Tsai.HybridLimits

/-! # Two-block expectation limits at hybrid endpoints

The original and replaced two-block expectations converge to the endpoint hybrid value
and its adjacent interior hybrid limit.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- The original and replaced two-block expectations at the initial endpoint have the corresponding hybrid limits. -/
theorem exists_hybrid_leftEndpoint_limits {θ : ℝ} (D : Set ℝ) {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsDenseSHF θ D P Z) (hZ' : IsDenseSHF θ D P' Z')
    {s b t : ℝ} (hs : s ∈ D) (hb : b ∈ D) (ht : t ∈ D) (hsb : s < b) (hbt : b < t)
    {m r : ℕ} (g g' : Fin m → Fin r → C_c(Plane, ℝ))
    (H : (Fin m → ℝ) → ℝ) (hH : Continuous H) (CH : ℝ) (hCH : ∀ z, ‖H z‖ ≤ CH) :
    ∃ Lb : ℝ,
      Tendsto (fun ℓ => hybridValue P P' Z Z' s t g g' H b ℓ) atTop (𝓝 Lb) ∧
      Tendsto (fun ℓ => ∫ ω : Ω' × Ω, H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2
        ∂smoothedProductMeasure (Z s b ω.2) (heatMollifier ℓ) (Z b t ω.2)) ∂P'.prod P)
        atTop (𝓝 (hybridValue P P' Z Z' s t g g' H s 0)) ∧
      Tendsto (fun ℓ => ∫ ω : Ω' × Ω, H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2
        ∂smoothedProductMeasure (Z' s b ω.1) (heatMollifier ℓ) (Z b t ω.2)) ∂P'.prod P)
        atTop (𝓝 Lb) ∧
      (∀ ℓ, Integrable (fun ω : Ω' × Ω => H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2
        ∂smoothedProductMeasure (Z s b ω.2) (heatMollifier ℓ) (Z b t ω.2))) (P'.prod P)) ∧
      (∀ ℓ, Integrable (fun ω : Ω' × Ω => H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2
        ∂smoothedProductMeasure (Z' s b ω.1) (heatMollifier ℓ) (Z b t ω.2))) (P'.prod P)) := by
  obtain ⟨Lb, hRepI, hRep⟩ := exists_hybridPairing_integral_limit D P P' Z Z' hZ hZ'
    hs hb ht hsb hbt g g' H hH CH hCH
  have hOrig := hZ.tendsto_integral_comp_smoothedProduct P Z hs hb ht hsb hbt
    heatMollifier isL2ApplicableMollifier_heatMollifier g g' H hH CH hCH
  refine ⟨Lb, ?_, ?_, hRep, ?_, hRepI⟩
  · simp only [hybridValue, ite_eq_right (ne_of_gt hsb), ite_eq_right (ne_of_lt hbt)]
    exact hRep
  · simp only [hybridValue_left]
    have heq (ℓ : ℕ) :
        (∫ ω : Ω' × Ω, H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2
          ∂smoothedProductMeasure (Z s b ω.2) (heatMollifier ℓ) (Z b t ω.2)) ∂P'.prod P) =
        ∫ ω, H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2
          ∂smoothedProductMeasure (Z s b ω) (heatMollifier ℓ) (Z b t ω)) ∂P := by
      simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using
        integral_fun_snd (μ := P') (ν := P) (fun ω => H (fun i => ∑ k, ∫ p,
          g i k p.1 * g' i k p.2 ∂smoothedProductMeasure (Z s b ω) (heatMollifier ℓ) (Z b t ω)))
    simpa only [heq] using hOrig.2
  · intro ℓ
    exact (measurePreserving_snd : MeasurePreserving Prod.snd (P'.prod P) P).integrable_comp_of_integrable
      (hOrig.1 ℓ)

/-- The original and replaced two-block expectations at the terminal endpoint have the corresponding hybrid limits. -/
theorem exists_hybrid_rightEndpoint_limits {θ : ℝ} (D : Set ℝ) {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsDenseSHF θ D P Z) (hZ' : IsDenseSHF θ D P' Z')
    {s a t : ℝ} (hs : s ∈ D) (ha : a ∈ D) (ht : t ∈ D) (hsa : s < a) (hat : a < t)
    {m r : ℕ} (g g' : Fin m → Fin r → C_c(Plane, ℝ))
    (H : (Fin m → ℝ) → ℝ) (hH : Continuous H) (CH : ℝ) (hCH : ∀ z, ‖H z‖ ≤ CH) :
    ∃ La : ℝ,
      Tendsto (fun ℓ => hybridValue P P' Z Z' s t g g' H a ℓ) atTop (𝓝 La) ∧
      Tendsto (fun ℓ => ∫ ω : Ω' × Ω, H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2
        ∂smoothedProductMeasure (Z' s a ω.1) (heatMollifier ℓ) (Z a t ω.2)) ∂P'.prod P)
        atTop (𝓝 La) ∧
      Tendsto (fun ℓ => ∫ ω : Ω' × Ω, H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2
        ∂smoothedProductMeasure (Z' s a ω.1) (heatMollifier ℓ) (Z' a t ω.1)) ∂P'.prod P)
        atTop (𝓝 (hybridValue P P' Z Z' s t g g' H t 0)) ∧
      (∀ ℓ, Integrable (fun ω : Ω' × Ω => H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2
        ∂smoothedProductMeasure (Z' s a ω.1) (heatMollifier ℓ) (Z a t ω.2))) (P'.prod P)) ∧
      (∀ ℓ, Integrable (fun ω : Ω' × Ω => H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2
        ∂smoothedProductMeasure (Z' s a ω.1) (heatMollifier ℓ) (Z' a t ω.1))) (P'.prod P)) := by
  obtain ⟨La, hOrigI, hOrig⟩ := exists_hybridPairing_integral_limit D P P' Z Z' hZ hZ'
    hs ha ht hsa hat g g' H hH CH hCH
  have hRep := hZ'.tendsto_integral_comp_smoothedProduct P' Z' hs ha ht hsa hat
    heatMollifier isL2ApplicableMollifier_heatMollifier g g' H hH CH hCH
  refine ⟨La, ?_, hOrig, ?_, hOrigI, ?_⟩
  · simp only [hybridValue, ite_eq_right (ne_of_gt hsa), ite_eq_right (ne_of_lt hat)]
    exact hOrig
  · rw [hybridValue_right P P' Z Z' (hsa.trans hat)]
    have heq (ℓ : ℕ) :
        (∫ ω : Ω' × Ω, H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2
          ∂smoothedProductMeasure (Z' s a ω.1) (heatMollifier ℓ) (Z' a t ω.1)) ∂P'.prod P) =
        ∫ ω, H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2
          ∂smoothedProductMeasure (Z' s a ω) (heatMollifier ℓ) (Z' a t ω)) ∂P' := by
      simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using
        integral_fun_fst (μ := P') (ν := P) (fun ω => H (fun i => ∑ k, ∫ p,
          g i k p.1 * g' i k p.2 ∂smoothedProductMeasure (Z' s a ω) (heatMollifier ℓ) (Z' a t ω)))
    simpa only [heq] using hRep.2
  · intro ℓ
    exact (measurePreserving_fst : MeasurePreserving Prod.fst (P'.prod P) P').integrable_comp_of_integrable
      (hRep.1 ℓ)

end Critical2DKPZ.SHF.Tsai

end
