/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. Bou-Rabee, Scott Armstrong
Modified for Critical2DKPZ, 2026.
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Rellich.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Fourier.Convolution

/-! Fourier identities and quantitative Sobolev energy bounds for mollification errors.

Adapted from work of A. Bou-Rabee, licensed under Apache 2.0. -/

@[expose] public section

noncomputable section

open MeasureTheory ContinuousLinearMap Set Real
open scoped ENNReal FourierTransform Convolution Pointwise

namespace Critical2DKPZ.Analysis.Sobolev.Rellich

variable {d : ℕ}

/-- Complex coercion commutes with real convolution. -/
theorem ofReal_convolution (φ K : Space d → ℝ)
    (hφ : Continuous φ) (hK : Continuous K)
    (hφc : HasCompactSupport φ) (x : Space d) :
    ((φ ⋆[lsmul ℝ ℝ, volume] K) x : ℂ)
      = ((fun y => (φ y : ℂ)) ⋆[lsmul ℂ ℂ, volume] (fun y => (K y : ℂ))) x := by
  have hcont : Continuous (fun t : Space d => φ t * K (x - t)) :=
    hφ.mul (hK.comp (continuous_const.sub continuous_id))
  have hsupp : Function.support (fun t : Space d => φ t * K (x - t)) ⊆
      Function.support φ := by
    intro t ht
    by_contra h
    rw [Function.mem_support] at ht
    exact ht (by rw [Function.notMem_support.mp h, zero_mul])
  have hc : HasCompactSupport (fun t : Space d => φ t * K (x - t)) := hφc.mono hsupp
  have hint : Integrable (fun t : Space d => φ t * K (x - t)) volume :=
    hcont.integrable_of_hasCompactSupport hc
  rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
  simp only [lsmul_apply, smul_eq_mul]
  have hcongr : (∫ t : Space d, (↑(φ t) : ℂ) * ↑(K (x - t)))
      = ∫ t : Space d, ↑(φ t * K (x - t)) := by
    apply integral_congr_ae
    filter_upwards with t
    rw [Complex.ofReal_mul]
  rw [hcongr]
  exact (ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM hint).symm

/-- The complex coercion of a continuous compactly supported real function is integrable. -/
private theorem integrable_ofReal_of_continuous_hasCompactSupport {f : Space d → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable (fun x => (f x : ℂ)) volume := by
  refine (Complex.continuous_ofReal.comp hf).integrable_of_hasCompactSupport ?_
  exact hfc.mono fun x hx => by
    rw [Function.mem_support] at hx ⊢
    exact fun h => hx (by simp [h])

/-- The Fourier transform preserves differences of integrable functions. -/
theorem fourier_sub_apply (Φ Ψ : Space d → ℂ)
    (hΦ : Integrable Φ volume) (hΨ : Integrable Ψ volume) (ξ : Space d) :
    𝓕 (Φ - Ψ) ξ = 𝓕 Φ ξ - 𝓕 Ψ ξ := by
  rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq]
  rw [← integral_sub]
  · apply integral_congr_ae
    filter_upwards with v
    simp only [Pi.sub_apply, smul_sub]
  · simpa using hΦ
  · simpa using hΨ

/-- The Fourier transform of a real convolution is the product of the complex Fourier transforms. -/
theorem fourier_ofReal_convolution (φ K : Space d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (hφc : HasCompactSupport φ) (hKc : HasCompactSupport K) (ξ : Space d) :
    𝓕 (fun x => (((φ ⋆[lsmul ℝ ℝ, volume] K) x : ℝ) : ℂ)) ξ
      = 𝓕 (fun x => (φ x : ℂ)) ξ * 𝓕 (fun x => (K x : ℂ)) ξ := by
  have hcoe : (fun x => (((φ ⋆[lsmul ℝ ℝ, volume] K) x : ℝ) : ℂ))
      = (fun x => (φ x : ℂ)) ⋆[lsmul ℂ ℂ, volume] (fun x => (K x : ℂ)) :=
    funext fun x => ofReal_convolution φ K hφ.continuous hK.continuous hφc x
  have hφint : Integrable (fun x => (φ x : ℂ)) volume :=
    integrable_ofReal_of_continuous_hasCompactSupport hφ.continuous hφc
  have hKint : Integrable (fun x => (K x : ℂ)) volume :=
    integrable_ofReal_of_continuous_hasCompactSupport hK.continuous hKc
  rw [hcoe, Real.fourier_smul_convolution_eq hφint hKint ξ, smul_eq_mul]

/-- **Fourier transform of the mollification error.**  For smooth compactly supported
`φ, K`,
`𝓕 (↑(φ - φ ⋆ K)) ξ = 𝓕(↑φ) ξ * (1 - 𝓕(↑K) ξ)`. -/
theorem fourier_sub_convolution (φ K : Space d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (hφc : HasCompactSupport φ) (hKc : HasCompactSupport K) (ξ : Space d) :
    𝓕 (fun x => ((φ x - (φ ⋆[lsmul ℝ ℝ, volume] K) x : ℝ) : ℂ)) ξ
      = 𝓕 (fun x => (φ x : ℂ)) ξ * (1 - 𝓕 (fun x => (K x : ℂ)) ξ) := by
  have hφint : Integrable (fun x => (φ x : ℂ)) volume :=
    integrable_ofReal_of_continuous_hasCompactSupport hφ.continuous hφc
  have hconvc : Continuous (φ ⋆[lsmul ℝ ℝ, volume] K) :=
    hKc.continuous_convolution_right (L := lsmul ℝ ℝ) hφ.continuous.locallyIntegrable
      hK.continuous
  have hconvk : HasCompactSupport (φ ⋆[lsmul ℝ ℝ, volume] K) :=
    HasCompactSupport.convolution (L := lsmul ℝ ℝ) (μ := volume) hφc hKc
  have hconvvint : Integrable
      (fun x => (((φ ⋆[lsmul ℝ ℝ, volume] K) x : ℝ) : ℂ)) volume :=
    integrable_ofReal_of_continuous_hasCompactSupport hconvc hconvk
  have hsub : (fun x => ((φ x - (φ ⋆[lsmul ℝ ℝ, volume] K) x : ℝ) : ℂ))
      = (fun x => (φ x : ℂ))
        - fun x => (((φ ⋆[lsmul ℝ ℝ, volume] K) x : ℝ) : ℂ) :=
    funext fun x => Complex.ofReal_sub _ _
  rw [hsub, fourier_sub_apply _ _ hφint hconvvint ξ,
    fourier_ofReal_convolution φ K hφ hK hφc hKc ξ]
  ring

/-- A uniform Fourier multiplier bound controls the weaker Sobolev energy of the mollification error by the stronger Sobolev energy. -/
theorem sobolevNormSq_sub_convolution_le (φ K : Space d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (hφc : HasCompactSupport φ) (hKc : HasCompactSupport K)
    {s₀ s M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ ξ : Space d,
      ‖1 - 𝓕 (fun x => (K x : ℂ)) ξ‖ ^ 2
          * (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s₀ - s) ≤ M) :
    sobolevNormSq d s₀ (fun x => φ x - (φ ⋆[lsmul ℝ ℝ, volume] K) x)
      ≤ ENNReal.ofReal M * sobolevNormSq d s φ := by
  have hwpos : ∀ ξ : Space d, 0 < 1 + (2 * Real.pi * ‖ξ‖) ^ 2 := fun ξ => by positivity
  have hpoint : ∀ ξ : Space d,
      (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀
          * ‖𝓕 (fun x => ((φ x - (φ ⋆[lsmul ℝ ℝ, volume] K) x : ℝ) : ℂ)) ξ‖ ^ 2
        ≤ M * ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
            * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) := by
    intro ξ
    rw [fourier_sub_convolution φ K hφ hK hφc hKc ξ, norm_mul]
    have hsplit : (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀
        = (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s₀ - s)
          * (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s := by
      rw [← Real.rpow_add (hwpos ξ)]; ring_nf
    rw [hsplit]
    calc (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s₀ - s)
            * (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
            * (‖𝓕 (fun x => (φ x : ℂ)) ξ‖ * ‖1 - 𝓕 (fun x => (K x : ℂ)) ξ‖) ^ 2
        = (‖1 - 𝓕 (fun x => (K x : ℂ)) ξ‖ ^ 2
              * (1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ (s₀ - s))
            * ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
              * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) := by ring
      _ ≤ M * ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
              * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (hM ξ) (by positivity)
  unfold sobolevNormSq
  calc ∫⁻ ξ : Space d, ENNReal.ofReal
        ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s₀
          * ‖𝓕 (fun x => ((φ x - (φ ⋆[lsmul ℝ ℝ, volume] K) x : ℝ) : ℂ)) ξ‖ ^ 2)
      ≤ ∫⁻ ξ : Space d, ENNReal.ofReal
          (M * ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
            * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2)) :=
        lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal (hpoint ξ)
    _ = ENNReal.ofReal M * ∫⁻ ξ : Space d, ENNReal.ofReal
          ((1 + (2 * Real.pi * ‖ξ‖) ^ 2) ^ s
            * ‖𝓕 (fun x => (φ x : ℂ)) ξ‖ ^ 2) := by
        rw [← lintegral_const_mul' (ENNReal.ofReal M) _ ENNReal.ofReal_ne_top]
        exact lintegral_congr fun ξ => ENNReal.ofReal_mul hM0




end Critical2DKPZ.Analysis.Sobolev.Rellich

end
