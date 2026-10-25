/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.TensorCompositionFourth
public import Critical2DKPZ.SHF.Tsai.FourthMomentTransitivity
public import Critical2DKPZ.SHF.Tsai.PairingMoments

/-! # Universal two-increment composition in fourth moment

The composition axiom identifies one applicable family. Fourth-moment
comparison transfers that limit to every other applicable family. Thus two
consecutive increments merge in `L⁴` for all spatial `L²` endpoint tensors.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Critical2DKPZ.SHF.Tsai

/-- Every applicable mollifier family merges two consecutive increments in fourth moment. -/
theorem isDenseSHF_smoothedProduct_tendsto_tensor (θ : ℝ) (D : Set ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsDenseSHF θ D P Z)
    {t₀ t₁ t₂ : ℝ} (h₀ : t₀ ∈ D) (h₁ : t₁ ∈ D) (h₂ : t₂ ∈ D) (h₀₁ : t₀ < t₁) (h₁₂ : t₁ < t₂)
    (w : ℕ → Plane → ℝ) (hw : IsL2ApplicableMollifier w)
    (g g' : Plane → ℝ) (hg : MemLp g 2) (hg' : MemLp g' 2) :
    (∀ ℓ, Integrable (fun ω => ((∫ p, g p.1 * g' p.2
      ∂smoothedProductMeasure (Z t₀ t₁ ω) (w ℓ) (Z t₁ t₂ ω)) -
        ∫ p, g p.1 * g' p.2 ∂Z t₀ t₂ ω) ^ 4) P) ∧
    Tendsto (fun ℓ => ∫ ω, ((∫ p, g p.1 * g' p.2
      ∂smoothedProductMeasure (Z t₀ t₁ ω) (w ℓ) (Z t₁ t₂ ω)) -
        ∫ p, g p.1 * g' p.2 ∂Z t₀ t₂ ω) ^ 4 ∂P) atTop (𝓝 0) := by
  classical
  obtain ⟨v, hv, hvP, hvconv⟩ := hZ.2.1 t₀ h₀ t₁ h₁ t₂ h₂ h₀₁ h₁₂
  have hvlim := tendsto_integral_smoothedProduct_sub_pow_four_tensor θ D P Z hZ
    h₀ h₁ h₂ h₀₁ h₁₂ v hv hvP hvconv g g' hg hg'
  let B (k : ℕ) := if k = 0 then Z t₀ t₁ else Z t₁ t₂
  let τ (k : ℕ) := if k = 0 then t₁ - t₀ else t₂ - t₁
  have hτ (k : ℕ) (_ : k ≤ 1) : 0 < τ k := by
    dsimp only [τ]
    split_ifs <;> linarith only [h₀₁, h₁₂]
  have hB (k : ℕ) (_ : k ≤ 1) : HasDeltaBoseMoments θ (τ k) P (B k) := by
    dsimp only [B, τ]
    split_ifs
    · exact hZ.hasDeltaBoseMoments h₀ h₁ h₀₁
    · exact hZ.hasDeltaBoseMoments h₁ h₂ h₁₂
  have hind : iIndepFun (fun k : Fin (1 + 1) => B k) P :=
    hZ.iIndepFun_twoConsecutive h₀ h₁ h₂ h₀₁ h₁₂
  let X (u : ℕ → Plane → ℝ) (ℓ : ℕ) (ω : Ω) := ∫ p, g p.1 * g' p.2
    ∂smoothedProductMeasure (Z t₀ t₁ ω) (u ℓ) (Z t₁ t₂ ω)
  let Y (ω : Ω) := ∫ p, g p.1 * g' p.2 ∂Z t₀ t₂ ω
  have hmem (u : ℕ → Plane → ℝ) (hu : IsL2ApplicableMollifier u) (ℓ : ℕ) : MemLp (X u ℓ) 4 P := by
    have h := memLp_chainPairing_four 1 τ hτ B hB hind (fun _ => u) (fun _ => hu) ℓ g g' hg hg'
    simpa only [chainProduct, B, ite_eq_left (show (0 : ℕ) = 0 from rfl),
      ite_eq_right (by norm_num : (1 : ℕ) ≠ 0)] using h
  have hY : MemLp Y 4 P := isDenseSHF_memLp_pairing_four hZ h₀ h₂ (h₀₁.trans h₁₂) hg hg'
  have hcompare : Tendsto (fun ℓ => ∫ ω, (X w ℓ ω - X v ℓ ω) ^ 4 ∂P) atTop (𝓝 0) := by
    have h := tendsto_integral_chainProduct_sub_pow_four 1 τ hτ B hB hind
      (fun _ => w) (fun _ => v) (fun _ => hw) (fun _ => hv) g g' hg hg'
    simpa only [chainProduct, B, ite_eq_left (show (0 : ℕ) = 0 from rfl),
      ite_eq_right (by norm_num : (1 : ℕ) ≠ 0)] using h.2
  exact tendsto_integral_sub_pow_four_trans P (X w) (X v) Y (hmem w hw) (hmem v hv) hY
    hcompare hvlim.2

end Critical2DKPZ.SHF.Tsai

end
