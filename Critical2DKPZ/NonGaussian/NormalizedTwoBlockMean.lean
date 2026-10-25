/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.TwoBlockSlice
public import Critical2DKPZ.NonGaussian.IndependentMeasureIntegration
public import Critical2DKPZ.NonGaussian.RandomMeasureParameterMeasurability
public import Critical2DKPZ.NonGaussian.PositiveRatios
public import Critical2DKPZ.SHF.Tsai.PositiveChainBlockMeasurability
import Mathlib.Tactic

/-! # The normalized two-block mean bound -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Tsai
open scoped ENNReal

namespace Critical2DKPZ.NonGaussian

/-- When an independent final block has heat-block mean and the terminal test takes values in `[0,1]`,
the normalized two-block mass is integrable and has expectation at most one. -/
theorem integral_normalized_twoBlock_chain_le_one {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B₀ B₁ : Ω → Measure (Plane × Plane)) (hB₀ : Measurable B₀) (hB₁ : Measurable B₁)
    (hLF₀ : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (B₀ ω))
    (hLF₁ : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (B₁ ω)) (hind : IndepFun B₀ B₁ P)
    (f g : Plane → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ y, 0 ≤ f y) (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1)
    {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) (hmean : P.bind B₁ = heatBlock τ)
    (hnum : ∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane => f p.1 * g p.2)
      (chainProduct (fun k => if k = 0 then B₀ ω else B₁ ω) (fun _ => heatKernel ε) 1))
    (hden : ∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane => f p.1) (B₀ ω)) :
    Integrable (fun ω => (∫ p, f p.1 * g p.2
      ∂chainProduct (fun k => if k = 0 then B₀ ω else B₁ ω) (fun _ => heatKernel ε) 1) /
        (∫ p, f p.1 ∂B₀ ω)) P ∧
    (∫ ω, (∫ p, f p.1 * g p.2
      ∂chainProduct (fun k => if k = 0 then B₀ ω else B₁ ω) (fun _ => heatKernel ε) 1) /
        (∫ p, f p.1 ∂B₀ ω) ∂P) ≤ 1 := by
  classical
  let E : CompactExhaustion (Plane × Plane) := RandomMeasure.vagueCompactExhaustion (Plane × Plane)
  let M : Measure (Plane × Plane) → Measure (Plane × Plane) :=
    RandomMeasure.locallyFiniteMeasureModification E id
  have hM : Measurable M :=
    RandomMeasure.measurable_locallyFiniteMeasureModification E id measurable_id
  let C (k : ℕ) (a : Measure (Plane × Plane)) := if k = 0 then M a else 0
  have hC (k : ℕ) (_ : k ≤ 1) : Measurable (C k) := by
    by_cases hk : k = 0
    · simpa only [C, hk, ↓reduceIte] using hM
    · simpa only [C, hk, ↓reduceIte] using
        (measurable_const : Measurable (fun _ : Measure (Plane × Plane) => (0 : Measure (Plane × Plane))))
  have hCLF (a : Measure (Plane × Plane)) (k : ℕ) : IsLocallyFiniteMeasure (C k a) := by
    dsimp only [C]
    split_ifs
    · exact RandomMeasure.locallyFinite_locallyFiniteMeasureModification E id a
    · infer_instance
  let F (y : Plane) := ENNReal.ofReal (f y)
  let G (y : Plane) := ENNReal.ofReal (g y)
  let H (a : Measure (Plane × Plane)) (q : Plane × Plane) :=
    (∫⁻ p, F p.1 ∂C 0 a)⁻¹ * positiveChainBlockTest 1 1 (fun k => C k a)
      (fun _ => heatKernel ε) (fun p => F p.1 * G p.2) q
  have hMass : Measurable (fun a => ∫⁻ p, F p.1 ∂C 0 a) :=
    (Measure.measurable_lintegral (hf.ennreal_ofReal.comp measurable_fst)).comp (hC 0 (by omega))
  have hH : Measurable (Function.uncurry H) :=
    (hMass.inv.comp measurable_fst).mul
      (measurable_positiveChainBlockTest 1 1 C hC (fun a k _ => hCLF a k) _
        (fun _ => measurable_heatKernel ε) _
        ((hf.ennreal_ofReal.comp measurable_fst).mul (hg.ennreal_ofReal.comp measurable_snd)))
  have hAvg (a : Measure (Plane × Plane)) : (∫⁻ q, H a q ∂P.bind B₁) ≤ 1 := by
    rw [hmean]
    let : ∀ k, IsLocallyFiniteMeasure (C k a) := hCLF a
    exact lintegral_normalized_positiveChainBlockTest_two_heat_le (fun k => C k a) F G
      hf.ennreal_ofReal hg.ennreal_ofReal
      (fun y => (ENNReal.ofReal_le_ofReal (hg1 y)).trans_eq ENNReal.ofReal_one) hτ hε
  have hTotal : (∫⁻ ω, ∫⁻ q, H (B₀ ω) q ∂B₁ ω ∂P) ≤ 1 := by
    calc
      _ = ∫⁻ a, ∫⁻ q, H a q ∂P.bind B₁ ∂P.map B₀ :=
        lintegral_independent_measure_parameter P B₀ hB₀ B₁ hB₁ hLF₁ hind H hH
      _ ≤ ∫⁻ a, (1 : ℝ≥0∞) ∂P.map B₀ := lintegral_mono hAvg
      _ = ∫⁻ ω, (1 : ℝ≥0∞) ∂P := lintegral_map' measurable_const.aemeasurable hB₀.aemeasurable
      _ = 1 := by simp
  have hMeas : AEMeasurable (fun ω => ∫⁻ q, H (B₀ ω) q ∂B₁ ω) P :=
    aemeasurable_lintegral_locallyFinite_randomMeasure_parameter P B₀ hB₀ B₁ hB₁ hLF₁ H hH
  have hFinite := ae_lt_top' hMeas (ne_top_of_le_ne_top (by simp) hTotal)
  let S (ω : Ω) := (∫⁻ q, H (B₀ ω) q ∂B₁ ω).toReal
  let R (ω : Ω) := (∫ p, f p.1 * g p.2
    ∂chainProduct (fun k => if k = 0 then B₀ ω else B₁ ω) (fun _ => heatKernel ε) 1) /
      (∫ p, f p.1 ∂B₀ ω)
  have hSI : Integrable S P :=
    integrable_toReal_of_lintegral_ne_top hMeas (ne_top_of_le_ne_top (by simp) hTotal)
  have hSBound : (∫ ω, S ω ∂P) ≤ 1 := by
    rw [show (∫ ω, S ω ∂P) = (∫⁻ ω, ∫⁻ q, H (B₀ ω) q ∂B₁ ω ∂P).toReal from
      integral_toReal hMeas hFinite]
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono (by simp) hTotal
  have hSR : S =ᵐ[P] R := by
    filter_upwards [hLF₀, hLF₁, hnum, hden] with ω hω₀ hω₁ hωnum hωden
    let μ : ℕ → Measure (Plane × Plane) := fun k => if k = 0 then B₀ ω else B₁ ω
    have hμ (k : ℕ) : IsLocallyFiniteMeasure (μ k) := by
      dsimp only [μ]
      split_ifs
      · exact hω₀
      · exact hω₁
    let : ∀ k, IsLocallyFiniteMeasure (μ k) := hμ
    let : ∀ k, IsLocallyFiniteMeasure (C k (B₀ ω)) := hCLF (B₀ ω)
    have hC0 : C 0 (B₀ ω) = μ 0 :=
      RandomMeasure.locallyFiniteMeasureModification_apply_of_isLocallyFinite E id (B₀ ω) hω₀
    have hslice := positiveChainBlockTest_two_congr_first (fun k => C k (B₀ ω)) μ hC0
      (fun _ => heatKernel ε) (fun p => F p.1 * G p.2)
    calc
      S ω = ((∫⁻ p, F p.1 * G p.2 ∂chainProduct μ (fun _ => heatKernel ε) 1) /
          (∫⁻ p, F p.1 ∂μ 0)).toReal := by
        rw [normalized_twoBlock_chain_eq_slice μ F G hf.ennreal_ofReal hg.ennreal_ofReal ε]
        change (∫⁻ q, (∫⁻ p, F p.1 ∂C 0 (B₀ ω))⁻¹ *
          positiveChainBlockTest 1 1 (fun k => C k (B₀ ω)) (fun _ => heatKernel ε)
            (fun p => F p.1 * G p.2) q ∂B₁ ω).toReal = _
        rw [hslice, hC0]
        rfl
      _ = R ω := positiveTensorRatio_toReal_eq _ _ f g hf0 hg0 hωnum hωden
  refine ⟨hSI.congr hSR, ?_⟩
  exact (integral_congr_ae hSR.symm).trans_le hSBound

end Critical2DKPZ.NonGaussian

end
