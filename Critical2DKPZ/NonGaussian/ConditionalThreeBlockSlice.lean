/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.ConditionalMeasureExpectation
public import Critical2DKPZ.NonGaussian.NormalizedThreeBlockSlice
public import Critical2DKPZ.SHF.Tsai.PositiveChainBlockMeasurability
import Critical2DKPZ.SHF.Tsai.MixedBlockJointMoments
import Mathlib.Tactic

/-! # Conditional bound for the normalized middle Gaussian slice -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Tsai
open scoped ENNReal

namespace Critical2DKPZ.NonGaussian

/-- An independent middle block with heat-block mean gives an integrable normalized slice
whose conditional expectation given the outer parameter is at most `(2πτ)⁻¹` times the last mass. -/
theorem condExp_normalized_threeBlock_slice_le {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → A) (hX : Measurable X)
    (B : Ω → Measure (Plane × Plane)) (hB : Measurable B)
    (hBLF : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (B ω)) (hind : IndepFun X B P)
    (C : ℕ → A → Measure (Plane × Plane)) (hC : ∀ k ≤ 2, Measurable (C k))
    (hCLF : ∀ a, ∀ k ≤ 2, IsLocallyFiniteMeasure (C k a))
    (f g : Plane → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) (hmean : P.bind B = heatBlock τ)
    (hLast : (∫⁻ ω, ∫⁻ p, g p.2 ∂C 2 (X ω) ∂P) ≠ ∞) :
    Integrable (fun ω => (∫⁻ q, (∫⁻ p, f p.1 ∂C 0 (X ω))⁻¹ *
      positiveChainBlockTest 2 1 (fun k => C k (X ω)) (fun _ => heatKernel ε)
        (fun p => f p.1 * g p.2) q ∂B ω).toReal) P ∧
    P[fun ω => (∫⁻ q, (∫⁻ p, f p.1 ∂C 0 (X ω))⁻¹ *
      positiveChainBlockTest 2 1 (fun k => C k (X ω)) (fun _ => heatKernel ε)
        (fun p => f p.1 * g p.2) q ∂B ω).toReal |
      MeasurableSpace.comap X inferInstance] ≤ᵐ[P]
        fun ω => (2 * Real.pi * τ)⁻¹ * (∫⁻ p, g p.2 ∂C 2 (X ω)).toReal := by
  let F (a : A) : ℝ≥0∞ := ∫⁻ p, f p.1 ∂C 0 a
  let G (a : A) : ℝ≥0∞ := ∫⁻ p, g p.2 ∂C 2 a
  let H (a : A) (q : Plane × Plane) : ℝ≥0∞ := (F a)⁻¹ *
    positiveChainBlockTest 2 1 (fun k => C k a) (fun _ => heatKernel ε)
      (fun p => f p.1 * g p.2) q
  have hF : Measurable F :=
    (Measure.measurable_lintegral (hf.comp measurable_fst)).comp (hC 0 (by omega))
  have hG : Measurable G :=
    (Measure.measurable_lintegral (hg.comp measurable_snd)).comp (hC 2 (by omega))
  have hH : Measurable (Function.uncurry H) :=
    (hF.inv.comp measurable_fst).mul
      (measurable_positiveChainBlockTest 2 1 C hC hCLF _ (fun _ => measurable_heatKernel ε) _
        ((hf.comp measurable_fst).mul (hg.comp measurable_snd)))
  let κ : ℝ≥0∞ := ENNReal.ofReal ((2 * Real.pi * τ)⁻¹)
  have hAvg (a : A) : (∫⁻ q, H a q ∂P.bind B) ≤ κ * G a := by
    rw [hmean]
    let μ : ℕ → Measure (Plane × Plane) := fun k => if k ≤ 2 then C k a else 0
    have hμ (k : ℕ) : IsLocallyFiniteMeasure (μ k) := by
      dsimp only [μ]
      split_ifs with hk
      · exact hCLF a k hk
      · infer_instance
    let : ∀ k, IsLocallyFiniteMeasure (μ k) := hμ
    have hslice := lintegral_normalized_positiveChainBlockTest_three_heat_le μ f g hf hg hτ hε
    have htest : positiveChainBlockTest 2 1 μ (fun _ => heatKernel ε) (fun p => f p.1 * g p.2) =
        positiveChainBlockTest 2 1 (fun k => C k a) (fun _ => heatKernel ε) (fun p => f p.1 * g p.2) := by
      funext q
      unfold positiveChainBlockTest
      congr 1
      apply congrArg Measure.pi
      funext i
      dsimp only [μ]
      rw [ite_eq_left (by omega : ((1 : Fin 3).succAbove i : ℕ) ≤ 2)]
    simpa only [H, F, G, κ, htest, μ, show (0 : ℕ) ≤ 2 by omega, show (2 : ℕ) ≤ 2 by omega, ite_eq_left] using hslice
  let : IsLocallyFiniteMeasure (P.bind B) := hmean ▸ locallyFinite_heatBlock τ
  have hfin : (∫⁻ a, ∫⁻ q, H a q ∂P.bind B ∂P.map X) ≠ ∞ := by
    apply ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hLast)
    calc
      _ ≤ ∫⁻ a, κ * G a ∂P.map X := lintegral_mono hAvg
      _ = κ * ∫⁻ ω, G (X ω) ∂P := by
        rw [lintegral_const_mul _ hG, lintegral_map' hG.aemeasurable hX.aemeasurable]
  have hCE := condExp_independent_measure_parameter P X hX B hB hBLF hind H hH hfin
  refine ⟨hCE.1, ?_⟩
  have hfinite := ae_lt_top' (hG.comp hX).aemeasurable hLast
  filter_upwards [hCE.2.2, hfinite] with ω hω hωfin
  rw [hω]
  have hbound := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωfin.ne) (hAvg (X ω))
  simpa only [Function.comp_apply, G, ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (show 0 ≤ (2 * Real.pi * τ)⁻¹ by positivity)] using hbound

end Critical2DKPZ.NonGaussian

end
